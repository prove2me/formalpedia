-- Prove2me | solution 1 for BanditAlgorithm.trajPairGLR_eq_pooled_gaussian_glr
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T19:22:02.639277+00:00
-- url     : https://prove2.me/submissions/c2921ce0-2dae-4816-9cc3-715c5bf40cd5

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit


/-!
# The Kullback–Leibler divergence between two real Gaussians of equal variance

`D(𝒩(a, v) ‖ 𝒩(b, v)) = (a − b)² / (2v)`.

This is the quantitative input of every fixed-confidence best-arm-identification
bound over the Gaussian class: the characteristic time `c*(ν)` of L&S Eq. (33.4)
is defined through `klDiv`, while the Track-and-Stop statistic `Z_t` is written in
the closed form `½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`, and the two are related
exactly by this identity.  Mathlib computes the mean and the variance of
`gaussianReal` but not its relative entropy.

The proof is the textbook one.  Both measures have a strictly positive density
against Lebesgue measure, so `d𝒩(a,v)/d𝒩(b,v) = pdf_a / pdf_b` Lebesgue-a.e. and
hence `𝒩(a,v)`-a.e., and the log-likelihood ratio collapses to an *affine*
function of `x`:

  `llr x = ((x − b)² − (x − a)²)/(2v) = (a − b)(2x − a − b)/(2v)`.

Only the first moment of a Gaussian is therefore needed, and `∫ x d𝒩(a,v) = a`
gives `(a − b)(2a − a − b)/(2v) = (a − b)²/(2v)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {v : ℝ≥0}

theorem nnreal_coe_pos_of_ne_zero (hv : v ≠ 0) : (0 : ℝ) < (v : ℝ) := by
  have : (0 : ℝ≥0) < v := lt_of_le_of_ne bot_le (Ne.symm hv)
  exact_mod_cast this

/-! ## 1. The logarithm of the Gaussian density -/

theorem log_gaussianPDFReal (hv : v ≠ 0) (m x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = -Real.log (√(2 * π * v)) - (x - m) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hs : (0 : ℝ) < √(2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  rw [gaussianPDFReal, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

/-- The log-likelihood ratio of two Gaussians with the same variance is affine. -/
theorem log_gaussianPDFReal_sub (hv : v ≠ 0) (a b x : ℝ) :
    Real.log (gaussianPDFReal a v x) - Real.log (gaussianPDFReal b v x)
      = (a - b) * (2 * x - a - b) / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  rw [log_gaussianPDFReal hv, log_gaussianPDFReal hv]
  field_simp
  ring

/-! ## 2. The Radon–Nikodym derivative -/

theorem rnDeriv_gaussianReal_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    (gaussianReal a v).rnDeriv (gaussianReal b v)
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * gaussianPDF a v x := by
  have hb : gaussianReal b v = volume.withDensity (gaussianPDF b v) :=
    gaussianReal_of_var_ne_zero _ hv
  have h1 : (gaussianReal a v).rnDeriv (volume.withDensity (gaussianPDF b v))
      =ᵐ[volume] fun x ↦ (gaussianPDF b v x)⁻¹ * (gaussianReal a v).rnDeriv volume x := by
    refine Measure.rnDeriv_withDensity_right _ _ (measurable_gaussianPDF b v).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ (gaussianPDF_pos b hv x).ne')
      (Filter.Eventually.of_forall fun x ↦ ?_)
    simp [gaussianPDF]
  have h2 : (gaussianReal a v).rnDeriv volume =ᵐ[volume] gaussianPDF a v :=
    rnDeriv_gaussianReal a v
  rw [hb]
  filter_upwards [h1, h2] with x hx1 hx2
  rw [hx1, hx2]

/-- The log-likelihood ratio of two same-variance Gaussians, `𝒩(a,v)`-almost
everywhere. -/
theorem llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    llr (gaussianReal a v) (gaussianReal b v)
      =ᵐ[gaussianReal a v] fun x ↦ (a - b) * (2 * x - a - b) / (2 * v) := by
  have hac : gaussianReal a v ≪ volume := gaussianReal_absolutelyContinuous a hv
  have hae : ∀ᵐ x ∂(gaussianReal a v), (gaussianReal a v).rnDeriv (gaussianReal b v) x
      = (gaussianPDF b v x)⁻¹ * gaussianPDF a v x :=
    hac.ae_le (rnDeriv_gaussianReal_gaussianReal hv a b)
  filter_upwards [hae] with x hx
  have hbpos : 0 < gaussianPDFReal b v x := gaussianPDFReal_pos b v x hv
  have hapos : 0 < gaussianPDFReal a v x := gaussianPDFReal_pos a v x hv
  rw [llr, hx, ENNReal.toReal_mul, gaussianPDF, gaussianPDF,
    ← ENNReal.ofReal_inv_of_pos hbpos, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hapos.le, Real.log_mul (by positivity) hapos.ne', Real.log_inv,
    ← log_gaussianPDFReal_sub hv a b x]
  ring

/-! ## 3. Integrability and the integral -/

/-- `x ↦ x` is integrable against a Gaussian. -/
theorem integrable_id_gaussianReal (m : ℝ) (w : ℝ≥0) :
    Integrable (fun x : ℝ ↦ x) (gaussianReal m w) := by
  have h : Integrable id (gaussianReal m w) :=
    MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ := m) (v := w) 1)
  simpa [Function.id_def] using h

/-- The affine function appearing as the log-likelihood ratio. -/
theorem integrable_llr_form (hv : v ≠ 0) (a b : ℝ) :
    Integrable (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v)) (gaussianReal a v) := by
  have hid := integrable_id_gaussianReal a v
  have h1 : Integrable (fun x : ℝ ↦ 2 * x - a - b) (gaussianReal a v) :=
    (((hid.const_mul 2).sub (integrable_const a)).sub (integrable_const b))
  exact (h1.const_mul (a - b)).div_const (2 * v)

theorem integrable_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    Integrable (llr (gaussianReal a v) (gaussianReal b v)) (gaussianReal a v) :=
  (integrable_llr_form hv a b).congr (llr_gaussianReal hv a b).symm

theorem integral_llr_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    ∫ x, llr (gaussianReal a v) (gaussianReal b v) x ∂(gaussianReal a v)
      = (a - b) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) := nnreal_coe_pos_of_ne_zero hv
  have hid := integrable_id_gaussianReal a v
  rw [integral_congr_ae (llr_gaussianReal hv a b)]
  have hrw : (fun x : ℝ ↦ (a - b) * (2 * x - a - b) / (2 * v))
      = fun x : ℝ ↦ ((a - b) / (v : ℝ)) * x - (a - b) * (a + b) / (2 * v) := by
    funext x
    field_simp
    ring
  rw [hrw, integral_sub (hid.const_mul _) (integrable_const _), integral_const_mul,
    integral_id_gaussianReal]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  field_simp
  ring

/-! ## 4. The divergence -/

/-- **The Kullback–Leibler divergence between two Gaussians of equal variance.** -/
theorem klDiv_gaussianReal (hv : v ≠ 0) (a b : ℝ) :
    klDiv (gaussianReal a v) (gaussianReal b v)
      = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have hac : gaussianReal a v ≪ gaussianReal b v := by
    refine (gaussianReal_absolutelyContinuous a hv).trans ?_
    exact gaussianReal_absolutelyContinuous' b hv
  rw [klDiv_of_ac_of_integrable hac (integrable_llr_gaussianReal hv a b),
    integral_llr_gaussianReal hv a b]
  simp

/-- The unit-variance case, which is the environment class `𝓔^k_𝒩(1)` of L&S
Chapter 33. -/
theorem klDiv_gaussianReal_one (a b : ℝ) :
    klDiv (gaussianReal a 1) (gaussianReal b 1)
      = ENNReal.ofReal ((a - b) ^ 2 / 2) := by
  rw [klDiv_gaussianReal one_ne_zero a b]
  norm_num

end BanditAlgorithm



/-!
# The pooled-mean decomposition

The algebraic identity behind the closed form of the Track-and-Stop statistic
`Z_t` (L&S p. 409).  For weights `p, q ≥ 0` with `p + q > 0` and reals `u, v`,

  `p (u − m)² + q (v − m)² = (p + q)(m − m*)² + pq/(p+q) · (u − v)²`,

where `m* = (pu + qv)/(p + q)` is the pooled mean.  Consequently the left-hand
side is minimised at `m = m*`, with minimum value `pq/(p+q) · (u − v)²`.

In the Gaussian bandit this is exactly the statement that

  `inf_{m} [T_a · D(μ̂_a, m) + T_b · D(μ̂_b, m)] = ½ · T_a T_b/(T_a + T_b) · (μ̂_a − μ̂_b)²`,

since `D(x, m) = (x − m)²/2` for unit-variance Gaussians: the generalised
likelihood ratio for "arm `a` is not better than arm `b`" collapses to the closed
form used by `trajPairGLR`.
-/

namespace BanditAlgorithm

/-- **Pooled-mean decomposition.** -/
theorem weighted_sq_dist_decomp {p q u v m : ℝ} (hpq : p + q ≠ 0) :
    p * (u - m) ^ 2 + q * (v - m) ^ 2
      = (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 + p * q / (p + q) * (u - v) ^ 2 := by
  field_simp
  ring

/-- The pooled mean minimises the weighted sum of squared distances. -/
theorem pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 ≤ p * (u - m) ^ 2 + q * (v - m) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq.ne']
  have : 0 ≤ (p + q) * (m - (p * u + q * v) / (p + q)) ^ 2 :=
    mul_nonneg hpq.le (sq_nonneg _)
  linarith

/-- Equality is attained at the pooled mean. -/
theorem pq_mul_sq_sub_eq {p q u v : ℝ} (hpq : p + q ≠ 0) :
    p * (u - (p * u + q * v) / (p + q)) ^ 2 + q * (v - (p * u + q * v) / (p + q)) ^ 2
      = p * q / (p + q) * (u - v) ^ 2 := by
  rw [weighted_sq_dist_decomp hpq]
  simp

/-- The minimum over `m` of the weighted sum of squared distances is exactly the
pooled term. -/
theorem iInf_weighted_sq_dist {p q u v : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * (u - m) ^ 2 + q * (v - m) ^ 2) = p * q / (p + q) * (u - v) ^ 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * (u - m) ^ 2 + q * (v - m) ^ 2) :=
    ⟨p * q / (p + q) * (u - v) ^ 2, by
      rintro _ ⟨m, rfl⟩
      exact pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ pq_mul_sq_sub_le hp hq hpq)
  exact le_of_le_of_eq (ciInf_le hbdd ((p * u + q * v) / (p + q))) (pq_mul_sq_sub_eq hpq.ne')

/-- Half the pooled term, in the form used by `trajPairGLR`. -/
theorem half_pq_mul_sq_sub_le {p q u v m : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    p * q / (p + q) * (u - v) ^ 2 / 2
      ≤ p * ((u - m) ^ 2 / 2) + q * ((v - m) ^ 2 / 2) := by
  have h := pq_mul_sq_sub_le hp hq hpq (u := u) (v := v) (m := m)
  linarith

end BanditAlgorithm



/-!
# The Gaussian bandit class `𝓔^k_𝒩(1)`, explicitly

Everything the fixed-confidence analysis needs about `gaussianBandit μ`, made
computable:

* `banditArmMean_gaussianBandit` — the arm means are the parameters;
* `banditOptimalMean_gaussianBandit`, `banditOptimalArms_gaussianBandit` — the
  optimal value and the optimal-arm set are the maximum and the argmax of `μ`;
* `klDiv_gaussianBandit` — `D(ν_i ‖ ν'_i) = (μ_i − μ'_i)²/2`;
* `baiAlternatives_gaussianBandit` — membership in `𝓔_alt(ν)` is a condition on
  the parameter vectors only;
* `baiComplexity_inner_gaussianBandit` — the inner sum defining `c*(ν)⁻¹` is
  `∑_i α_i (μ_i − μ'_i)²/2`.

The last three are what turn the abstract characteristic time of L&S Eq. (33.4)
into the quantity Track-and-Stop actually tracks, and `pooled_pair_glr` is the
bridge to the closed form `trajPairGLR` used by `trajGLR`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Means, optimal value, optimal arms -/

@[simp]
theorem banditArmMean_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditArmMean (gaussianBandit μvec) i = μvec i := by
  simp [banditArmMean, gaussianBandit, integral_id_gaussianReal]

@[simp]
theorem banditOptimalMean_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalMean (gaussianBandit μvec) = ⨆ i, μvec i := by
  simp [banditOptimalMean]

@[simp]
theorem banditGap_gaussianBandit (μvec : Fin k → ℝ) (i : Fin k) :
    banditGap (gaussianBandit μvec) i = (⨆ j, μvec j) - μvec i := by
  simp [banditGap]

theorem banditOptimalArms_gaussianBandit (μvec : Fin k → ℝ) :
    banditOptimalArms (gaussianBandit μvec) = {i | μvec i = ⨆ j, μvec j} := by
  ext i
  simp [banditOptimalArms]

/-- With finitely many arms and at least one, the optimal mean is attained. -/
theorem exists_mem_banditOptimalArms [NeZero k] (μvec : Fin k → ℝ) :
    ∃ i, i ∈ banditOptimalArms (gaussianBandit μvec) := by
  classical
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k)) μvec
    Finset.univ_nonempty
  refine ⟨i, ?_⟩
  rw [banditOptimalArms_gaussianBandit]
  refine le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) ?_
  exact ciSup_le fun j ↦ hi j (Finset.mem_univ j)

/-- An arm is optimal exactly when it maximises the parameter vector. -/
theorem mem_banditOptimalArms_gaussianBandit_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    i ∈ banditOptimalArms (gaussianBandit μvec) ↔ ∀ j, μvec j ≤ μvec i := by
  rw [banditOptimalArms_gaussianBandit]
  constructor
  · intro hi j
    rw [Set.mem_setOf_eq] at hi
    exact hi ▸ le_ciSup (f := μvec) (Finite.bddAbove_range _) j
  · intro hi
    exact le_antisymm (le_ciSup (f := μvec) (Finite.bddAbove_range _) i) (ciSup_le hi)

/-- The gap is positive exactly when the arm is not optimal. -/
theorem banditGap_pos_iff [NeZero k] (μvec : Fin k → ℝ) (i : Fin k) :
    0 < banditGap (gaussianBandit μvec) i ↔ ∃ j, μvec i < μvec j := by
  rw [banditGap_gaussianBandit, sub_pos]
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    exact absurd (ciSup_le hcon) (not_le.mpr h)
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le hj (le_ciSup (f := μvec) (Finite.bddAbove_range _) j)

/-! ## 2. Divergences -/

@[simp]
theorem klDiv_gaussianBandit (a b : Fin k → ℝ) (i : Fin k) :
    klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i)
      = ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simpa [gaussianBandit] using klDiv_gaussianReal_one (a i) (b i)

/-- The inner sum in the definition of the characteristic time, for Gaussians. -/
theorem baiComplexity_inner_gaussianBandit (a b : Fin k → ℝ) (α : Fin k → ℝ≥0) :
    (∑ i, (α i : ℝ≥0∞) * klDiv ((gaussianBandit a).P i) ((gaussianBandit b).P i))
      = ∑ i, (α i : ℝ≥0∞) * ENNReal.ofReal ((a i - b i) ^ 2 / 2) := by
  simp

/-- The alternative set of a Gaussian bandit inside the Gaussian class, in terms
of the parameter vectors. -/
theorem mem_baiAlternatives_gaussianBandit_iff (a : Fin k → ℝ)
    (ν' : StochasticBandit k) :
    ν' ∈ baiAlternatives (Set.range (gaussianBandit (k := k))) (gaussianBandit a) ↔
      ∃ b : Fin k → ℝ, ν' = gaussianBandit b ∧
        Disjoint (banditOptimalArms (gaussianBandit b))
          (banditOptimalArms (gaussianBandit a)) := by
  constructor
  · rintro ⟨⟨b, rfl⟩, hdisj⟩
    exact ⟨b, rfl, hdisj⟩
  · rintro ⟨b, rfl, hdisj⟩
    exact ⟨⟨b, rfl⟩, hdisj⟩

/-! ## 3. The bridge to the closed-form pair statistic -/

/-- **The Gaussian generalised likelihood ratio for a pair of arms.**  For weights
`p, q ≥ 0` (the pull counts) the least total divergence achievable by moving both
empirical means to a common value `m` is exactly the closed form used by
`trajPairGLR`. -/
theorem pooled_pair_glr {p q u w : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q) :
    ⨅ m : ℝ, (p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2))
      = p * q / (p + q) * (u - w) ^ 2 / 2 := by
  have hbdd : BddBelow (Set.range fun m : ℝ ↦ p * ((u - m) ^ 2 / 2) + q * ((w - m) ^ 2 / 2)) :=
    ⟨p * q / (p + q) * (u - w) ^ 2 / 2, by
      rintro _ ⟨m, rfl⟩
      exact half_pq_mul_sq_sub_le hp hq hpq⟩
  refine le_antisymm ?_ (le_ciInf fun m ↦ half_pq_mul_sq_sub_le hp hq hpq)
  refine le_of_le_of_eq (ciInf_le hbdd ((p * u + q * w) / (p + q))) ?_
  have h := pq_mul_sq_sub_eq (p := p) (q := q) (u := u) (v := w) hpq.ne'
  linarith

/-- The pair statistic of `Def_TrackAndStop` is the Gaussian GLR of the pair. -/
theorem trajPairGLR_eq_iInf (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : 0 < (trajPullCount a t ω : ℝ) + (trajPullCount b t ω : ℝ)) :
    trajPairGLR a b t ω
      = ⨅ m : ℝ, ((trajPullCount a t ω : ℝ) * ((trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (trajPullCount b t ω : ℝ) * ((trajEmpiricalMean b t ω - m) ^ 2 / 2)) := by
  rw [pooled_pair_glr (Nat.cast_nonneg _) (Nat.cast_nonneg _) h]
  rfl

end BanditAlgorithm


theorem _root_.solution {k : ℕ} (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : 0 < (BanditAlgorithm.trajPullCount a t ω : ℝ)
      + (BanditAlgorithm.trajPullCount b t ω : ℝ)) :
    BanditAlgorithm.trajPairGLR a b t ω
      = ⨅ m : ℝ, ((BanditAlgorithm.trajPullCount a t ω : ℝ)
            * ((BanditAlgorithm.trajEmpiricalMean a t ω - m) ^ 2 / 2)
          + (BanditAlgorithm.trajPullCount b t ω : ℝ)
            * ((BanditAlgorithm.trajEmpiricalMean b t ω - m) ^ 2 / 2)) :=
  BanditAlgorithm.trajPairGLR_eq_iInf a b t ω h
