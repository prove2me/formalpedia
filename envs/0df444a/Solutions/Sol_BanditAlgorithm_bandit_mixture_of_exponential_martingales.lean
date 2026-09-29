-- Prove2me | solution 1 for BanditAlgorithm.bandit_mixture_of_exponential_martingales
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T21:33:26.603724+00:00
-- url     : https://prove2.me/submissions/bba52047-a680-4d09-b759-87169c954f76

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_TrackAndStop

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
# The one-step exponential (martingale) identity for the bandit trajectory

This is the foundational brick that the three remaining leaves of Theorem 33.6 all
need: it is the *only* place where the conditional law of a reward given the past
enters, and once it is available the rest of the concentration argument is
martingale bookkeeping.

For a unit-variance Gaussian bandit, an arbitrary sampling rule, an arbitrary
`𝓕_n`-measurable weight `F`, an arm `a` and a parameter `λ`:

  `E[ F(prefix_n) · exp(λ(X_{n+1} − μ_a) − λ²/2)^{1{A_{n+1} = a}} ] = E[ F(prefix_n) ]`.

In other words `exp(λ(S_a(n) − T_a(n)μ_a) − λ²T_a(n)/2)` is a martingale, which is
the starting point of every self-normalised deviation bound (and hence of
`chernoff_pairwise_selfnormalised_deviation_bound`, of Garivier–Kaufmann's
Proposition 13, and — through the strong law it yields — of the D-Tracking
convergence statement).

The proof is exactly the decomposition the model was built for:

* `banditTrajMeasure_joint_eq_compProd` (already Proved) turns the expectation of a
  function of `(prefix_n, round_{n+1})` into an integral against
  `P_n ⊗ₘ banditStepKernel`;
* `banditStepKernel = (π.select n) ⊗ₖ (banditRewardKernel ∘ snd)` splits that into
  "choose the arm, then draw the reward";
* the inner reward integral is `1` for every arm — trivially if the arm is not `a`,
  and by the Gaussian moment generating function `∫ e^{λx} d𝒩(μ,1) = e^{λμ+λ²/2}`
  if it is.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The tilt factor `exp(λ(x − μ) − λ²/2)` integrates to `1` against `𝒩(μ, 1)`. -/
theorem lintegral_expTilt_gaussianReal (m lam : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (x - m) - lam ^ 2 / 2))
        ∂(gaussianReal m 1) = 1 := by
  have hint : Integrable (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
      (gaussianReal m 1) := by
    have h := integrable_exp_mul_gaussianReal (μ := m) (v := 1) lam
    have hrw : (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
        = fun x : ℝ ↦ Real.exp (-(lam * m) - lam ^ 2 / 2) * Real.exp (lam * x) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [hrw]
    exact h.const_mul _
  have hval : ∫ x, Real.exp (lam * (x - m) - lam ^ 2 / 2) ∂(gaussianReal m 1) = 1 := by
    have hrw : (fun x : ℝ ↦ Real.exp (lam * (x - m) - lam ^ 2 / 2))
        = fun x : ℝ ↦ Real.exp (-(lam * m) - lam ^ 2 / 2) * Real.exp (lam * x) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [hrw, integral_const_mul]
    have hmgf : ∫ x, Real.exp (lam * x) ∂(gaussianReal m 1)
        = Real.exp (m * lam + (1 : ℝ≥0) * lam ^ 2 / 2) := by
      have := mgf_fun_id_gaussianReal (μ := m) (v := 1)
      have h2 := congrFun this lam
      rw [mgf] at h2
      simpa using h2
    rw [hmgf, ← Real.exp_add]
    rw [show -(lam * m) - lam ^ 2 / 2 + (m * lam + ((1 : ℝ≥0) : ℝ) * lam ^ 2 / 2) = 0 by
      push_cast; ring]
    exact Real.exp_zero
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x ↦ (Real.exp_pos _).le), hval,
    ENNReal.ofReal_one]

/-- The tilt factor, as a function of a whole round. -/
noncomputable def expTilt (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (y : Fin k × ℝ) : ℝ≥0∞ :=
  if y.1 = a then ENNReal.ofReal (Real.exp (lam * (y.2 - μvec a) - lam ^ 2 / 2)) else 1

theorem measurable_expTilt (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) :
    Measurable (expTilt μvec a lam) := by
  classical
  unfold expTilt
  refine Measurable.ite (measurable_fst (measurableSet_singleton a)) ?_ measurable_const
  have h1 : Measurable fun y : Fin k × ℝ ↦ lam * (y.2 - μvec a) - lam ^ 2 / 2 :=
    ((measurable_snd.sub_const (μvec a)).const_mul lam).sub_const (lam ^ 2 / 2)
  exact ENNReal.measurable_ofReal.comp h1.exp

/-- The tilt integrates to `1` against the reward distribution of any arm. -/
theorem lintegral_expTilt_arm (μvec : Fin k → ℝ) (a b : Fin k) (lam : ℝ) :
    ∫⁻ x, expTilt μvec a lam (b, x) ∂(gaussianReal (μvec b) 1) = 1 := by
  classical
  by_cases hb : b = a
  · subst hb
    have hfun : (fun x : ℝ ↦ expTilt μvec b lam (b, x))
        = fun x : ℝ ↦ ENNReal.ofReal (Real.exp (lam * (x - μvec b) - lam ^ 2 / 2)) := by
      funext x; simp [expTilt]
    rw [hfun, lintegral_expTilt_gaussianReal]
  · have hfun : (fun x : ℝ ↦ expTilt μvec a lam (b, x)) = fun _ : ℝ ↦ (1 : ℝ≥0∞) := by
      funext x; simp [expTilt, hb]
    rw [hfun, lintegral_one, measure_univ]

/-- The tilt integrates to `1` against one round of the Gaussian bandit. -/
theorem lintegral_expTilt_stepKernel (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (h : BanditHistory k n) :
    ∫⁻ y, expTilt μvec a lam y ∂(banditStepKernel (gaussianBandit μvec) pol n h) = 1 := by
  classical
  rw [banditStepKernel, Kernel.lintegral_compProd _ _ _ (measurable_expTilt μvec a lam)]
  have hrk : ∀ b : Fin k,
      banditRewardKernel (gaussianBandit μvec) b = gaussianReal (μvec b) 1 := fun _ ↦ rfl
  simp only [Kernel.comap_apply, hrk]
  refine Eq.trans (lintegral_congr (g := fun _ : Fin k ↦ (1 : ℝ≥0∞)) fun b ↦ ?_) ?_
  · exact lintegral_expTilt_arm μvec a b lam
  · rw [lintegral_one, measure_univ]

/-- **The one-step exponential identity.** -/
theorem lintegral_mul_expTilt (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (F : BanditHistory k n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (banditTrajPrefix k n ω) * expTilt μvec a lam (ω n)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol)
      = ∫⁻ ω, F (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) := by
  classical
  set ν : StochasticBandit k := gaussianBandit μvec with hν
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure ν pol with hP
  set G : BanditHistory k n × (Fin k × ℝ) → ℝ≥0∞ := fun p ↦ F p.1 * expTilt μvec a lam p.2
    with hG
  have hGmeas : Measurable G :=
    (hF.comp measurable_fst).mul ((measurable_expTilt μvec a lam).comp measurable_snd)
  have hmap : Measurable (fun ω : ℕ → Fin k × ℝ ↦ (banditTrajPrefix k n ω, ω n)) :=
    measurable_banditTrajPrefix.prodMk (measurable_pi_apply n)
  -- rewrite the left side as an integral against the joint law
  have hL : ∫⁻ ω, F (banditTrajPrefix k n ω) * expTilt μvec a lam (ω n) ∂P
      = ∫⁻ p, G p ∂(P.map (fun ω ↦ (banditTrajPrefix k n ω, ω n))) := by
    rw [lintegral_map hGmeas hmap]
  rw [hL, banditTrajMeasure_joint_eq_compProd ν pol n,
    Measure.lintegral_compProd hGmeas]
  have hinner : ∀ h : BanditHistory k n,
      ∫⁻ y, G (h, y) ∂(banditStepKernel ν pol n h) = F h := by
    intro h
    have : (fun y ↦ G (h, y)) = fun y ↦ F h * expTilt μvec a lam y := rfl
    rw [this, lintegral_const_mul _ (measurable_expTilt μvec a lam),
      lintegral_expTilt_stepKernel μvec pol n a lam h, mul_one]
  simp only [hinner]
  -- and the right side is the same integral against the prefix law
  rw [lintegral_map hF measurable_banditTrajPrefix]

/-- The one-step identity with the tilt written out, for use as a standalone
statement. -/
theorem lintegral_mul_expTilt' (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (a : Fin k) (lam : ℝ) (F : BanditHistory k n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol)
      = ∫⁻ ω, F (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) :=
  lintegral_mul_expTilt μvec pol n a lam F hF

end BanditAlgorithm

/-!
# Elementary algebra of the trajectory statistics

Pull counts, empirical means and empirical allocations, and the identities that
every part of the Track-and-Stop analysis uses:

* `trajPullCount_succ` — the one-round recursion `T_i(t+1) = T_i(t) + 1{A_{t+1} = i}`;
* `sum_trajPullCount` — `∑_i T_i(t) = t`;
* `trajPullCount_le` — `T_i(t) ≤ t`, and monotonicity in `t`;
* `sum_trajAllocation` — the empirical allocation lies in the simplex for `t > 0`;
* `trajEmpiricalMean_eq_zero_of_pullCount_eq_zero` — the junk value convention;
* `trajRewardSum_eq` — `∑ rewards = T_i(t) · μ̂_i(t)` when `T_i(t) > 0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-- The sum of the rewards collected from arm `i` in the first `t` rounds. -/
noncomputable def trajRewardSum (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ :=
  ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2

theorem trajEmpiricalMean_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajEmpiricalMean i t ω = trajRewardSum i t ω / (trajPullCount i t ω : ℝ) := rfl

/-! ## Pull counts -/

@[simp]
theorem trajPullCount_zero (i : Fin k) (ω : ℕ → Fin k × ℝ) : trajPullCount i 0 ω = 0 := by
  simp [trajPullCount]

theorem trajPullCount_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i (t + 1) ω =
      trajPullCount i t ω + if (ω t).1 = i then 1 else 0 := by
  classical
  simp only [trajPullCount, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.card_insert_of_notMem (by simp), if_pos h]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajRewardSum_succ (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajRewardSum i (t + 1) ω =
      trajRewardSum i t ω + if (ω t).1 = i then (ω t).2 else 0 := by
  classical
  simp only [trajRewardSum, Finset.range_add_one, Finset.filter_insert]
  by_cases h : (ω t).1 = i
  · rw [if_pos h, Finset.sum_insert (by simp), if_pos h, add_comm]
  · rw [if_neg h, if_neg h, add_zero]

theorem trajPullCount_mono (i : Fin k) {s t : ℕ} (h : s ≤ t) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i s ω ≤ trajPullCount i t ω := by
  classical
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  exact fun x hx ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

theorem trajPullCount_le (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount i t ω ≤ t := by
  classical
  calc trajPullCount i t ω ≤ (Finset.range t).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = t := Finset.card_range t

/-- The pull counts of the `k` arms partition the rounds: `∑_i T_i(t) = t`. -/
theorem sum_trajPullCount (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajPullCount i t ω = t := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      simp only [trajPullCount_succ, Finset.sum_add_distrib, ih]
      congr 1
      simp

/-- Some arm is played at least `t / k` times. -/
theorem exists_trajPullCount_ge (hk : 0 < k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    ∃ i : Fin k, t ≤ k * trajPullCount i t ω := by
  classical
  haveI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i ↦ trajPullCount i t ω) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  calc t = ∑ j : Fin k, trajPullCount j t ω := (sum_trajPullCount t ω).symm
    _ ≤ ∑ _j : Fin k, trajPullCount i t ω :=
        Finset.sum_le_sum fun j _ ↦ hi j (Finset.mem_univ j)
    _ = k * trajPullCount i t ω := by simp [mul_comm]

/-! ## Empirical allocations -/

@[simp]
theorem trajAllocation_eq (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω = (trajPullCount i t ω : ℝ) / (t : ℝ) := rfl

theorem trajAllocation_nonneg (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajAllocation i t ω :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem trajAllocation_le_one (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajAllocation i t ω ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [trajAllocation]
  · rw [trajAllocation_eq, div_le_one (by exact_mod_cast ht)]
    exact_mod_cast trajPullCount_le i t ω

/-- For `t > 0` the empirical allocation lies in the probability simplex. -/
theorem sum_trajAllocation {t : ℕ} (ht : 0 < t) (ω : ℕ → Fin k × ℝ) :
    ∑ i : Fin k, trajAllocation i t ω = 1 := by
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ht.ne'
  simp only [trajAllocation_eq, ← Finset.sum_div]
  rw [← Nat.cast_sum, sum_trajPullCount t ω]
  exact div_self htR

/-! ## Empirical means -/

theorem trajEmpiricalMean_of_pullCount_eq_zero {i : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajPullCount i t ω = 0) : trajEmpiricalMean i t ω = 0 := by
  simp [trajEmpiricalMean, h]

theorem trajRewardSum_eq_mul (i : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajPullCount i t ω ≠ 0) :
    trajRewardSum i t ω = (trajPullCount i t ω : ℝ) * trajEmpiricalMean i t ω := by
  have hne : ((trajPullCount i t ω : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h
  rw [trajEmpiricalMean_eq, mul_div_cancel₀ _ hne]

/-! ## The pairwise GLR statistic -/

theorem trajPairGLR_comm (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a b t ω = trajPairGLR b a t ω := by
  simp only [trajPairGLR]
  rw [mul_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    add_comm ((trajPullCount a t ω : ℕ) : ℝ) ((trajPullCount b t ω : ℕ) : ℝ),
    ← neg_sub (trajEmpiricalMean a t ω) (trajEmpiricalMean b t ω), neg_pow]
  ring

theorem trajPairGLR_nonneg (a b : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 ≤ trajPairGLR a b t ω := by
  refine div_nonneg (mul_nonneg (div_nonneg (mul_nonneg ?_ ?_) ?_) (sq_nonneg _)) (by norm_num)
  · exact Nat.cast_nonneg _
  · exact Nat.cast_nonneg _
  · positivity

theorem trajPairGLR_self (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPairGLR a a t ω = 0 := by
  simp [trajPairGLR]

end BanditAlgorithm

/-!
# The exponential martingale of a Gaussian bandit has expectation one

Iterating the one-step identity of `OneStepMGF` gives, for every arm `a`, every
`λ` and every round `n`,

  `E[ exp( λ (S_a(n) − T_a(n) μ_a) − λ² T_a(n) / 2 ) ] = 1`,

where `S_a(n)` is the sum of the rewards collected from arm `a` in the first `n`
rounds and `T_a(n)` is the number of times it was played.  Markov's inequality
then turns this into the fixed-round Chernoff bound that the self-normalised
deviation estimate is built from.

The induction step is exactly the one-step identity: the weight at round `n+1`
factorises as (weight at round `n`, a function of the prefix) times the tilt of
round `n+1`, because `S_a` and `T_a` both increase by the round's contribution
only when arm `a` is played.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. History-level pull counts and reward sums -/

/-- The number of times arm `a` was played, as a function of the history. -/
def histPullCount (a : Fin k) {n : ℕ} (hst : BanditHistory k n) : ℕ :=
  ∑ t : Fin n, if (hst t).1 = a then 1 else 0

/-- The sum of the rewards collected from arm `a`, as a function of the history. -/
noncomputable def histRewardSum (a : Fin k) {n : ℕ} (hst : BanditHistory k n) : ℝ :=
  ∑ t : Fin n, if (hst t).1 = a then (hst t).2 else 0

theorem histPullCount_prefix (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    histPullCount a (banditTrajPrefix k n ω) = trajPullCount a n ω := by
  classical
  rw [histPullCount, trajPullCount, Finset.card_filter]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ if (ω s).1 = a then 1 else 0) n

theorem histRewardSum_prefix (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    histRewardSum a (banditTrajPrefix k n ω) = trajRewardSum a n ω := by
  classical
  rw [histRewardSum, trajRewardSum, Finset.sum_filter]
  exact Fin.sum_univ_eq_sum_range (fun s ↦ if (ω s).1 = a then (ω s).2 else 0) n

theorem measurable_histPullCount (a : Fin k) (n : ℕ) :
    Measurable (histPullCount (k := k) a (n := n)) := by
  classical
  refine Finset.measurable_sum _ fun t _ ↦ ?_
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply t))
    (measurableSet_singleton a)) measurable_const measurable_const

theorem measurable_histRewardSum (a : Fin k) (n : ℕ) :
    Measurable (histRewardSum (k := k) a (n := n)) := by
  classical
  refine Finset.measurable_sum _ fun t _ ↦ ?_
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply t))
    (measurableSet_singleton a)) (measurable_snd.comp (measurable_pi_apply t)) measurable_const

/-! ## 2. The weight -/

/-- The exponential weight `exp(λ(S_a − T_a μ_a) − λ² T_a/2)` on histories. -/
noncomputable def expWeight (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) {n : ℕ}
    (hst : BanditHistory k n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lam * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a)
    - lam ^ 2 * (histPullCount a hst : ℝ) / 2))

theorem measurable_expWeight (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ) :
    Measurable (expWeight (k := k) μvec a lam (n := n)) := by
  unfold expWeight
  refine ENNReal.measurable_ofReal.comp (Measurable.exp ?_)
  have h1 : Measurable fun hst : BanditHistory k n ↦ (histPullCount a hst : ℝ) :=
    measurable_from_top.comp (measurable_histPullCount a n)
  exact (((measurable_histRewardSum a n).sub (h1.mul measurable_const)).const_mul lam).sub
    ((h1.const_mul (lam ^ 2)).div_const 2)

/-- The one-round recursion of the weight. -/
theorem expWeight_succ (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expWeight μvec a lam (banditTrajPrefix k (n + 1) ω)
      = expWeight μvec a lam (banditTrajPrefix k n ω) *
        (if (ω n).1 = a then
          ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1) := by
  classical
  unfold expWeight
  rw [histPullCount_prefix, histPullCount_prefix, histRewardSum_prefix, histRewardSum_prefix,
    trajPullCount_succ, trajRewardSum_succ]
  by_cases h : (ω n).1 = a
  · rw [if_pos h, if_pos h, if_pos h, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    push_cast
    ring
  · rw [if_neg h, if_neg h, if_neg h, mul_one]
    congr 2
    push_cast
    ring

/-! ## 3. Expectation one -/

/-- **The exponential martingale has expectation one.** -/
theorem lintegral_expWeight (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) :
    ∫⁻ ω, expWeight μvec a lam (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) = 1 := by
  induction n with
  | zero =>
      have h0 : ∀ ω : ℕ → Fin k × ℝ,
          expWeight μvec a lam (banditTrajPrefix k 0 ω) = 1 := by
        intro ω
        unfold expWeight histPullCount histRewardSum
        simp
      simp only [h0]
      rw [lintegral_one, measure_univ]
  | succ n ih =>
      have hrw : ∀ ω : ℕ → Fin k × ℝ,
          expWeight μvec a lam (banditTrajPrefix k (n + 1) ω)
            = expWeight μvec a lam (banditTrajPrefix k n ω) *
              (if (ω n).1 = a then
                ENNReal.ofReal (Real.exp (lam * ((ω n).2 - μvec a) - lam ^ 2 / 2)) else 1) :=
        expWeight_succ μvec a lam n
      simp only [hrw]
      rw [lintegral_mul_expTilt' μvec pol n a lam (expWeight μvec a lam)
        (measurable_expWeight μvec a lam n)]
      exact ih

end BanditAlgorithm

/-!
# Restricting a history to an earlier round

`banditTrajPrefix k n ω` is the length-`n` prefix of a trajectory.  For `j ≤ n`
the length-`j` prefix factors through it,

  `banditTrajPrefix k j = histRestrict h ∘ banditTrajPrefix k n`,

by the plain re-indexing `Fin j ↪ Fin n`.  This is definitionally true, but
having it as a named lemma with the measurability of `histRestrict` alongside is
what lets one speak of an event of the form "nothing has happened up to round
`n`" as a *single* measurable function of the length-`n` history — which is
exactly what the optional-stopping argument of `Solutions/VilleEngine.lean`
needs.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- Restrict a length-`n` history to its first `j` rounds. -/
def histRestrict {j n : ℕ} (hjn : j ≤ n) (hst : BanditHistory k n) : BanditHistory k j :=
  fun t ↦ hst (Fin.castLE hjn t)

@[simp]
theorem histRestrict_prefix {j n : ℕ} (hjn : j ≤ n) (ω : ℕ → Fin k × ℝ) :
    histRestrict (k := k) hjn (banditTrajPrefix k n ω) = banditTrajPrefix k j ω := rfl

@[simp]
theorem histRestrict_self {n : ℕ} (hst : BanditHistory k n) :
    histRestrict (k := k) (le_refl n) hst = hst := by
  funext t
  simp [histRestrict, Fin.castLE]

theorem measurable_histRestrict {j n : ℕ} (hjn : j ≤ n) :
    Measurable (histRestrict (k := k) hjn) :=
  measurable_pi_lambda _ fun t ↦ measurable_pi_apply _

theorem histRestrict_trans {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n)
    (hst : BanditHistory k n) :
    histRestrict (k := k) hij (histRestrict hjn hst)
      = histRestrict (le_trans hij hjn) hst := rfl

/-! ## Pull counts and reward sums are stable under restriction

The count of arm `a` in the first `j` rounds of a history equals its count in the
first `j` rounds of any longer history extending it.  Stated through
`histRestrict` these are `rfl`-level facts once the prefix is unfolded, but they
are needed in the rewritten form below. -/

theorem histPullCount_restrict {j n : ℕ} (hjn : j ≤ n) (a : Fin k)
    (hst : BanditHistory k n) :
    histPullCount a (histRestrict (k := k) hjn hst)
      = ∑ t : Fin j, if (hst (Fin.castLE hjn t)).1 = a then 1 else 0 := rfl

theorem histRewardSum_restrict {j n : ℕ} (hjn : j ≤ n) (a : Fin k)
    (hst : BanditHistory k n) :
    histRewardSum a (histRestrict (k := k) hjn hst)
      = ∑ t : Fin j, if (hst (Fin.castLE hjn t)).1 = a then (hst (Fin.castLE hjn t)).2 else 0 :=
  rfl

end BanditAlgorithm

/-!
# Ville's maximal inequality for bandit exponential weights

A fixed-round Chernoff bound controls `P(W_n ≥ c)` for each `n` separately, and
turning it into a bound on `P(∃ n, W_n ≥ c)` by a union bound costs a factor that
grows with the horizon.  Ville's inequality removes that cost entirely: for a
nonnegative martingale `W` with `E[W_0] = 1`,

  `P(∃ n, W_n ≥ c) ≤ 1/c`,

with no dependence on the horizon at all.  This is what makes the *time-uniform*
threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7
achievable — a union over rounds would force a threshold linear in `t`.

## The martingale hypothesis, in integrated form

The canonical bandit model does not come with a ready-made filtered probability
space, so rather than asking for `E[W_{n+1} | 𝓕_n] = W_n` we ask for the
integrated form that the one-step tilt identity directly supplies:

  `∫ F(prefix_n ω) · W_{n+1}(prefix_{n+1} ω) dP = ∫ F(prefix_n ω) · W_n(prefix_n ω) dP`

for every measurable `F ≥ 0` on length-`n` histories (`IsTrajWeight.step`).  This
is *equivalent* to the martingale property here and is what
`lintegral_mul_expTiltVec` proves, so no conditional expectations are needed
anywhere in the development.

## The proof

The usual optional-stopping argument, arranged so that only the one-step
identity is ever used.  Write `A_N` for the event "no crossing up to round `N`"
and `E_N` for its complement.  The induction hypothesis is

  `∫_{A_N} W_N dP + c · P(E_N) ≤ 1`,

and the step splits `A_N` into `A_{N+1}` and `A_N ∩ {W_{N+1} ≥ c}`, bounds `c` by
`W_{N+1}` on the second piece, recombines the two integrals into `∫_{A_N} W_{N+1}`,
and finally replaces it by `∫_{A_N} W_N` — which is legitimate precisely because
`A_N` is a function of the length-`N` history.  Letting `N → ∞` along the
increasing events `E_N` gives the result.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- A nonnegative process on histories which is a martingale for the trajectory
measure `P`, expressed through the integrated one-step identity. -/
structure IsTrajWeight (P : Measure (ℕ → Fin k × ℝ))
    (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) : Prop where
  /-- Each `W n` is measurable on length-`n` histories. -/
  meas : ∀ n, Measurable (W n)
  /-- The weight starts with unit mass. -/
  init : ∫⁻ ω, W 0 (banditTrajPrefix k 0 ω) ∂P = 1
  /-- The martingale property, integrated against an arbitrary `𝓕_n`-measurable
  nonnegative test function. -/
  step : ∀ (n : ℕ) (F : BanditHistory k n → ℝ≥0∞), Measurable F →
    ∫⁻ ω, F (banditTrajPrefix k n ω) * W (n + 1) (banditTrajPrefix k (n + 1) ω) ∂P
      = ∫⁻ ω, F (banditTrajPrefix k n ω) * W n (banditTrajPrefix k n ω) ∂P

namespace IsTrajWeight

variable {P : Measure (ℕ → Fin k × ℝ)} {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞}

/-- The total mass is preserved: `E[W_n] = 1` for every `n`. -/
theorem lintegral_eq_one (hW : IsTrajWeight P W) (n : ℕ) :
    ∫⁻ ω, W n (banditTrajPrefix k n ω) ∂P = 1 := by
  induction n with
  | zero => exact hW.init
  | succ n ih =>
      have h := hW.step n (fun _ ↦ 1) measurable_const
      simp only [one_mul] at h
      exact h.trans ih

end IsTrajWeight

/-! ## The "no crossing yet" event -/

/-- `Survives c W n hst`: the weight has stayed strictly below `c` at every round
up to and including `n`.  Phrased as a predicate on the length-`n` history, which
is what makes it usable as the test function `F` of `IsTrajWeight.step`. -/
def Survives (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) (n : ℕ)
    (hst : BanditHistory k n) : Prop :=
  ∀ i : Fin (n + 1), W i.val (histRestrict (Nat.lt_succ_iff.mp i.isLt) hst) < c

open Classical in
/-- The indicator of `Survives`. -/
noncomputable def survIndicator (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (n : ℕ) (hst : BanditHistory k n) : ℝ≥0∞ :=
  if Survives c W n hst then 1 else 0

theorem measurableSet_survives (c : ℝ≥0∞) {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞}
    (hWm : ∀ n, Measurable (W n)) (n : ℕ) :
    MeasurableSet {hst : BanditHistory k n | Survives c W n hst} := by
  have hset : {hst : BanditHistory k n | Survives c W n hst}
      = ⋂ i : Fin (n + 1),
        {hst : BanditHistory k n |
          W i.val (histRestrict (Nat.lt_succ_iff.mp i.isLt) hst) < c} := by
    ext hst; simp [Survives]
  rw [hset]
  refine MeasurableSet.iInter fun i ↦ ?_
  exact ((hWm i.val).comp (measurable_histRestrict _)) measurableSet_Iio

theorem measurable_survIndicator (c : ℝ≥0∞) {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞}
    (hWm : ∀ n, Measurable (W n)) (n : ℕ) :
    Measurable (survIndicator (k := k) c W n) := by
  classical
  unfold survIndicator
  exact Measurable.ite (measurableSet_survives c hWm n) measurable_const measurable_const

/-- On a trajectory, `Survives` says exactly that no round up to `n` has crossed. -/
theorem survives_prefix_iff (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    Survives c W n (banditTrajPrefix k n ω)
      ↔ ∀ i ≤ n, W i (banditTrajPrefix k i ω) < c := by
  constructor
  · intro h i hi
    have := h ⟨i, Nat.lt_succ_of_le hi⟩
    simpa using this
  · intro h i
    have := h i.val (Nat.lt_succ_iff.mp i.isLt)
    simpa using this

/-! ## The crossing events -/

/-- `crossedBy c W N` : some round up to `N` has reached the level `c`. -/
def crossedBy (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) (N : ℕ) :
    Set (ℕ → Fin k × ℝ) :=
  {ω | ∃ i ≤ N, c ≤ W i (banditTrajPrefix k i ω)}

/-- `crossedEver c W` : some round has reached the level `c`. -/
def crossedEver (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) :
    Set (ℕ → Fin k × ℝ) :=
  {ω | ∃ i, c ≤ W i (banditTrajPrefix k i ω)}

theorem crossedBy_mono (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    {M N : ℕ} (hMN : M ≤ N) : crossedBy c W M ⊆ crossedBy c W N := by
  rintro ω ⟨i, hi, hci⟩
  exact ⟨i, le_trans hi hMN, hci⟩

theorem crossedEver_eq_iUnion (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) :
    crossedEver c W = ⋃ N : ℕ, crossedBy c W N := by
  ext ω
  simp only [crossedEver, crossedBy, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, i, le_refl i, hi⟩
  · rintro ⟨N, i, _, hi⟩; exact ⟨i, hi⟩

theorem measurableSet_crossedBy (c : ℝ≥0∞) {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞}
    (hWm : ∀ n, Measurable (W n)) (N : ℕ) :
    MeasurableSet (crossedBy (k := k) c W N) := by
  have hset : crossedBy (k := k) c W N
      = ⋃ i : Fin (N + 1),
        {ω : ℕ → Fin k × ℝ | c ≤ W i.val (banditTrajPrefix k i.val ω)} := by
    ext ω
    simp only [crossedBy, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hci⟩; exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, hci⟩
    · rintro ⟨i, hci⟩; exact ⟨i.val, Nat.lt_succ_iff.mp i.isLt, hci⟩
  rw [hset]
  refine MeasurableSet.iUnion fun i ↦ ?_
  exact ((hWm i.val).comp measurable_banditTrajPrefix) measurableSet_Ici

/-! ## The key pointwise identities

Everything below is arithmetic on the indicator functions; the only probabilistic
input is `IsTrajWeight.step`, used once, at the very end of `ville_aux`. -/

open Classical in
/-- The survival indicator factorises: surviving through round `n+1` is surviving
through `n` *and* not crossing at `n+1`. -/
theorem survIndicator_succ (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    survIndicator c W (n + 1) (banditTrajPrefix k (n + 1) ω)
      = survIndicator c W n (banditTrajPrefix k n ω)
        * (if c ≤ W (n + 1) (banditTrajPrefix k (n + 1) ω) then 0 else 1) := by
  classical
  by_cases hsucc : Survives c W (n + 1) (banditTrajPrefix k (n + 1) ω)
  · have hall := (survives_prefix_iff c W (n + 1) ω).mp hsucc
    have hn : Survives c W n (banditTrajPrefix k n ω) :=
      (survives_prefix_iff c W n ω).mpr fun i hi ↦ hall i (le_trans hi (Nat.le_succ n))
    have hlast : ¬ (c ≤ W (n + 1) (banditTrajPrefix k (n + 1) ω)) :=
      not_le.mpr (hall (n + 1) (le_refl _))
    simp [survIndicator, hsucc, hn, hlast]
  · simp only [survIndicator, if_neg hsucc]
    by_cases hn : Survives c W n (banditTrajPrefix k n ω)
    · have hall := (survives_prefix_iff c W n ω).mp hn
      have hlast : c ≤ W (n + 1) (banditTrajPrefix k (n + 1) ω) := by
        by_contra hcon
        exact hsucc ((survives_prefix_iff c W (n + 1) ω).mpr fun i hi ↦ by
          rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with h | h
          · exact hall i (Nat.lt_succ_iff.mp h)
          · subst h; exact not_le.mp hcon)
      simp [hn, hlast]
    · simp [hn]

/-- If a crossing has happened by round `n+1` then either it had happened by
round `n`, or the trajectory survived through `n` and crosses at `n+1`. -/
theorem crossedBy_succ_subset (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (n : ℕ) :
    crossedBy (k := k) c W (n + 1)
      ⊆ crossedBy c W n
        ∪ ({ω | Survives c W n (banditTrajPrefix k n ω)}
            ∩ {ω | c ≤ W (n + 1) (banditTrajPrefix k (n + 1) ω)}) := by
  rintro ω ⟨i, hi, hci⟩
  by_cases hn : ∃ j ≤ n, c ≤ W j (banditTrajPrefix k j ω)
  · exact Or.inl hn
  · refine Or.inr ⟨?_, ?_⟩
    · refine (survives_prefix_iff c W n ω).mpr fun j hj ↦ ?_
      by_contra hcon
      exact hn ⟨j, hj, not_lt.mp hcon⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with h | h
      · exact absurd ⟨i, Nat.lt_succ_iff.mp h, hci⟩ hn
      · subst h; exact hci

theorem crossedBy_zero (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞) :
    crossedBy (k := k) c W 0 = {ω | c ≤ W 0 (banditTrajPrefix k 0 ω)} := by
  ext ω
  simp only [crossedBy, Set.mem_setOf_eq, Nat.le_zero]
  constructor
  · rintro ⟨i, hi, hci⟩; subst hi; exact hci
  · intro h; exact ⟨0, rfl, h⟩

open Classical in
theorem survIndicator_zero (c : ℝ≥0∞) (W : (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (hst : BanditHistory k 0) :
    survIndicator c W 0 hst = if c ≤ W 0 hst then 0 else 1 := by
  classical
  have hiff : Survives c W 0 hst ↔ W 0 hst < c := by
    constructor
    · intro h; exact h ⟨0, Nat.zero_lt_succ 0⟩
    · intro h i
      have hi : i = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by omega)
      subst hi
      exact h
  by_cases hc : c ≤ W 0 hst
  · simp [survIndicator, hiff, not_lt.mpr hc, if_pos hc]
  · simp [survIndicator, hiff, not_le.mp hc, if_neg hc]

/-! ## The level-splitting estimate

The single measure-theoretic step of the argument, isolated: for a `{0,1}`-valued
weight `g` and a nonnegative `f`, splitting `g` at the level `c` of `f` loses at
least `c` times the mass of the part where the level is reached. -/

open Classical in
theorem level_split_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : ℝ≥0∞)
    {g f : Ω → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    (∫⁻ ω, g ω * (if c ≤ f ω then 0 else 1) * f ω ∂μ)
        + c * μ ({ω | g ω = 1} ∩ {ω | c ≤ f ω})
      ≤ ∫⁻ ω, g ω * f ω ∂μ := by
  classical
  set S : Set Ω := {ω | g ω = 1} ∩ {ω | c ≤ f ω} with hSdef
  have hSmeas : MeasurableSet S :=
    (hg (measurableSet_singleton 1)).inter (hf measurableSet_Ici)
  have hsplit : ∀ ω, g ω * (if c ≤ f ω then 0 else 1) * f ω
      + g ω * (if c ≤ f ω then 1 else 0) * f ω = g ω * f ω := by
    intro ω
    by_cases hc : c ≤ f ω <;> simp [hc]
  have hdom : ∀ ω, S.indicator (fun _ ↦ c) ω ≤ g ω * (if c ≤ f ω then 1 else 0) * f ω := by
    intro ω
    by_cases hω : ω ∈ S
    · have hg1 : g ω = 1 := hω.1
      have hcf : c ≤ f ω := hω.2
      rw [Set.indicator_of_mem hω, hg1, if_pos hcf, one_mul, one_mul]
      exact hcf
    · rw [Set.indicator_of_notMem hω]
      exact zero_le'
  have hcS : c * μ S = ∫⁻ ω, S.indicator (fun _ ↦ c) ω ∂μ :=
    (lintegral_indicator_const hSmeas c).symm
  have hmeas1 : Measurable fun ω ↦ g ω * (if c ≤ f ω then 0 else 1) * f ω :=
    (hg.mul (Measurable.ite (hf measurableSet_Ici) measurable_const measurable_const)).mul hf
  calc (∫⁻ ω, g ω * (if c ≤ f ω then 0 else 1) * f ω ∂μ) + c * μ S
      ≤ (∫⁻ ω, g ω * (if c ≤ f ω then 0 else 1) * f ω ∂μ)
        + ∫⁻ ω, g ω * (if c ≤ f ω then 1 else 0) * f ω ∂μ := by
        rw [hcS]
        exact add_le_add le_rfl (lintegral_mono hdom)
    _ = ∫⁻ ω, (g ω * (if c ≤ f ω then 0 else 1) * f ω
          + g ω * (if c ≤ f ω then 1 else 0) * f ω) ∂μ := (lintegral_add_left hmeas1 _).symm
    _ = ∫⁻ ω, g ω * f ω ∂μ := lintegral_congr hsplit

/-! ## Ville's inequality -/

/-- The induction underlying Ville's inequality: at every horizon `N`, the mass
still carried by the surviving trajectories plus `c` times the probability of a
crossing before `N` is at most the total mass `1`. -/
theorem ville_aux {P : Measure (ℕ → Fin k × ℝ)} {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞}
    (hW : IsTrajWeight P W) (c : ℝ≥0∞) (N : ℕ) :
    (∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
        * W N (banditTrajPrefix k N ω) ∂P)
      + c * P (crossedBy c W N) ≤ 1 := by
  classical
  induction N with
  | zero =>
      have hsplit := level_split_le (Ω := ℕ → Fin k × ℝ) P c
        (g := fun _ ↦ (1 : ℝ≥0∞))
        (f := fun ω ↦ W 0 (banditTrajPrefix k 0 ω))
        measurable_const ((hW.meas 0).comp measurable_banditTrajPrefix)
      simp only [one_mul] at hsplit
      have hset : ({ω : ℕ → Fin k × ℝ | True}
          ∩ {ω : ℕ → Fin k × ℝ | c ≤ W 0 (banditTrajPrefix k 0 ω)})
          = crossedBy (k := k) c W 0 := by
        rw [crossedBy_zero]
        ext ω; simp
      rw [hset] at hsplit
      refine le_trans (le_of_eq ?_) (le_trans hsplit (le_of_eq (hW.lintegral_eq_one 0)))
      congr 1
      exact lintegral_congr fun ω ↦ by rw [survIndicator_zero]
  | succ N ih =>
      have hsplit := level_split_le (Ω := ℕ → Fin k × ℝ) P c
        (g := fun ω ↦ survIndicator c W N (banditTrajPrefix k N ω))
        (f := fun ω ↦ W (N + 1) (banditTrajPrefix k (N + 1) ω))
        ((measurable_survIndicator c hW.meas N).comp measurable_banditTrajPrefix)
        ((hW.meas (N + 1)).comp measurable_banditTrajPrefix)
      have hlhs : (∫⁻ ω, survIndicator c W (N + 1) (banditTrajPrefix k (N + 1) ω)
            * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P)
          = ∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
              * (if c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω) then 0 else 1)
              * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P := by
        refine lintegral_congr fun ω ↦ ?_
        rw [survIndicator_succ]
      have hsetS : ({ω : ℕ → Fin k × ℝ | survIndicator c W N (banditTrajPrefix k N ω) = 1}
            ∩ {ω : ℕ → Fin k × ℝ | c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω)})
          = {ω : ℕ → Fin k × ℝ | Survives c W N (banditTrajPrefix k N ω)}
            ∩ {ω : ℕ → Fin k × ℝ | c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω)} := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_congr_left_iff]
        intro _
        constructor
        · intro h
          by_contra hcon
          rw [survIndicator, if_neg hcon] at h
          exact zero_ne_one h
        · intro h; simp [survIndicator, h]
      rw [hsetS] at hsplit
      have hstep := hW.step N (survIndicator c W N) (measurable_survIndicator c hW.meas N)
      have hmono : P (crossedBy (k := k) c W (N + 1))
          ≤ P (crossedBy (k := k) c W N)
            + P ({ω : ℕ → Fin k × ℝ | Survives c W N (banditTrajPrefix k N ω)}
                ∩ {ω : ℕ → Fin k × ℝ | c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω)}) :=
        le_trans (measure_mono (crossedBy_succ_subset c W N)) (measure_union_le _ _)
      calc (∫⁻ ω, survIndicator c W (N + 1) (banditTrajPrefix k (N + 1) ω)
              * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P)
            + c * P (crossedBy c W (N + 1))
          ≤ (∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
              * (if c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω) then 0 else 1)
              * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P)
            + (c * P (crossedBy c W N)
              + c * P ({ω : ℕ → Fin k × ℝ | Survives c W N (banditTrajPrefix k N ω)}
                  ∩ {ω | c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω)})) := by
            rw [hlhs, ← mul_add]
            exact add_le_add le_rfl (by gcongr)
        _ = ((∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
                * (if c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω) then 0 else 1)
                * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P)
              + c * P ({ω : ℕ → Fin k × ℝ | Survives c W N (banditTrajPrefix k N ω)}
                  ∩ {ω | c ≤ W (N + 1) (banditTrajPrefix k (N + 1) ω)}))
            + c * P (crossedBy c W N) := by
            rw [add_assoc, add_comm (c * P (crossedBy c W N)), ← add_assoc]
        _ ≤ (∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
              * W (N + 1) (banditTrajPrefix k (N + 1) ω) ∂P)
            + c * P (crossedBy c W N) := add_le_add hsplit le_rfl
        _ = (∫⁻ ω, survIndicator c W N (banditTrajPrefix k N ω)
              * W N (banditTrajPrefix k N ω) ∂P)
            + c * P (crossedBy c W N) := by rw [hstep]
        _ ≤ 1 := ih

/-- **Ville's maximal inequality** for a bandit exponential weight: a nonnegative
weight with unit mass and the one-step martingale property reaches the level `c`
at *some* round with probability at most `1/c`, uniformly in the horizon. -/
theorem ville_inequality {P : Measure (ℕ → Fin k × ℝ)}
    {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞} (hW : IsTrajWeight P W) (c : ℝ≥0∞) :
    c * P (crossedEver c W) ≤ 1 := by
  have hmono : Monotone (crossedBy (k := k) c W) := fun _ _ h ↦ crossedBy_mono c W h
  rw [crossedEver_eq_iUnion, hmono.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun N ↦ le_trans le_add_self (ville_aux hW c N)

/-- Ville's inequality in the form used downstream. -/
theorem ville_inequality' {P : Measure (ℕ → Fin k × ℝ)}
    {W : (n : ℕ) → BanditHistory k n → ℝ≥0∞} (hW : IsTrajWeight P W) (c : ℝ≥0∞) :
    P (crossedEver c W) ≤ c⁻¹ := by
  have h := ville_inequality hW c
  rw [ENNReal.le_inv_iff_mul_le]
  rwa [mul_comm] at h

end BanditAlgorithm

/-!
# The vector-tilt exponential martingale

The martingale of `ExpMartingale` tilts a single arm.  Tilting *every* arm at once,
by its own parameter `λ_i`, costs nothing extra — the one-round integral is `1`
whichever arm is played — and gives

  `E[ exp( Σ_i (λ_i (S_i(n) − T_i(n) μ_i) − λ_i² T_i(n)/2) ) ] = 1`.

This is the object the *multivariate* self-normalised bound is built from, and it
is the version Track-and-Stop actually needs: the threshold of L&S Lemma 33.7 is
`f(x) = e^{k−x}(x/k)^k`, whose polynomial factor `(x/k)^k` comes precisely from a
`k`-dimensional mixture over the tilt vector `λ ∈ ℝ^k`.  A one-dimensional,
per-arm bound cannot produce it — summing the per-arm estimate over rounds
diverges for `k ≤ 3`.

The proof is the same induction as in the scalar case: at round `n+1` only the
coordinate of the arm actually played changes, and it changes by exactly that
arm's tilt.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The one-round tilt of the arm that was played, by its own parameter. -/
noncomputable def expTiltVec (μvec : Fin k → ℝ) (lams : Fin k → ℝ) (y : Fin k × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (lams y.1 * (y.2 - μvec y.1) - (lams y.1) ^ 2 / 2))

theorem measurable_expTiltVec (μvec : Fin k → ℝ) (lams : Fin k → ℝ) :
    Measurable (expTiltVec μvec lams) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.exp ?_)
  have hl : Measurable fun y : Fin k × ℝ ↦ lams y.1 := measurable_from_top.comp measurable_fst
  have hm : Measurable fun y : Fin k × ℝ ↦ μvec y.1 := measurable_from_top.comp measurable_fst
  exact (hl.mul (measurable_snd.sub hm)).sub ((hl.pow_const 2).div_const 2)

/-- The vector tilt integrates to `1` against the reward distribution of any arm. -/
theorem lintegral_expTiltVec_arm (μvec : Fin k → ℝ) (lams : Fin k → ℝ) (b : Fin k) :
    ∫⁻ x, expTiltVec μvec lams (b, x) ∂(gaussianReal (μvec b) 1) = 1 := by
  have hfun : (fun x : ℝ ↦ expTiltVec μvec lams (b, x))
      = fun x : ℝ ↦ ENNReal.ofReal (Real.exp (lams b * (x - μvec b) - (lams b) ^ 2 / 2)) := rfl
  rw [hfun, lintegral_expTilt_gaussianReal]

theorem lintegral_expTiltVec_stepKernel (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (lams : Fin k → ℝ) (h : BanditHistory k n) :
    ∫⁻ y, expTiltVec μvec lams y ∂(banditStepKernel (gaussianBandit μvec) pol n h) = 1 := by
  classical
  rw [banditStepKernel, Kernel.lintegral_compProd _ _ _ (measurable_expTiltVec μvec lams)]
  have hrk : ∀ b : Fin k,
      banditRewardKernel (gaussianBandit μvec) b = gaussianReal (μvec b) 1 := fun _ ↦ rfl
  simp only [Kernel.comap_apply, hrk]
  refine Eq.trans (lintegral_congr (g := fun _ : Fin k ↦ (1 : ℝ≥0∞)) fun b ↦ ?_) ?_
  · exact lintegral_expTiltVec_arm μvec lams b
  · rw [lintegral_one, measure_univ]

/-- The one-step identity for the vector tilt. -/
theorem lintegral_mul_expTiltVec (μvec : Fin k → ℝ) (pol : BanditPolicy k) (n : ℕ)
    (lams : Fin k → ℝ) (F : BanditHistory k n → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (banditTrajPrefix k n ω) * expTiltVec μvec lams (ω n)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol)
      = ∫⁻ ω, F (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) := by
  classical
  set ν : StochasticBandit k := gaussianBandit μvec with hν
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure ν pol with hP
  set G : BanditHistory k n × (Fin k × ℝ) → ℝ≥0∞ := fun p ↦ F p.1 * expTiltVec μvec lams p.2
    with hG
  have hGmeas : Measurable G :=
    (hF.comp measurable_fst).mul ((measurable_expTiltVec μvec lams).comp measurable_snd)
  have hmap : Measurable (fun ω : ℕ → Fin k × ℝ ↦ (banditTrajPrefix k n ω, ω n)) :=
    measurable_banditTrajPrefix.prodMk (measurable_pi_apply n)
  have hL : ∫⁻ ω, F (banditTrajPrefix k n ω) * expTiltVec μvec lams (ω n) ∂P
      = ∫⁻ p, G p ∂(P.map (fun ω ↦ (banditTrajPrefix k n ω, ω n))) := by
    rw [lintegral_map hGmeas hmap]
  rw [hL, banditTrajMeasure_joint_eq_compProd ν pol n, Measure.lintegral_compProd hGmeas]
  have hinner : ∀ h : BanditHistory k n,
      ∫⁻ y, G (h, y) ∂(banditStepKernel ν pol n h) = F h := by
    intro h
    have hfun : (fun y ↦ G (h, y)) = fun y ↦ F h * expTiltVec μvec lams y := rfl
    rw [hfun, lintegral_const_mul _ (measurable_expTiltVec μvec lams),
      lintegral_expTiltVec_stepKernel μvec pol n lams h, mul_one]
  simp only [hinner]
  rw [lintegral_map hF measurable_banditTrajPrefix]

/-! ## The vector weight -/

/-- The exponent `Σ_i (λ_i (S_i − T_i μ_i) − λ_i² T_i / 2)` on histories. -/
noncomputable def vecExponent (μvec : Fin k → ℝ) (lams : Fin k → ℝ) {n : ℕ}
    (hst : BanditHistory k n) : ℝ :=
  ∑ i : Fin k, (lams i * (histRewardSum i hst - (histPullCount i hst : ℝ) * μvec i)
    - (lams i) ^ 2 * (histPullCount i hst : ℝ) / 2)

/-- The vector exponential weight. -/
noncomputable def expWeightVec (μvec : Fin k → ℝ) (lams : Fin k → ℝ) {n : ℕ}
    (hst : BanditHistory k n) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (vecExponent μvec lams hst))

theorem measurable_expWeightVec (μvec : Fin k → ℝ) (lams : Fin k → ℝ) (n : ℕ) :
    Measurable (expWeightVec (k := k) μvec lams (n := n)) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.exp ?_)
  unfold vecExponent
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have h1 : Measurable fun hst : BanditHistory k n ↦ (histPullCount i hst : ℝ) :=
    measurable_from_top.comp (measurable_histPullCount i n)
  exact (((measurable_histRewardSum i n).sub (h1.mul measurable_const)).const_mul (lams i)).sub
    ((h1.const_mul ((lams i) ^ 2)).div_const 2)

/-- The one-round recursion: only the coordinate of the arm played changes. -/
theorem vecExponent_succ (μvec : Fin k → ℝ) (lams : Fin k → ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    vecExponent μvec lams (banditTrajPrefix k (n + 1) ω)
      = vecExponent μvec lams (banditTrajPrefix k n ω)
        + (lams (ω n).1 * ((ω n).2 - μvec (ω n).1) - (lams (ω n).1) ^ 2 / 2) := by
  classical
  have key : vecExponent μvec lams (banditTrajPrefix k (n + 1) ω)
      - vecExponent μvec lams (banditTrajPrefix k n ω)
      = lams (ω n).1 * ((ω n).2 - μvec (ω n).1) - (lams (ω n).1) ^ 2 / 2 := by
    unfold vecExponent
    rw [← Finset.sum_sub_distrib]
    refine (Finset.sum_eq_single (ω n).1 (fun i _ hi ↦ ?_)
      (fun hi ↦ absurd (Finset.mem_univ _) hi)).trans ?_
    · simp only [histPullCount_prefix, histRewardSum_prefix, trajPullCount_succ,
        trajRewardSum_succ, if_neg (Ne.symm hi)]
      push_cast
      ring
    · simp only [histPullCount_prefix, histRewardSum_prefix, trajPullCount_succ,
        trajRewardSum_succ, if_pos rfl]
      push_cast
      ring
  linarith

/-- **The vector-tilt exponential martingale has expectation one.** -/
theorem lintegral_expWeightVec (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (lams : Fin k → ℝ) (n : ℕ) :
    ∫⁻ ω, expWeightVec μvec lams (banditTrajPrefix k n ω)
        ∂(banditTrajMeasure (gaussianBandit μvec) pol) = 1 := by
  induction n with
  | zero =>
      have h0 : ∀ ω : ℕ → Fin k × ℝ,
          expWeightVec μvec lams (banditTrajPrefix k 0 ω) = 1 := by
        intro ω
        unfold expWeightVec vecExponent histPullCount histRewardSum
        simp
      simp only [h0]
      rw [lintegral_one, measure_univ]
  | succ n ih =>
      have hrw : ∀ ω : ℕ → Fin k × ℝ,
          expWeightVec μvec lams (banditTrajPrefix k (n + 1) ω)
            = expWeightVec μvec lams (banditTrajPrefix k n ω) * expTiltVec μvec lams (ω n) := by
        intro ω
        unfold expWeightVec expTiltVec
        rw [vecExponent_succ, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp only [hrw]
      rw [lintegral_mul_expTiltVec μvec pol n lams (expWeightVec μvec lams)
        (measurable_expWeightVec μvec lams n)]
      exact ih

end BanditAlgorithm

/-!
# Mixing bandit martingales

The exponential martingale of a Gaussian bandit is a *family*, indexed by the
tilt: for each fixed `λ` the weight `exp(λ(S_a − T_a μ_a) − λ² T_a/2)` has unit
mass and the one-step martingale property.  A fixed tilt is of no use when the
optimal one depends on the realised pull counts, which are random — the standard
remedy is to average the family against a prior on `λ`, and the resulting
*mixture* is again a martingale.

This file proves that in the generality the development needs:

* `isTrajWeight_mixture` — averaging any family of `IsTrajWeight`s against a
  probability density on an arbitrary index space produces an `IsTrajWeight`;
* `isTrajWeight_expWeightVec` — for each fixed tilt *vector* the vector
  exponential weight is an `IsTrajWeight`.

Combining the two with the Gaussian density of `Solutions/GaussianMixture.lean`
is what produces the self-normalised weight that Ville's inequality is applied
to.  The only analytic input is Tonelli's theorem; the martingale property of the
mixture is inherited coordinatewise from the family.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Interchanging a mixture with the trajectory measure -/

/-- Tonelli, in the shape the mixture argument uses: a density-weighted average
over the index space commutes with the trajectory integral. -/
theorem lintegral_mixture_swap {ι Ω : Type*} [MeasurableSpace ι] [MeasurableSpace Ω]
    (ν : Measure ι) [SFinite ν] (P : Measure Ω) [SFinite P]
    (ρ : ι → ℝ≥0∞) (H : ι → Ω → ℝ≥0∞)
    (hH : Measurable fun q : ι × Ω ↦ H q.1 q.2) (hρm : Measurable ρ) :
    ∫⁻ ω, (∫⁻ i, ρ i * H i ω ∂ν) ∂P = ∫⁻ i, ρ i * (∫⁻ ω, H i ω ∂P) ∂ν := by
  have hswap : ∫⁻ ω, (∫⁻ i, ρ i * H i ω ∂ν) ∂P
      = ∫⁻ i, (∫⁻ ω, ρ i * H i ω ∂P) ∂ν := by
    rw [lintegral_lintegral_swap]
    refine Measurable.aemeasurable ?_
    exact ((hρm.comp measurable_snd).mul
      (hH.comp (measurable_snd.prodMk measurable_fst)))
  rw [hswap]
  refine lintegral_congr fun i ↦ ?_
  exact lintegral_const_mul _ (hH.comp ((measurable_const (a := i)).prodMk measurable_id))

/-- **A mixture of bandit martingales is a bandit martingale.**  If `ρ` is a
probability density on an index space `ι` and `W i` is an `IsTrajWeight` for each
`i`, then the average `∫ ρ i · W i dν` is an `IsTrajWeight`. -/
theorem isTrajWeight_mixture {ι : Type*} [MeasurableSpace ι] (ν : Measure ι) [SFinite ν]
    {P : Measure (ℕ → Fin k × ℝ)} [SFinite P]
    (ρ : ι → ℝ≥0∞) (hρm : Measurable ρ) (hρ : ∫⁻ i, ρ i ∂ν = 1)
    (W : ι → (n : ℕ) → BanditHistory k n → ℝ≥0∞)
    (hjoint : ∀ n, Measurable fun q : ι × BanditHistory k n ↦ W q.1 n q.2)
    (hW : ∀ i, IsTrajWeight P (W i)) :
    IsTrajWeight P (fun n hst ↦ ∫⁻ i, ρ i * W i n hst ∂ν) := by
  constructor
  · -- measurability of the mixture
    intro n
    have hmeas : Measurable fun q : BanditHistory k n × ι ↦ ρ q.2 * W q.2 n q.1 :=
      (hρm.comp measurable_snd).mul
        ((hjoint n).comp (measurable_snd.prodMk measurable_fst))
    exact hmeas.lintegral_prod_right'
  · -- unit mass
    have hH : Measurable fun q : ι × (ℕ → Fin k × ℝ) ↦ W q.1 0 (banditTrajPrefix k 0 q.2) :=
      (hjoint 0).comp (measurable_fst.prodMk
        (measurable_banditTrajPrefix.comp measurable_snd))
    rw [lintegral_mixture_swap ν P ρ
      (fun i ω ↦ W i 0 (banditTrajPrefix k 0 ω)) hH hρm]
    simp only [(hW _).init, mul_one]
    exact hρ
  · -- the one-step martingale property, inherited coordinatewise
    intro n F hF
    have hHsucc : Measurable fun q : ι × (ℕ → Fin k × ℝ) ↦
        F (banditTrajPrefix k n q.2) * W q.1 (n + 1) (banditTrajPrefix k (n + 1) q.2) :=
      ((hF.comp measurable_banditTrajPrefix).comp measurable_snd).mul
        ((hjoint (n + 1)).comp (measurable_fst.prodMk
          (measurable_banditTrajPrefix.comp measurable_snd)))
    have hHcur : Measurable fun q : ι × (ℕ → Fin k × ℝ) ↦
        F (banditTrajPrefix k n q.2) * W q.1 n (banditTrajPrefix k n q.2) :=
      ((hF.comp measurable_banditTrajPrefix).comp measurable_snd).mul
        ((hjoint n).comp (measurable_fst.prodMk
          (measurable_banditTrajPrefix.comp measurable_snd)))
    -- pulling the `𝓕_n`-measurable factor inside the mixture, at both rounds
    have hpull : ∀ (m : ℕ) (hst : BanditHistory k m) (c : ℝ≥0∞),
        c * (∫⁻ i, ρ i * W i m hst ∂ν) = ∫⁻ i, ρ i * (c * W i m hst) ∂ν := by
      intro m hst c
      have hmeas : Measurable fun i ↦ ρ i * W i m hst :=
        hρm.mul ((hjoint m).comp (measurable_id.prodMk measurable_const))
      rw [← lintegral_const_mul c hmeas]
      exact lintegral_congr fun i ↦ by ring
    calc ∫⁻ ω, F (banditTrajPrefix k n ω)
            * (∫⁻ i, ρ i * W i (n + 1) (banditTrajPrefix k (n + 1) ω) ∂ν) ∂P
        = ∫⁻ ω, (∫⁻ i, ρ i * (F (banditTrajPrefix k n ω)
              * W i (n + 1) (banditTrajPrefix k (n + 1) ω)) ∂ν) ∂P := by
          exact lintegral_congr fun ω ↦ hpull _ _ _
      _ = ∫⁻ i, ρ i * (∫⁻ ω, F (banditTrajPrefix k n ω)
              * W i (n + 1) (banditTrajPrefix k (n + 1) ω) ∂P) ∂ν :=
          lintegral_mixture_swap ν P ρ _ hHsucc hρm
      _ = ∫⁻ i, ρ i * (∫⁻ ω, F (banditTrajPrefix k n ω)
              * W i n (banditTrajPrefix k n ω) ∂P) ∂ν := by
          exact lintegral_congr fun i ↦ by rw [(hW i).step n F hF]
      _ = ∫⁻ ω, (∫⁻ i, ρ i * (F (banditTrajPrefix k n ω)
              * W i n (banditTrajPrefix k n ω)) ∂ν) ∂P :=
          (lintegral_mixture_swap ν P ρ _ hHcur hρm).symm
      _ = ∫⁻ ω, F (banditTrajPrefix k n ω)
            * (∫⁻ i, ρ i * W i n (banditTrajPrefix k n ω) ∂ν) ∂P := by
          exact lintegral_congr fun ω ↦ (hpull _ _ _).symm

/-! ## The vector exponential weight is a bandit martingale

The content is already in `Solutions/VectorMartingale.lean`; this repackages it
in the form `Solutions/VilleEngine.lean` consumes. -/

/-- The vector exponential weight factorises across a round: only the coordinate
of the arm played changes, and it changes by exactly that arm's tilt. -/
theorem expWeightVec_succ (μvec : Fin k → ℝ) (lams : Fin k → ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expWeightVec μvec lams (banditTrajPrefix k (n + 1) ω)
      = expWeightVec μvec lams (banditTrajPrefix k n ω) * expTiltVec μvec lams (ω n) := by
  unfold expWeightVec expTiltVec
  rw [vecExponent_succ, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **For each fixed tilt vector, the vector exponential weight is an
`IsTrajWeight`.**  This is the family that the Gaussian prior is averaged over. -/
theorem isTrajWeight_expWeightVec (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (lams : Fin k → ℝ) :
    IsTrajWeight (banditTrajMeasure (gaussianBandit μvec) pol)
      (fun n ↦ expWeightVec (k := k) μvec lams (n := n)) := by
  constructor
  · exact fun n ↦ measurable_expWeightVec μvec lams n
  · exact lintegral_expWeightVec μvec pol lams 0
  · intro n F hF
    have hrw : ∀ ω : ℕ → Fin k × ℝ,
        F (banditTrajPrefix k n ω) * expWeightVec μvec lams (banditTrajPrefix k (n + 1) ω)
          = (fun hst ↦ F hst * expWeightVec μvec lams hst) (banditTrajPrefix k n ω)
            * expTiltVec μvec lams (ω n) := by
      intro ω
      rw [expWeightVec_succ, ← mul_assoc]
    rw [lintegral_congr hrw]
    exact lintegral_mul_expTiltVec μvec pol n lams
      (fun hst ↦ F hst * expWeightVec μvec lams hst)
      (hF.mul (measurable_expWeightVec μvec lams n))

end BanditAlgorithm

theorem _root_.solution {k : ℕ} {ι : Type*}
    [MeasurableSpace ι] (ν : MeasureTheory.Measure ι) [MeasureTheory.SFinite ν]
    (P : MeasureTheory.Measure (ℕ → Fin k × ℝ)) [MeasureTheory.SFinite P]
    (ρ : ι → ENNReal) (hρm : Measurable ρ) (hρ : ∫⁻ i, ρ i ∂ν = 1)
    (W : ι → (n : ℕ) → BanditAlgorithm.BanditHistory k n → ENNReal)
    (hjoint : ∀ n, Measurable fun q : ι × BanditAlgorithm.BanditHistory k n ↦ W q.1 n q.2)
    (hinit : ∀ i, ∫⁻ ω, W i 0 (BanditAlgorithm.banditTrajPrefix k 0 ω) ∂P = 1)
    (hstep : ∀ (i : ι) (n : ℕ) (F : BanditAlgorithm.BanditHistory k n → ENNReal),
      Measurable F →
        ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
            * W i (n + 1) (BanditAlgorithm.banditTrajPrefix k (n + 1) ω) ∂P
          = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
            * W i n (BanditAlgorithm.banditTrajPrefix k n ω) ∂P) :
    (∀ n : ℕ, Measurable fun hst : BanditAlgorithm.BanditHistory k n ↦ ∫⁻ i, ρ i * W i n hst ∂ν)
      ∧ (∫⁻ ω, (∫⁻ i, ρ i * W i 0 (BanditAlgorithm.banditTrajPrefix k 0 ω) ∂ν) ∂P = 1)
      ∧ ∀ (n : ℕ) (F : BanditAlgorithm.BanditHistory k n → ENNReal), Measurable F →
          ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
              * (∫⁻ i, ρ i * W i (n + 1)
                  (BanditAlgorithm.banditTrajPrefix k (n + 1) ω) ∂ν) ∂P
            = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
              * (∫⁻ i, ρ i * W i n (BanditAlgorithm.banditTrajPrefix k n ω) ∂ν) ∂P := by
  have h := BanditAlgorithm.isTrajWeight_mixture ν ρ hρm hρ W hjoint
    (fun i ↦ ⟨fun n ↦ ((hjoint n).comp
      ((measurable_const (a := i)).prodMk measurable_id)), hinit i, hstep i⟩)
  exact ⟨h.meas, h.init, h.step⟩
