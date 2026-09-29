-- Prove2me | solution 1 for BanditAlgorithm.chernoff_pairwise_selfnormalised_deviation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T21:54:27.312434+00:00
-- url     : https://prove2.me/submissions/0950d99f-3a8e-4eec-b906-f85bb08388e7

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
import Definitions.Def_GaussianBandit
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Definitions.Def_TrackAndStop
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp

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

/-!
# The Gaussian integral with a linear term

`∫ exp(−a x² + c x) dx = √(π/a) · exp(c²/(4a))` for `a > 0`.

Mathlib has the pure Gaussian integral `∫ exp(−b x²) = √(π/b)` but not the
completed-square version with a linear term, which is what every "method of
mixtures" computation needs: mixing the bandit exponential martingale
`exp(λ z − λ² t/2)` over a Gaussian prior on the tilt `λ` is exactly this integral
with `a = (1+t)/2` and `c = z`, and produces the self-normalised weight
`(1+t)^{−1/2} exp(z²/(2(1+t)))`.

The proof is completing the square and translating.
-/

open MeasureTheory Real

namespace BanditAlgorithm

/-- **The Gaussian integral with a linear term.** -/
theorem integral_exp_quadratic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2 + c * x)
      = Real.sqrt (π / a) * Real.exp (c ^ 2 / (4 * a)) := by
  have hrw : (fun x : ℝ ↦ Real.exp (-a * x ^ 2 + c * x))
      = fun x : ℝ ↦ Real.exp (c ^ 2 / (4 * a)) *
        (fun y : ℝ ↦ Real.exp (-a * y ^ 2)) (x - c / (2 * a)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hrw, integral_const_mul,
    integral_sub_right_eq_self (fun y : ℝ ↦ Real.exp (-a * y ^ 2)) (c / (2 * a)),
    integral_gaussian]
  ring

/-- The mixture weight: integrating the exponential tilt `exp(λ z − λ² t / 2)`
against the standard Gaussian density in `λ`. -/
theorem integral_exp_tilt_mixture {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫ lam : ℝ, (Real.sqrt (2 * π))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2)
      = (Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t))) := by
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have ha : (0 : ℝ) < (1 + t) / 2 := by linarith
  have hrw : (fun lam : ℝ ↦ (Real.sqrt (2 * π))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2))
      = fun lam : ℝ ↦ (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-((1 + t) / 2) * lam ^ 2 + z * lam) := by
    funext lam
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hrw, integral_const_mul, integral_exp_quadratic ha z]
  have hsqrt : Real.sqrt (π / ((1 + t) / 2)) = Real.sqrt (2 * π) * (Real.sqrt (1 + t))⁻¹ := by
    rw [show π / ((1 + t) / 2) = (2 * π) / (1 + t) by field_simp]
    rw [Real.sqrt_div' _ (by positivity), div_eq_mul_inv]
  rw [hsqrt]
  have hexp : z ^ 2 / (4 * ((1 + t) / 2)) = z ^ 2 / (2 * (1 + t)) := by
    congr 1
    ring
  rw [hexp]
  have h2π : Real.sqrt (2 * π) ≠ 0 := by positivity
  field_simp

end BanditAlgorithm

/-!
# The Gaussian mixture of an exponential tilt, in `ℝ≥0∞`

`Solutions/GaussianQuadratic.lean` computes the mixture

  `∫ φ(λ) e^{λ z − λ² t/2} dλ = (1 + t)^{−1/2} e^{z²/(2(1+t))}`

as a Bochner integral.  Every use of it downstream sits inside a Tonelli
interchange with the trajectory measure, so what is actually needed is the
`ℝ≥0∞`-valued version, together with the two-dimensional product form: the pair
statistic of Chernoff's stopping rule involves two arms, so the mixing is over
`λ = (λ_a, λ_b) ∈ ℝ²` against the standard Gaussian density of the plane.

Converting between the two costs an integrability proof, which is the reason
`integrable_exp_quadratic` is here: the integrand is a Gaussian with a linear
term, integrable by the same translation that evaluates it.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

/-- The standard Gaussian density on the line. -/
noncomputable def stdGaussianPDF (x : ℝ) : ℝ :=
  (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2)

theorem stdGaussianPDF_pos (x : ℝ) : 0 < stdGaussianPDF x := by
  unfold stdGaussianPDF
  have h2π : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem stdGaussianPDF_nonneg (x : ℝ) : 0 ≤ stdGaussianPDF x := (stdGaussianPDF_pos x).le

theorem measurable_stdGaussianPDF : Measurable stdGaussianPDF := by
  unfold stdGaussianPDF
  fun_prop

/-- A Gaussian with a linear term is integrable. -/
theorem integrable_exp_quadratic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (-a * x ^ 2 + c * x)) := by
  have hrw : (fun x : ℝ ↦ Real.exp (-a * x ^ 2 + c * x))
      = fun x : ℝ ↦ Real.exp (c ^ 2 / (4 * a)) *
        (fun y : ℝ ↦ Real.exp (-a * y ^ 2)) (x - c / (2 * a)) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hrw]
  exact ((integrable_exp_neg_mul_sq ha).comp_sub_right (c / (2 * a))).const_mul _

/-- The mixture integrand is integrable. -/
theorem integrable_tilt_mixture {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    Integrable (fun lam : ℝ ↦
      stdGaussianPDF lam * Real.exp (lam * z - lam ^ 2 * t / 2)) := by
  have ha : (0 : ℝ) < (1 + t) / 2 := by linarith
  have hrw : (fun lam : ℝ ↦ stdGaussianPDF lam * Real.exp (lam * z - lam ^ 2 * t / 2))
      = fun lam : ℝ ↦ (Real.sqrt (2 * π))⁻¹ *
        Real.exp (-((1 + t) / 2) * lam ^ 2 + z * lam) := by
    funext lam
    unfold stdGaussianPDF
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [hrw]
  exact (integrable_exp_quadratic ha z).const_mul _

/-- **The Gaussian mixture of an exponential tilt, in `ℝ≥0∞`.** -/
theorem lintegral_tilt_mixture {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫⁻ lam : ℝ, ENNReal.ofReal (stdGaussianPDF lam * Real.exp (lam * z - lam ^ 2 * t / 2))
      = ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tilt_mixture ht z)
    (Filter.Eventually.of_forall fun lam ↦ by
      have := stdGaussianPDF_nonneg lam
      positivity)]
  congr 1
  have hval := integral_exp_tilt_mixture ht z
  rw [← hval]
  apply integral_congr_ae
  filter_upwards with lam
  unfold stdGaussianPDF
  ring

/-! ## The two-dimensional mixture

The pair statistic of Chernoff's stopping rule involves two arms, so the mixing
measure is the standard Gaussian of the plane.  Tonelli reduces it to the
one-dimensional computation in each coordinate. -/

/-- The standard Gaussian density of the plane. -/
noncomputable def stdGaussianPDF₂ (p : ℝ × ℝ) : ℝ :=
  stdGaussianPDF p.1 * stdGaussianPDF p.2

theorem stdGaussianPDF₂_pos (p : ℝ × ℝ) : 0 < stdGaussianPDF₂ p :=
  mul_pos (stdGaussianPDF_pos _) (stdGaussianPDF_pos _)

theorem stdGaussianPDF₂_nonneg (p : ℝ × ℝ) : 0 ≤ stdGaussianPDF₂ p :=
  (stdGaussianPDF₂_pos p).le

theorem measurable_stdGaussianPDF₂ : Measurable stdGaussianPDF₂ := by
  unfold stdGaussianPDF₂
  exact (measurable_stdGaussianPDF.comp measurable_fst).mul
    (measurable_stdGaussianPDF.comp measurable_snd)

/-- **The two-dimensional Gaussian mixture of a pair of exponential tilts.** -/
theorem lintegral_tilt_mixture₂ {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (y z : ℝ) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (stdGaussianPDF₂ p
        * Real.exp ((p.1 * y - p.1 ^ 2 * s / 2) + (p.2 * z - p.2 ^ 2 * t / 2)))
      = ENNReal.ofReal ((Real.sqrt (1 + s))⁻¹ * Real.exp (y ^ 2 / (2 * (1 + s))))
        * ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) := by
  have hfac : ∀ p : ℝ × ℝ, ENNReal.ofReal (stdGaussianPDF₂ p
      * Real.exp ((p.1 * y - p.1 ^ 2 * s / 2) + (p.2 * z - p.2 ^ 2 * t / 2)))
      = ENNReal.ofReal (stdGaussianPDF p.1 * Real.exp (p.1 * y - p.1 ^ 2 * s / 2))
        * ENNReal.ofReal (stdGaussianPDF p.2 * Real.exp (p.2 * z - p.2 ^ 2 * t / 2)) := by
    intro p
    rw [← ENNReal.ofReal_mul (by
      have := stdGaussianPDF_nonneg p.1
      positivity)]
    congr 1
    unfold stdGaussianPDF₂
    rw [Real.exp_add]
    ring
  simp only [hfac]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod _ (by
    refine Measurable.aemeasurable ?_
    exact (ENNReal.measurable_ofReal.comp
        ((measurable_stdGaussianPDF.comp measurable_fst).mul
          (Measurable.exp (by fun_prop)))).mul
      (ENNReal.measurable_ofReal.comp
        ((measurable_stdGaussianPDF.comp measurable_snd).mul
          (Measurable.exp (by fun_prop)))))]
  have hinner : ∀ x : ℝ,
      ∫⁻ w : ℝ, ENNReal.ofReal (stdGaussianPDF x * Real.exp (x * y - x ^ 2 * s / 2))
          * ENNReal.ofReal (stdGaussianPDF w * Real.exp (w * z - w ^ 2 * t / 2))
        = ENNReal.ofReal (stdGaussianPDF x * Real.exp (x * y - x ^ 2 * s / 2))
          * ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) := by
    intro x
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tilt_mixture ht z]
  simp only [hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_tilt_mixture hs y]

end BanditAlgorithm

/-!
# The pair mixture martingale

Chernoff's stopping rule compares the threshold `β_t(δ)` against a statistic built
from *two* arms at a time, so the martingale that controls it mixes over a tilt
supported on a pair `{a, b}`.  Averaging the vector exponential martingale against
the standard Gaussian density of the plane in those two coordinates gives

  `M_n = (1 + T_a(n))^{−1/2} e^{Z_a(n)²/(2(1+T_a(n)))}
        · (1 + T_b(n))^{−1/2} e^{Z_b(n)²/(2(1+T_b(n)))}`,

where `Z_i(n) = S_i(n) − T_i(n) μ_i`.  Two things about `M_n` matter.  It is a
martingale of unit mass, by `isTrajWeight_mixture`, so Ville's inequality applies
to it *without any union over rounds*.  And its exponent is the self-normalised
deviation of the pair, up to replacing `T_i` by `1 + T_i` — a replacement which
only weakens the exponent, and whose cost is the explicit `(1 + T_i)^{−1/2}`
prefactor.  Those prefactors are exactly the polynomial term in the threshold
`f(x) = e^{k−x}(x/k)^k` of Lattimore--Szepesvári Lemma 33.7.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## A tilt supported on a pair of arms -/

/-- The tilt vector that is `la` on arm `a`, `lb` on arm `b` and zero elsewhere. -/
noncomputable def pairTilt (a b : Fin k) (la lb : ℝ) : Fin k → ℝ :=
  fun i ↦ if i = a then la else if i = b then lb else 0

@[simp]
theorem pairTilt_left (a b : Fin k) (la lb : ℝ) : pairTilt a b la lb a = la := by
  simp [pairTilt]

@[simp]
theorem pairTilt_right {a b : Fin k} (hab : a ≠ b) (la lb : ℝ) :
    pairTilt a b la lb b = lb := by
  simp [pairTilt, Ne.symm hab]

theorem pairTilt_other {a b : Fin k} (la lb : ℝ) {i : Fin k} (hia : i ≠ a) (hib : i ≠ b) :
    pairTilt a b la lb i = 0 := by
  simp [pairTilt, hia, hib]

theorem measurable_pairTilt (a b : Fin k) (i : Fin k) :
    Measurable fun p : ℝ × ℝ ↦ pairTilt a b p.1 p.2 i := by
  unfold pairTilt
  by_cases hia : i = a
  · simp only [hia, if_pos rfl]
    exact measurable_fst
  · simp only [if_neg hia]
    by_cases hib : i = b
    · simp only [hib, if_pos rfl]
      exact measurable_snd
    · simp only [if_neg hib]
      exact measurable_const

/-- On a pair tilt the vector exponent collapses to the two-arm expression. -/
theorem vecExponent_pairTilt (μvec : Fin k → ℝ) {a b : Fin k} (hab : a ≠ b)
    (la lb : ℝ) {n : ℕ} (hst : BanditHistory k n) :
    vecExponent μvec (pairTilt a b la lb) hst
      = (la * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a)
          - la ^ 2 * (histPullCount a hst : ℝ) / 2)
        + (lb * (histRewardSum b hst - (histPullCount b hst : ℝ) * μvec b)
          - lb ^ 2 * (histPullCount b hst : ℝ) / 2) := by
  classical
  unfold vecExponent
  have hsub : ({a, b} : Finset (Fin k)) ⊆ Finset.univ := Finset.subset_univ _
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin k)), i ∉ ({a, b} : Finset (Fin k)) →
      (pairTilt a b la lb i
          * (histRewardSum i hst - (histPullCount i hst : ℝ) * μvec i)
        - (pairTilt a b la lb i) ^ 2 * (histPullCount i hst : ℝ) / 2) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    rw [pairTilt_other la lb hi.1 hi.2]
    ring
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair hab, pairTilt_left,
    pairTilt_right hab]

/-! ## The mixture -/

/-- The pair mixture weight: the vector exponential martingale averaged against
the standard Gaussian density of the plane in the coordinates `a` and `b`. -/
noncomputable def pairMixtureWeight (μvec : Fin k → ℝ) (a b : Fin k) (n : ℕ)
    (hst : BanditHistory k n) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (stdGaussianPDF₂ p)
    * expWeightVec μvec (pairTilt a b p.1 p.2) hst

/-- The Gaussian density of the plane is a probability density. -/
theorem lintegral_stdGaussianPDF₂ :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (stdGaussianPDF₂ p) = 1 := by
  have h := lintegral_tilt_mixture₂ (s := 0) (t := 0) le_rfl le_rfl 0 0
  simp only [mul_zero, zero_mul, sub_zero, zero_div, add_zero, Real.exp_zero, mul_one,
    zero_add, Real.sqrt_one, inv_one, one_mul, ENNReal.ofReal_one] at h
  simpa using h

/-- The mixture integrand is jointly measurable in the tilt and the history. -/
theorem measurable_pairMixture_integrand (μvec : Fin k → ℝ) (a b : Fin k) (n : ℕ) :
    Measurable fun q : (ℝ × ℝ) × BanditHistory k n ↦
      expWeightVec μvec (pairTilt a b q.1.1 q.1.2) q.2 := by
  classical
  refine ENNReal.measurable_ofReal.comp (Measurable.exp ?_)
  unfold vecExponent
  refine Finset.measurable_sum _ fun i _ ↦ ?_
  have hl : Measurable fun q : (ℝ × ℝ) × BanditHistory k n ↦ pairTilt a b q.1.1 q.1.2 i :=
    (measurable_pairTilt a b i).comp measurable_fst
  have hT : Measurable fun q : (ℝ × ℝ) × BanditHistory k n ↦ (histPullCount i q.2 : ℝ) :=
    (measurable_from_top.comp (measurable_histPullCount i n)).comp measurable_snd
  have hS : Measurable fun q : (ℝ × ℝ) × BanditHistory k n ↦ histRewardSum i q.2 :=
    (measurable_histRewardSum i n).comp measurable_snd
  exact (hl.mul (hS.sub (hT.mul measurable_const))).sub
    ((hl.pow_const 2).mul hT |>.div_const 2)

/-- **The pair mixture weight is a bandit martingale.** -/
theorem isTrajWeight_pairMixtureWeight (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (a b : Fin k) :
    IsTrajWeight (banditTrajMeasure (gaussianBandit μvec) pol)
      (fun n ↦ pairMixtureWeight (k := k) μvec a b n) := by
  have h := isTrajWeight_mixture (k := k) (ι := ℝ × ℝ) (volume : Measure (ℝ × ℝ))
    (P := banditTrajMeasure (gaussianBandit μvec) pol)
    (fun p ↦ ENNReal.ofReal (stdGaussianPDF₂ p))
    (ENNReal.measurable_ofReal.comp measurable_stdGaussianPDF₂)
    lintegral_stdGaussianPDF₂
    (fun p n hst ↦ expWeightVec μvec (pairTilt a b p.1 p.2) hst)
    (fun n ↦ measurable_pairMixture_integrand μvec a b n)
    (fun p ↦ isTrajWeight_expWeightVec μvec pol (pairTilt a b p.1 p.2))
  exact h

/-! ## The closed form -/

/-- **The closed form of the pair mixture weight.**  The Gaussian mixture of the
two tilts evaluates to the self-normalised weight of the pair. -/
theorem pairMixtureWeight_eq (μvec : Fin k → ℝ) {a b : Fin k} (hab : a ≠ b) (n : ℕ)
    (hst : BanditHistory k n) :
    pairMixtureWeight μvec a b n hst
      = ENNReal.ofReal ((Real.sqrt (1 + (histPullCount a hst : ℝ)))⁻¹
          * Real.exp ((histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a) ^ 2
              / (2 * (1 + (histPullCount a hst : ℝ)))))
        * ENNReal.ofReal ((Real.sqrt (1 + (histPullCount b hst : ℝ)))⁻¹
          * Real.exp ((histRewardSum b hst - (histPullCount b hst : ℝ) * μvec b) ^ 2
              / (2 * (1 + (histPullCount b hst : ℝ))))) := by
  unfold pairMixtureWeight expWeightVec
  have hrw : ∀ p : ℝ × ℝ, ENNReal.ofReal (stdGaussianPDF₂ p)
      * ENNReal.ofReal (Real.exp (vecExponent μvec (pairTilt a b p.1 p.2) hst))
      = ENNReal.ofReal (stdGaussianPDF₂ p
        * Real.exp ((p.1 * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a)
              - p.1 ^ 2 * (histPullCount a hst : ℝ) / 2)
            + (p.2 * (histRewardSum b hst - (histPullCount b hst : ℝ) * μvec b)
              - p.2 ^ 2 * (histPullCount b hst : ℝ) / 2))) := by
    intro p
    rw [← ENNReal.ofReal_mul (stdGaussianPDF₂_nonneg p),
      vecExponent_pairTilt μvec hab p.1 p.2 hst]
  simp only [hrw]
  exact lintegral_tilt_mixture₂ (Nat.cast_nonneg _) (Nat.cast_nonneg _) _ _

end BanditAlgorithm

/-!
# The Chernoff bound for a Gaussian bandit

Markov's inequality applied to the exponential martingale of `ExpMartingale`:
for every arm `a`, every `λ` and every round `n`,

  `P( λ (S_a(n) − T_a(n) μ_a) − λ² T_a(n)/2 ≥ x ) ≤ e^{−x}`.

This is the fixed-`λ` deviation bound; optimising over `λ` at a fixed pull count
gives the usual `exp(−T_a d²/2)` sub-Gaussian tail, and mixing over `λ` gives the
self-normalised, uniform-in-time bound that
`chernoff_pairwise_selfnormalised_deviation_bound` asks for.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The exponent of the bandit exponential martingale. -/
noncomputable def expExponent (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  lam * (trajRewardSum a n ω - (trajPullCount a n ω : ℝ) * μvec a)
    - lam ^ 2 * (trajPullCount a n ω : ℝ) / 2

theorem measurable_expWeight_traj (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ) :
    Measurable fun ω : ℕ → Fin k × ℝ ↦ expWeight μvec a lam (banditTrajPrefix k n ω) :=
  (measurable_expWeight μvec a lam n).comp measurable_banditTrajPrefix

theorem expWeight_prefix_eq (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expWeight μvec a lam (banditTrajPrefix k n ω)
      = ENNReal.ofReal (Real.exp (expExponent μvec a lam n ω)) := by
  unfold expWeight expExponent
  rw [histPullCount_prefix, histRewardSum_prefix]

/-- **The Chernoff bound.** -/
theorem bandit_chernoff_bound (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | x ≤ expExponent μvec a lam n ω}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure (gaussianBandit μvec) pol with hP
  set f : (ℕ → Fin k × ℝ) → ℝ≥0∞ := fun ω ↦ expWeight μvec a lam (banditTrajPrefix k n ω)
    with hf
  have hfmeas : Measurable f := measurable_expWeight_traj μvec a lam n
  have hint : ∫⁻ ω, f ω ∂P = 1 := lintegral_expWeight μvec pol a lam n
  -- the event is contained in a level set of `f`
  have hsub : {ω : ℕ → Fin k × ℝ | x ≤ expExponent μvec a lam n ω}
      ⊆ {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (Real.exp x) ≤ f ω} := by
    intro ω hω
    show ENNReal.ofReal (Real.exp x) ≤ expWeight μvec a lam (banditTrajPrefix k n ω)
    rw [expWeight_prefix_eq]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hω)
  refine le_trans (measure_mono hsub) ?_
  -- Markov
  have hne : ENNReal.ofReal (Real.exp x) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos x
  have htop : ENNReal.ofReal (Real.exp x) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmarkov := meas_ge_le_lintegral_div (μ := P) hfmeas.aemeasurable hne htop
  rw [hint] at hmarkov
  refine le_trans hmarkov (le_of_eq ?_)
  rw [one_div, ← ENNReal.ofReal_inv_of_pos (Real.exp_pos x), ← Real.exp_neg]

/-- The sub-Gaussian form: optimising the Chernoff bound is not needed for the
statement, but the bound at a fixed `λ` already gives the classical estimate. -/
theorem bandit_chernoff_bound' (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (lam : ℝ) (n : ℕ) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ |
          x + lam ^ 2 * (trajPullCount a n ω : ℝ) / 2
            ≤ lam * (trajRewardSum a n ω - (trajPullCount a n ω : ℝ) * μvec a)}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  refine le_trans (measure_mono ?_) (bandit_chernoff_bound μvec pol a lam n x)
  intro ω hω
  simp only [Set.mem_setOf_eq, expExponent] at hω ⊢
  linarith

end BanditAlgorithm

/-!
# The weighted-union Chernoff bound (discrete method of mixtures)

The fixed-`λ` bound of `BanditChernoff` is turned into a bound that holds
*simultaneously over a whole family of tilts* by paying `log(1/w_j)` for the
`j`-th one, where the weights `w_j` are any positive reals summing to at most `1`:

  `P( ∃ j, λ_j (S_a(n) − T_a(n)μ_a) − λ_j² T_a(n)/2 ≥ x + log(1/w_j) ) ≤ e^{−x}`.

This is the discrete form of the method of mixtures — the same device as
integrating the exponential martingale against a Gaussian prior on `λ`, but with
a countable prior, so that it needs nothing beyond a union bound.  Choosing the
`λ_j` to form a grid and optimising is exactly how one passes from the fixed-tilt
bound to the self-normalised statement that Chernoff's stopping rule requires.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- **The weighted union bound over a countable family of tilts.** -/
theorem bandit_chernoff_union (μvec : Fin k → ℝ) (pol : BanditPolicy k) (a : Fin k)
    (n : ℕ) (lams : ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) (hsum : Summable w)
    (hle : ∑' j, w j ≤ 1) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ j : ℕ,
          x + Real.log (1 / w j) ≤ expExponent μvec a (lams j) n ω}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  set P : Measure (ℕ → Fin k × ℝ) := banditTrajMeasure (gaussianBandit μvec) pol with hP
  -- the event is a countable union
  have hunion : {ω : ℕ → Fin k × ℝ | ∃ j : ℕ,
        x + Real.log (1 / w j) ≤ expExponent μvec a (lams j) n ω}
      = ⋃ j : ℕ, {ω : ℕ → Fin k × ℝ |
        x + Real.log (1 / w j) ≤ expExponent μvec a (lams j) n ω} := by
    ext ω; simp
  rw [hunion]
  refine le_trans (measure_iUnion_le _) ?_
  -- each term is bounded by `w j * e^{-x}`
  have hterm : ∀ j : ℕ, P {ω : ℕ → Fin k × ℝ |
      x + Real.log (1 / w j) ≤ expExponent μvec a (lams j) n ω}
      ≤ ENNReal.ofReal (Real.exp (-x) * w j) := by
    intro j
    refine le_trans (bandit_chernoff_bound μvec pol a (lams j) n (x + Real.log (1 / w j)))
      (le_of_eq ?_)
    congr 1
    rw [neg_add, Real.exp_add]
    congr 1
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log (hw j)]
  refine le_trans (ENNReal.tsum_le_tsum hterm) ?_
  -- and the weights sum to at most one
  have hrw : ∀ j : ℕ, ENNReal.ofReal (Real.exp (-x) * w j)
      = ENNReal.ofReal (Real.exp (-x)) * ENNReal.ofReal (w j) := fun j ↦
    ENNReal.ofReal_mul (Real.exp_pos _).le
  simp only [hrw]
  rw [ENNReal.tsum_mul_left]
  have hws : (∑' j : ℕ, ENNReal.ofReal (w j)) ≤ 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j ↦ (hw j).le) hsum]
    exact ENNReal.ofReal_le_one.mpr hle
  calc ENNReal.ofReal (Real.exp (-x)) * (∑' j : ℕ, ENNReal.ofReal (w j))
      ≤ ENNReal.ofReal (Real.exp (-x)) * 1 := by gcongr
    _ = ENNReal.ofReal (Real.exp (-x)) := mul_one _

/-- The same bound with the standard weights `w_j = 2^{-(j+1)}`, so that the price
of the `j`-th tilt is `(j+1) log 2`. -/
theorem bandit_chernoff_union_geometric (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (a : Fin k) (n : ℕ) (lams : ℕ → ℝ) (x : ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ j : ℕ,
          x + ((j : ℝ) + 1) * Real.log 2 ≤ expExponent μvec a (lams j) n ω}
      ≤ ENNReal.ofReal (Real.exp (-x)) := by
  have hw : ∀ j : ℕ, (0 : ℝ) < (1 / 2) ^ (j + 1) := fun j ↦ by positivity
  have hg : Summable fun j : ℕ ↦ (1 / 2 : ℝ) ^ j :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : Summable fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 1) := by
    refine (hg.mul_left (1 / 2 : ℝ)).congr fun j ↦ ?_
    ring
  have hle : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1)) ≤ 1 := by
    have : (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 1)) = 1 := by
      rw [show (fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 1)) = fun j : ℕ ↦ (1 / 2) * (1 / 2) ^ j by
        funext j; ring]
      rw [_root_.tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    exact le_of_eq this
  refine le_trans (measure_mono ?_)
    (bandit_chernoff_union μvec pol a n lams (fun j ↦ (1 / 2) ^ (j + 1)) hw hsum hle x)
  rintro ω ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have hlog : Real.log (1 / (1 / 2 : ℝ) ^ (j + 1)) = ((j : ℝ) + 1) * Real.log 2 := by
    rw [one_div, ← Real.rpow_natCast ((1 : ℝ) / 2) (j + 1)]
    rw [← Real.rpow_neg (by norm_num), Real.log_rpow (by norm_num)]
    push_cast
    rw [one_div, Real.log_inv]
    ring
  rw [hlog]
  exact hj

end BanditAlgorithm

/-!
# The self-normalised bound at a fixed pull count

Optimising the tilt of `BanditChernoff` for a *deterministic* pull count `m` gives

  `P( T_a(n) = m  ∧  Z_a(n)² ≥ 2 m β ) ≤ 2 e^{−β}`,

where `Z_a(n) = S_a(n) − T_a(n) μ_a`, i.e. `Z_a(n)²/(2 T_a(n)) = T_a(n)(μ̂_a − μ_a)²/2`
is exactly the self-normalised deviation appearing in Chernoff's stopping rule.

The tilt `λ = ±√(2β/m)` is the optimal one for the count `m`: it makes
`λ² T_a/2 = β` on the event, while `λ Z_a ≥ 2β`, so the exponent of the
martingale already exceeds `β`.  Summing this estimate over the possible values
of `T_a(n)` is the remaining step towards
`chernoff_pairwise_selfnormalised_deviation_bound`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The centred reward sum `Z_a(n) = S_a(n) − T_a(n) μ_a`. -/
noncomputable def centredSum (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  trajRewardSum a n ω - (trajPullCount a n ω : ℝ) * μvec a

theorem expExponent_eq (μvec : Fin k → ℝ) (a : Fin k) (lam : ℝ) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    expExponent μvec a lam n ω
      = lam * centredSum μvec a n ω - lam ^ 2 * (trajPullCount a n ω : ℝ) / 2 := rfl

/-- The key arithmetic: at the optimal tilt for the count `m`, the martingale
exponent is at least `β` on the one-sided deviation event. -/
theorem tilt_exponent_ge {m : ℕ} (hm : 0 < m) {β z : ℝ} (hβ : 0 < β)
    (hz : Real.sqrt (2 * (m : ℝ) * β) ≤ z) :
    β ≤ Real.sqrt (2 * β / (m : ℝ)) * z
      - Real.sqrt (2 * β / (m : ℝ)) ^ 2 * (m : ℝ) / 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlam : 0 ≤ Real.sqrt (2 * β / (m : ℝ)) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (2 * β / (m : ℝ)) ^ 2 = 2 * β / (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hprod : Real.sqrt (2 * β / (m : ℝ)) * Real.sqrt (2 * (m : ℝ) * β) = 2 * β := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show 2 * β / (m : ℝ) * (2 * (m : ℝ) * β) = (2 * β) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hmul : Real.sqrt (2 * β / (m : ℝ)) * Real.sqrt (2 * (m : ℝ) * β)
      ≤ Real.sqrt (2 * β / (m : ℝ)) * z := mul_le_mul_of_nonneg_left hz hlam
  rw [hprod] at hmul
  rw [hsq]
  have : 2 * β / (m : ℝ) * (m : ℝ) / 2 = β := by field_simp
  rw [this]
  linarith

/-- **The self-normalised deviation bound at a fixed pull count.** -/
theorem bandit_selfnormalised_fixed_count (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (a : Fin k) (n : ℕ) {m : ℕ} (hm : 0 < m) {β : ℝ} (hβ : 0 < β) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | trajPullCount a n ω = m ∧
          2 * (m : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2}
      ≤ 2 * ENNReal.ofReal (Real.exp (-β)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set lam : ℝ := Real.sqrt (2 * β / (m : ℝ)) with hlamdef
  set s : ℝ := Real.sqrt (2 * (m : ℝ) * β) with hsdef
  have hsplit : {ω : ℕ → Fin k × ℝ | trajPullCount a n ω = m ∧
        2 * (m : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2}
      ⊆ {ω : ℕ → Fin k × ℝ | β ≤ expExponent μvec a lam n ω}
        ∪ {ω : ℕ → Fin k × ℝ | β ≤ expExponent μvec a (-lam) n ω} := by
    rintro ω ⟨hT, hZ⟩
    have hTR : ((trajPullCount a n ω : ℕ) : ℝ) = (m : ℝ) := by rw [hT]
    have habs : s ≤ |centredSum μvec a n ω| := by
      rw [hsdef, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hZ
    rcases le_abs.mp habs with hpos | hneg
    · left
      show β ≤ expExponent μvec a lam n ω
      rw [expExponent_eq, hTR]
      exact tilt_exponent_ge hm hβ hpos
    · right
      show β ≤ expExponent μvec a (-lam) n ω
      rw [expExponent_eq, hTR]
      have h := tilt_exponent_ge (m := m) hm hβ (z := -centredSum μvec a n ω) hneg
      rw [← hlamdef] at h
      have hsq : (-lam) ^ 2 = lam ^ 2 := by ring
      rw [hsq]
      linarith
  refine le_trans (measure_mono hsplit) ?_
  refine le_trans (measure_union_le _ _) ?_
  have h1 := bandit_chernoff_bound μvec pol a lam n β
  have h2 := bandit_chernoff_bound μvec pol a (-lam) n β
  calc banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | β ≤ expExponent μvec a lam n ω}
      + banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | β ≤ expExponent μvec a (-lam) n ω}
      ≤ ENNReal.ofReal (Real.exp (-β)) + ENNReal.ofReal (Real.exp (-β)) := add_le_add h1 h2
    _ = 2 * ENNReal.ofReal (Real.exp (-β)) := by ring

/-! ## Summing over the possible pull counts -/

/-- **The self-normalised bound, uniform over the pull count.**  Note the
hypothesis `0 < T_a(n)`: when arm `a` has never been played both sides of the
deviation inequality vanish, so that case carries no information (and, in the
application, contributes nothing because the deviation `T_a(μ̂_a − μ_a)²/2` is
then `0 < β`). -/
theorem bandit_selfnormalised_union_counts (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    (a : Fin k) (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | 0 < trajPullCount a n ω ∧
          2 * (trajPullCount a n ω : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2}
      ≤ (n : ℝ≥0∞) * (2 * ENNReal.ofReal (Real.exp (-β))) := by
  classical
  have hsub : {ω : ℕ → Fin k × ℝ | 0 < trajPullCount a n ω ∧
        2 * (trajPullCount a n ω : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2}
      ⊆ ⋃ m ∈ Finset.Icc 1 n, {ω : ℕ → Fin k × ℝ | trajPullCount a n ω = m ∧
        2 * (m : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2} := by
    rintro ω ⟨hpos, hdev⟩
    simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_setOf_eq, exists_prop]
    exact ⟨trajPullCount a n ω,
      Finset.mem_Icc.mpr ⟨hpos, trajPullCount_le a n ω⟩, rfl, hdev⟩
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hterm : ∀ m ∈ Finset.Icc 1 n,
      banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | trajPullCount a n ω = m ∧
          2 * (m : ℝ) * β ≤ (centredSum μvec a n ω) ^ 2}
        ≤ 2 * ENNReal.ofReal (Real.exp (-β)) := by
    intro m hm
    exact bandit_selfnormalised_fixed_count μvec pol a n
      (Finset.mem_Icc.mp hm).1 hβ
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Nat.card_Icc]
  simp only [nsmul_eq_mul]
  have hcard : ((n + 1 - 1 : ℕ) : ℝ≥0∞) = (n : ℝ≥0∞) := by norm_num
  rw [hcard]

end BanditAlgorithm

/-!
# The time-uniform self-normalised deviation bound for a pair of arms

Applying Ville's inequality to the pair mixture martingale at the level `1/δ`
gives, for a *fixed* pair of distinct arms `a ≠ b` and an arbitrary sampling rule,

  `P( ∃ n,  Z_a(n)²/(2(1+T_a(n))) + Z_b(n)²/(2(1+T_b(n)))
             ≥ log(1/δ) + ½log(1+T_a(n)) + ½log(1+T_b(n)) )  ≤  δ`,

where `Z_i(n) = S_i(n) − T_i(n) μ_i`.

Two features distinguish this from the fixed-round Chernoff estimate of
`Solutions/BanditChernoff.lean` and the pull-count union of
`Solutions/SelfNormalised.lean`.  It is *uniform over all rounds at once* — there
is no union over `n`, so no factor growing with the horizon, which is what the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7
requires.  And it is uniform over the realised pull counts, which enter only
through the explicit `½log(1+T_i(n))` price — that is the "self-normalisation".

The cost of doing without a union is the shift `T_i ↦ 1 + T_i` in the
denominators, which is the exact trace left by the unit variance of the Gaussian
prior on the tilt.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The self-normalised exponent of a single arm at the mixture's scale:
`Z²/(2(1+T)) − ½log(1+T)`. -/
noncomputable def mixtureExponent (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  (centredSum μvec a n ω) ^ 2 / (2 * (1 + (trajPullCount a n ω : ℝ)))
    - Real.log (1 + (trajPullCount a n ω : ℝ)) / 2

/-- The one-arm factor of the pair mixture weight, in real form. -/
noncomputable def mixtureFactor (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  (Real.sqrt (1 + (trajPullCount a n ω : ℝ)))⁻¹
    * Real.exp ((centredSum μvec a n ω) ^ 2 / (2 * (1 + (trajPullCount a n ω : ℝ))))

theorem mixtureFactor_pos (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    0 < mixtureFactor μvec a n ω := by
  unfold mixtureFactor
  have h1 : (0 : ℝ) < 1 + (trajPullCount a n ω : ℝ) := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (1 + (trajPullCount a n ω : ℝ)) := Real.sqrt_pos.mpr h1
  positivity

/-- The factor is the exponential of the exponent: `w = e^{Z²/(2(1+T)) − ½log(1+T)}`. -/
theorem log_mixtureFactor (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    Real.log (mixtureFactor μvec a n ω) = mixtureExponent μvec a n ω := by
  unfold mixtureFactor mixtureExponent
  have h1 : (0 : ℝ) < 1 + (trajPullCount a n ω : ℝ) := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (1 + (trajPullCount a n ω : ℝ)) := Real.sqrt_pos.mpr h1
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt h1.le, Real.log_exp]
  ring

/-- The pair mixture weight evaluated along a trajectory. -/
theorem pairMixtureWeight_prefix (μvec : Fin k → ℝ) {a b : Fin k} (hab : a ≠ b) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    pairMixtureWeight μvec a b n (banditTrajPrefix k n ω)
      = ENNReal.ofReal (mixtureFactor μvec a n ω * mixtureFactor μvec b n ω) := by
  rw [pairMixtureWeight_eq μvec hab n (banditTrajPrefix k n ω),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold mixtureFactor centredSum
  rw [histPullCount_prefix, histPullCount_prefix, histRewardSum_prefix, histRewardSum_prefix]

/-- **The time-uniform self-normalised deviation bound for a fixed pair of arms.**
Ville's inequality applied to the pair mixture martingale. -/
theorem bandit_pair_selfnormalised_time_uniform (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    {a b : Fin k} (hab : a ≠ b) {δ : ℝ} (hδ : 0 < δ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
          Real.log (1 / δ)
            ≤ mixtureExponent μvec a n ω + mixtureExponent μvec b n ω}
      ≤ ENNReal.ofReal δ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (1 / δ) with hc
  -- the deviation event is contained in the crossing event of the mixture weight
  have hsub : {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
        Real.log (1 / δ) ≤ mixtureExponent μvec a n ω + mixtureExponent μvec b n ω}
      ⊆ crossedEver c (fun n ↦ pairMixtureWeight (k := k) μvec a b n) := by
    rintro ω ⟨n, hn⟩
    refine ⟨n, ?_⟩
    show c ≤ pairMixtureWeight μvec a b n (banditTrajPrefix k n ω)
    rw [pairMixtureWeight_prefix μvec hab n ω, hc]
    refine ENNReal.ofReal_le_ofReal ?_
    -- compare through logarithms: both sides are positive
    have hwa := mixtureFactor_pos μvec a n ω
    have hwb := mixtureFactor_pos μvec b n ω
    have hprod : 0 < mixtureFactor μvec a n ω * mixtureFactor μvec b n ω := mul_pos hwa hwb
    have hδ' : (0 : ℝ) < 1 / δ := by positivity
    rw [← Real.log_le_log_iff hδ' hprod, Real.log_mul hwa.ne' hwb.ne',
      log_mixtureFactor, log_mixtureFactor]
    exact hn
  -- and Ville's inequality bounds that crossing probability by `δ`
  refine le_trans (measure_mono hsub) ?_
  have hville := ville_inequality' (isTrajWeight_pairMixtureWeight μvec pol a b) c
  refine le_trans hville (le_of_eq ?_)
  rw [hc, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]

/-! ## The bound in explicit form

Unfolding `mixtureExponent` puts the estimate in the shape in which the
Track-and-Stop analysis consumes it: the self-normalised deviation of the pair
exceeds `log(1/δ)` plus the logarithmic price of the two pull counts. -/

theorem bandit_pair_selfnormalised_time_uniform' (μvec : Fin k → ℝ)
    (pol : BanditPolicy k) {a b : Fin k} (hab : a ≠ b) {δ : ℝ} (hδ : 0 < δ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
          Real.log (1 / δ)
              + Real.log (1 + (trajPullCount a n ω : ℝ)) / 2
              + Real.log (1 + (trajPullCount b n ω : ℝ)) / 2
            ≤ (centredSum μvec a n ω) ^ 2 / (2 * (1 + (trajPullCount a n ω : ℝ)))
              + (centredSum μvec b n ω) ^ 2 / (2 * (1 + (trajPullCount b n ω : ℝ)))}
      ≤ ENNReal.ofReal δ := by
  refine le_trans (measure_mono ?_)
    (bandit_pair_selfnormalised_time_uniform μvec pol hab hδ)
  rintro ω ⟨n, hn⟩
  refine ⟨n, ?_⟩
  unfold mixtureExponent
  linarith

end BanditAlgorithm

/-!
# The Gaussian mixture at an arbitrary prior variance

Mixing the exponential tilt `e^{λz − λ²t/2}` against a *unit*-variance Gaussian
prior on `λ` produces the weight `(1+t)^{−1/2} e^{z²/(2(1+t))}`, whose exponent is
the self-normalised deviation with `t` replaced by `1 + t`.  For the
Track-and-Stop analysis that replacement is not harmless: the deviation the
Chernoff stopping rule actually compares against its threshold is `z²/(2t)`, and
the ratio `t/(1+t)` is `1/2` at `t = 1`.

Widening the prior fixes this.  At variance `c` the mixture is

  `∫ φ_c(λ) e^{λz − λ²t/2} dλ = (1 + ct)^{−1/2} exp( c z²/(2(1+ct)) )`,

whose exponent is `z²/(2(t + 1/c))` — as close to `z²/(2t)` as one likes, at the
price of the prefactor `(1+ct)^{−1/2}` growing like `√c`.  That trade-off, with `c`
tuned to the confidence level `δ`, is the quantitative heart of Lemma 33.7: the
loss factor is `t/(t + 1/c) ≥ c/(c+1)`, and the price paid is `½log(1+ct)`.

Setting `c = 1` recovers `Solutions/GaussianMixture.lean`.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

/-- The centred Gaussian density of variance `c`. -/
noncomputable def scaledGaussianPDF (c : ℝ) (x : ℝ) : ℝ :=
  (Real.sqrt (2 * π * c))⁻¹ * Real.exp (-(x ^ 2) / (2 * c))

theorem scaledGaussianPDF_pos {c : ℝ} (hc : 0 < c) (x : ℝ) : 0 < scaledGaussianPDF c x := by
  unfold scaledGaussianPDF
  have h : (0 : ℝ) < Real.sqrt (2 * π * c) := Real.sqrt_pos.mpr (by positivity)
  positivity

theorem scaledGaussianPDF_nonneg {c : ℝ} (hc : 0 < c) (x : ℝ) :
    0 ≤ scaledGaussianPDF c x := (scaledGaussianPDF_pos hc x).le

theorem measurable_scaledGaussianPDF (c : ℝ) : Measurable (scaledGaussianPDF c) := by
  unfold scaledGaussianPDF
  fun_prop

/-- **The Gaussian mixture of an exponential tilt, at prior variance `c`.** -/
theorem integral_exp_tilt_mixture_scaled {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫ lam : ℝ, scaledGaussianPDF c lam * Real.exp (lam * z - lam ^ 2 * t / 2)
      = (Real.sqrt (1 + c * t))⁻¹ * Real.exp (c * z ^ 2 / (2 * (1 + c * t))) := by
  have hct : (0 : ℝ) < 1 + c * t := by positivity
  have ha : (0 : ℝ) < (1 + c * t) / (2 * c) := by positivity
  -- rewrite the integrand as a Gaussian with a linear term
  have hrw : (fun lam : ℝ ↦ scaledGaussianPDF c lam * Real.exp (lam * z - lam ^ 2 * t / 2))
      = fun lam : ℝ ↦ (Real.sqrt (2 * π * c))⁻¹ *
        Real.exp (-((1 + c * t) / (2 * c)) * lam ^ 2 + z * lam) := by
    funext lam
    unfold scaledGaussianPDF
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [hrw, integral_const_mul, integral_exp_quadratic ha z]
  -- the two constants
  have hsqrt : Real.sqrt (π / ((1 + c * t) / (2 * c)))
      = Real.sqrt (2 * π * c) * (Real.sqrt (1 + c * t))⁻¹ := by
    rw [show π / ((1 + c * t) / (2 * c)) = (2 * π * c) / (1 + c * t) by field_simp]
    rw [Real.sqrt_div' _ hct.le, div_eq_mul_inv]
  have hexp : z ^ 2 / (4 * ((1 + c * t) / (2 * c))) = c * z ^ 2 / (2 * (1 + c * t)) := by
    field_simp
    ring
  rw [hsqrt, hexp]
  have h2πc : Real.sqrt (2 * π * c) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (2 * π * c) := Real.sqrt_pos.mpr (by positivity)
    exact this.ne'
  field_simp

theorem integrable_tilt_mixture_scaled {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    Integrable (fun lam : ℝ ↦
      scaledGaussianPDF c lam * Real.exp (lam * z - lam ^ 2 * t / 2)) := by
  have ha : (0 : ℝ) < (1 + c * t) / (2 * c) := by positivity
  have hrw : (fun lam : ℝ ↦ scaledGaussianPDF c lam * Real.exp (lam * z - lam ^ 2 * t / 2))
      = fun lam : ℝ ↦ (Real.sqrt (2 * π * c))⁻¹ *
        Real.exp (-((1 + c * t) / (2 * c)) * lam ^ 2 + z * lam) := by
    funext lam
    unfold scaledGaussianPDF
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [hrw]
  exact (integrable_exp_quadratic ha z).const_mul _

/-- The scaled mixture in `ℝ≥0∞`. -/
theorem lintegral_tilt_mixture_scaled {c : ℝ} (hc : 0 < c) {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫⁻ lam : ℝ, ENNReal.ofReal
        (scaledGaussianPDF c lam * Real.exp (lam * z - lam ^ 2 * t / 2))
      = ENNReal.ofReal ((Real.sqrt (1 + c * t))⁻¹
          * Real.exp (c * z ^ 2 / (2 * (1 + c * t)))) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tilt_mixture_scaled hc ht z)
    (Filter.Eventually.of_forall fun lam ↦ by
      have := scaledGaussianPDF_nonneg hc lam
      positivity)]
  rw [integral_exp_tilt_mixture_scaled hc ht z]

/-! ## The scaled mixture of a pair of tilts -/

/-- The centred Gaussian density of variance `c` on the plane. -/
noncomputable def scaledGaussianPDF₂ (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  scaledGaussianPDF c p.1 * scaledGaussianPDF c p.2

theorem scaledGaussianPDF₂_pos {c : ℝ} (hc : 0 < c) (p : ℝ × ℝ) :
    0 < scaledGaussianPDF₂ c p :=
  mul_pos (scaledGaussianPDF_pos hc _) (scaledGaussianPDF_pos hc _)

theorem scaledGaussianPDF₂_nonneg {c : ℝ} (hc : 0 < c) (p : ℝ × ℝ) :
    0 ≤ scaledGaussianPDF₂ c p := (scaledGaussianPDF₂_pos hc p).le

theorem measurable_scaledGaussianPDF₂ (c : ℝ) : Measurable (scaledGaussianPDF₂ c) :=
  ((measurable_scaledGaussianPDF c).comp measurable_fst).mul
    ((measurable_scaledGaussianPDF c).comp measurable_snd)

/-- **The planar Gaussian mixture of a pair of exponential tilts, at variance `c`.** -/
theorem lintegral_tilt_mixture₂_scaled {c : ℝ} (hc : 0 < c) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) (y z : ℝ) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (scaledGaussianPDF₂ c p
        * Real.exp ((p.1 * y - p.1 ^ 2 * s / 2) + (p.2 * z - p.2 ^ 2 * t / 2)))
      = ENNReal.ofReal ((Real.sqrt (1 + c * s))⁻¹
            * Real.exp (c * y ^ 2 / (2 * (1 + c * s))))
        * ENNReal.ofReal ((Real.sqrt (1 + c * t))⁻¹
            * Real.exp (c * z ^ 2 / (2 * (1 + c * t)))) := by
  have hfac : ∀ p : ℝ × ℝ, ENNReal.ofReal (scaledGaussianPDF₂ c p
      * Real.exp ((p.1 * y - p.1 ^ 2 * s / 2) + (p.2 * z - p.2 ^ 2 * t / 2)))
      = ENNReal.ofReal (scaledGaussianPDF c p.1 * Real.exp (p.1 * y - p.1 ^ 2 * s / 2))
        * ENNReal.ofReal (scaledGaussianPDF c p.2 * Real.exp (p.2 * z - p.2 ^ 2 * t / 2)) := by
    intro p
    rw [← ENNReal.ofReal_mul (by
      have := scaledGaussianPDF_nonneg hc p.1
      positivity)]
    congr 1
    unfold scaledGaussianPDF₂
    rw [Real.exp_add]
    ring
  simp only [hfac]
  rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.lintegral_prod _ (by
    refine Measurable.aemeasurable ?_
    exact (ENNReal.measurable_ofReal.comp
        (((measurable_scaledGaussianPDF c).comp measurable_fst).mul
          (Measurable.exp (by fun_prop)))).mul
      (ENNReal.measurable_ofReal.comp
        (((measurable_scaledGaussianPDF c).comp measurable_snd).mul
          (Measurable.exp (by fun_prop)))))]
  have hinner : ∀ x : ℝ,
      ∫⁻ w : ℝ, ENNReal.ofReal (scaledGaussianPDF c x * Real.exp (x * y - x ^ 2 * s / 2))
          * ENNReal.ofReal (scaledGaussianPDF c w * Real.exp (w * z - w ^ 2 * t / 2))
        = ENNReal.ofReal (scaledGaussianPDF c x * Real.exp (x * y - x ^ 2 * s / 2))
          * ENNReal.ofReal ((Real.sqrt (1 + c * t))⁻¹
              * Real.exp (c * z ^ 2 / (2 * (1 + c * t)))) := by
    intro x
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tilt_mixture_scaled hc ht z]
  simp only [hinner]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_tilt_mixture_scaled hc hs y]

/-- The scaled Gaussian density of the plane is a probability density. -/
theorem lintegral_scaledGaussianPDF₂ {c : ℝ} (hc : 0 < c) :
    ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (scaledGaussianPDF₂ c p) = 1 := by
  have h := lintegral_tilt_mixture₂_scaled hc (s := 0) (t := 0) le_rfl le_rfl 0 0
  simp only [mul_zero, sub_zero, zero_div, add_zero, Real.exp_zero, mul_one,
    Real.sqrt_one, inv_one, one_mul, zero_mul, ENNReal.ofReal_one] at h
  simpa using h

end BanditAlgorithm

/-!
# The pair mixture martingale at an arbitrary prior variance

The unit-variance pair mixture of `Solutions/PairMixture.lean` controls the
statistic `Z_i²/(2(1+T_i))`, whereas Chernoff's stopping rule compares its
threshold against `Z_i²/(2T_i)`.  Widening the prior to variance `c` replaces the
shift `1 + T_i` by `T_i + 1/c`, giving the weight

  `M_n^{(c)} = ∏_{i ∈ {a,b}} (1 + c T_i(n))^{−1/2} exp( c Z_i(n)²/(2(1+c T_i(n))) )`,

whose exponent is `Z_i²/(2(T_i + 1/c))`.  Ville's inequality then yields, for every
`c > 0`,

  `P( ∃ n,  Σ_{i∈{a,b}} Z_i²/(2(T_i + 1/c))
             ≥ log(1/δ) + ½ Σ_{i∈{a,b}} log(1 + c T_i) )  ≤  δ`.

Sending `c → ∞` recovers the true statistic `Z_i²/(2T_i)` in the exponent, at the
price of the `½log(1 + cT_i)` terms growing like `½log c`.  That trade-off — and
the resulting loss factor `T/(T + 1/c) ≥ c/(c+1)` on the exponent, isolated below
as `selfnormalised_scale_loss` — is the quantitative mechanism behind the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7:
tuning `c` to `δ` is what converts the mixture bound into that threshold.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## The weight -/

/-- The pair mixture weight at prior variance `c`. -/
noncomputable def pairMixtureWeightScaled (μvec : Fin k → ℝ) (c : ℝ) (a b : Fin k) (n : ℕ)
    (hst : BanditHistory k n) : ℝ≥0∞ :=
  ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (scaledGaussianPDF₂ c p)
    * expWeightVec μvec (pairTilt a b p.1 p.2) hst

/-- **The scaled pair mixture weight is a bandit martingale.** -/
theorem isTrajWeight_pairMixtureWeightScaled (μvec : Fin k → ℝ) (pol : BanditPolicy k)
    {c : ℝ} (hc : 0 < c) (a b : Fin k) :
    IsTrajWeight (banditTrajMeasure (gaussianBandit μvec) pol)
      (fun n ↦ pairMixtureWeightScaled (k := k) μvec c a b n) :=
  isTrajWeight_mixture (k := k) (ι := ℝ × ℝ) (volume : Measure (ℝ × ℝ))
    (P := banditTrajMeasure (gaussianBandit μvec) pol)
    (fun p ↦ ENNReal.ofReal (scaledGaussianPDF₂ c p))
    (ENNReal.measurable_ofReal.comp (measurable_scaledGaussianPDF₂ c))
    (lintegral_scaledGaussianPDF₂ hc)
    (fun p n hst ↦ expWeightVec μvec (pairTilt a b p.1 p.2) hst)
    (fun n ↦ measurable_pairMixture_integrand μvec a b n)
    (fun p ↦ isTrajWeight_expWeightVec μvec pol (pairTilt a b p.1 p.2))

/-- **The closed form of the scaled pair mixture weight.** -/
theorem pairMixtureWeightScaled_eq (μvec : Fin k → ℝ) {c : ℝ} (hc : 0 < c)
    {a b : Fin k} (hab : a ≠ b) (n : ℕ) (hst : BanditHistory k n) :
    pairMixtureWeightScaled μvec c a b n hst
      = ENNReal.ofReal ((Real.sqrt (1 + c * (histPullCount a hst : ℝ)))⁻¹
          * Real.exp (c * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a) ^ 2
              / (2 * (1 + c * (histPullCount a hst : ℝ)))))
        * ENNReal.ofReal ((Real.sqrt (1 + c * (histPullCount b hst : ℝ)))⁻¹
          * Real.exp (c * (histRewardSum b hst - (histPullCount b hst : ℝ) * μvec b) ^ 2
              / (2 * (1 + c * (histPullCount b hst : ℝ))))) := by
  unfold pairMixtureWeightScaled expWeightVec
  have hrw : ∀ p : ℝ × ℝ, ENNReal.ofReal (scaledGaussianPDF₂ c p)
      * ENNReal.ofReal (Real.exp (vecExponent μvec (pairTilt a b p.1 p.2) hst))
      = ENNReal.ofReal (scaledGaussianPDF₂ c p
        * Real.exp ((p.1 * (histRewardSum a hst - (histPullCount a hst : ℝ) * μvec a)
              - p.1 ^ 2 * (histPullCount a hst : ℝ) / 2)
            + (p.2 * (histRewardSum b hst - (histPullCount b hst : ℝ) * μvec b)
              - p.2 ^ 2 * (histPullCount b hst : ℝ) / 2))) := by
    intro p
    rw [← ENNReal.ofReal_mul (scaledGaussianPDF₂_nonneg hc p),
      vecExponent_pairTilt μvec hab p.1 p.2 hst]
  simp only [hrw]
  exact lintegral_tilt_mixture₂_scaled hc (Nat.cast_nonneg _) (Nat.cast_nonneg _) _ _

/-! ## The exponent and the deviation bound -/

/-- The scaled self-normalised exponent of a single arm:
`c Z²/(2(1+cT)) − ½log(1+cT)`. -/
noncomputable def scaledMixtureExponent (μvec : Fin k → ℝ) (c : ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  c * (centredSum μvec a n ω) ^ 2 / (2 * (1 + c * (trajPullCount a n ω : ℝ)))
    - Real.log (1 + c * (trajPullCount a n ω : ℝ)) / 2

/-- The one-arm factor of the scaled pair mixture weight. -/
noncomputable def scaledMixtureFactor (μvec : Fin k → ℝ) (c : ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) : ℝ :=
  (Real.sqrt (1 + c * (trajPullCount a n ω : ℝ)))⁻¹
    * Real.exp (c * (centredSum μvec a n ω) ^ 2
        / (2 * (1 + c * (trajPullCount a n ω : ℝ))))

theorem scaledMixtureFactor_pos (μvec : Fin k → ℝ) {c : ℝ} (hc : 0 < c) (a : Fin k)
    (n : ℕ) (ω : ℕ → Fin k × ℝ) : 0 < scaledMixtureFactor μvec c a n ω := by
  unfold scaledMixtureFactor
  have h1 : (0 : ℝ) < 1 + c * (trajPullCount a n ω : ℝ) := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (1 + c * (trajPullCount a n ω : ℝ)) := Real.sqrt_pos.mpr h1
  positivity

theorem log_scaledMixtureFactor (μvec : Fin k → ℝ) {c : ℝ} (hc : 0 < c) (a : Fin k)
    (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    Real.log (scaledMixtureFactor μvec c a n ω) = scaledMixtureExponent μvec c a n ω := by
  unfold scaledMixtureFactor scaledMixtureExponent
  have h1 : (0 : ℝ) < 1 + c * (trajPullCount a n ω : ℝ) := by positivity
  have h2 : (0 : ℝ) < Real.sqrt (1 + c * (trajPullCount a n ω : ℝ)) := Real.sqrt_pos.mpr h1
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_inv,
    Real.log_sqrt h1.le, Real.log_exp]
  ring

theorem pairMixtureWeightScaled_prefix (μvec : Fin k → ℝ) {c : ℝ} (hc : 0 < c)
    {a b : Fin k} (hab : a ≠ b) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    pairMixtureWeightScaled μvec c a b n (banditTrajPrefix k n ω)
      = ENNReal.ofReal (scaledMixtureFactor μvec c a n ω
          * scaledMixtureFactor μvec c b n ω) := by
  rw [pairMixtureWeightScaled_eq μvec hc hab n (banditTrajPrefix k n ω),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold scaledMixtureFactor centredSum
  rw [histPullCount_prefix, histPullCount_prefix, histRewardSum_prefix, histRewardSum_prefix]

/-- **The time-uniform self-normalised deviation bound at prior variance `c`.** -/
theorem bandit_pair_selfnormalised_time_uniform_scaled (μvec : Fin k → ℝ)
    (pol : BanditPolicy k) {c : ℝ} (hc : 0 < c) {a b : Fin k} (hab : a ≠ b)
    {δ : ℝ} (hδ : 0 < δ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
          Real.log (1 / δ)
            ≤ scaledMixtureExponent μvec c a n ω + scaledMixtureExponent μvec c b n ω}
      ≤ ENNReal.ofReal δ := by
  set lvl : ℝ≥0∞ := ENNReal.ofReal (1 / δ) with hlvl
  have hsub : {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
        Real.log (1 / δ)
          ≤ scaledMixtureExponent μvec c a n ω + scaledMixtureExponent μvec c b n ω}
      ⊆ crossedEver lvl (fun n ↦ pairMixtureWeightScaled (k := k) μvec c a b n) := by
    rintro ω ⟨n, hn⟩
    refine ⟨n, ?_⟩
    show lvl ≤ pairMixtureWeightScaled μvec c a b n (banditTrajPrefix k n ω)
    rw [pairMixtureWeightScaled_prefix μvec hc hab n ω, hlvl]
    refine ENNReal.ofReal_le_ofReal ?_
    have hwa := scaledMixtureFactor_pos μvec hc a n ω
    have hwb := scaledMixtureFactor_pos μvec hc b n ω
    have hδ' : (0 : ℝ) < 1 / δ := by positivity
    rw [← Real.log_le_log_iff hδ' (mul_pos hwa hwb), Real.log_mul hwa.ne' hwb.ne',
      log_scaledMixtureFactor μvec hc, log_scaledMixtureFactor μvec hc]
    exact hn
  refine le_trans (measure_mono hsub) ?_
  refine le_trans (ville_inequality' (isTrajWeight_pairMixtureWeightScaled μvec pol hc a b) lvl)
    (le_of_eq ?_)
  rw [hlvl, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]

/-! ## The scale loss

The exponent controlled by the mixture is `c z²/(2(1+cT)) = z²/(2(T + 1/c))`, while
the statistic of Chernoff's stopping rule is `z²/(2T)`.  On the event that the arm
has been played at least once the two differ by at most the factor `c/(c+1)`, and
that factor is the only loss the mixture argument incurs. -/

theorem selfnormalised_scale_loss {c T z : ℝ} (hc : 0 < c) (hT : 1 ≤ T) :
    c / (c + 1) * (z ^ 2 / (2 * T)) ≤ c * z ^ 2 / (2 * (1 + c * T)) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hc1 : (0 : ℝ) < c + 1 := by linarith
  have hden : (0 : ℝ) < 2 * (1 + c * T) := by positivity
  have hd : 2 * (1 + c * T) ≤ (c + 1) * (2 * T) := by nlinarith
  have hnum : (0 : ℝ) ≤ c * z ^ 2 := by positivity
  calc c / (c + 1) * (z ^ 2 / (2 * T)) = c * z ^ 2 / ((c + 1) * (2 * T)) := by
        field_simp
    _ ≤ c * z ^ 2 / (2 * (1 + c * T)) := by gcongr

/-- The scale loss, covering the degenerate case of an arm never played: there
`T = 0`, the statistic `z²/(2T)` is `0` by Lean's division convention, and the
inequality is trivial. -/
theorem selfnormalised_scale_loss_zero_or_one {c T z : ℝ} (hc : 0 < c)
    (hT : T = 0 ∨ 1 ≤ T) :
    c / (c + 1) * (z ^ 2 / (2 * T)) ≤ c * z ^ 2 / (2 * (1 + c * T)) := by
  rcases hT with h0 | h1
  · subst h0
    have hl : z ^ 2 / (2 * (0 : ℝ)) = 0 := by norm_num
    have hr : c * z ^ 2 / (2 * (1 + c * (0 : ℝ))) = c * z ^ 2 / 2 := by norm_num
    rw [hl, hr, mul_zero]
    positivity
  · exact selfnormalised_scale_loss hc h1

/-- The scale loss, in the form the deviation bound consumes: the *pair* exponent
is at least `c/(c+1)` times the pair self-normalised statistic. -/
theorem selfnormalised_scale_loss_pair {c Ta Tb za zb : ℝ} (hc : 0 < c)
    (hTa : 1 ≤ Ta) (hTb : 1 ≤ Tb) :
    c / (c + 1) * (za ^ 2 / (2 * Ta) + zb ^ 2 / (2 * Tb))
      ≤ c * za ^ 2 / (2 * (1 + c * Ta)) + c * zb ^ 2 / (2 * (1 + c * Tb)) := by
  have ha := selfnormalised_scale_loss (c := c) (T := Ta) (z := za) hc hTa
  have hb := selfnormalised_scale_loss (c := c) (T := Tb) (z := zb) hc hTb
  have hrw : c / (c + 1) * (za ^ 2 / (2 * Ta) + zb ^ 2 / (2 * Tb))
      = c / (c + 1) * (za ^ 2 / (2 * Ta)) + c / (c + 1) * (zb ^ 2 / (2 * Tb)) := by ring
  rw [hrw]
  exact add_le_add ha hb

end BanditAlgorithm

/-!
# Measurability of the Track-and-Stop trajectory statistics

Everything Algorithm 21 computes at the end of round `t` is a function of the
first `t` rounds, hence `banditFiltration k t`-measurable.  This file proves that,
for each statistic of `Def_TrackAndStop`, and deduces the two structural clauses
of L&S Lemma 33.7:

* `isBanditStoppingTime_chernoffStoppingTime` — Chernoff's rule really is a
  stopping time of the natural filtration;
* `measurable_chernoffRecommendation` — the recommended arm is measurable with
  respect to the stopping-time σ-algebra `𝓕_τ`.

The only delicate point is that `trajEmpiricalBestArm` is defined through
`Finset.exists_max_image`, i.e. through `Classical.choose`, which carries no
measurability whatsoever.  It is handled in §3: we introduce the *canonical*
(least-index) maximiser `trajArgmax`, which is manifestly measurable, and show
that `trajGLR` — the only consumer of `trajEmpiricalBestArm` — is unchanged when
the canonical maximiser is substituted.  The proof splits on whether the maximum
is attained twice: if it is, both versions of `trajGLR` vanish (the pair term for
the two tied maximisers is `0`), and if it is not, the two maximisers coincide.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Generic comap measurability -/

/-- `Nat.cast : ℕ → ℝ` is measurable (source σ-algebra is `⊤`). -/
theorem measurable_natCast_real : Measurable (fun n : ℕ ↦ (n : ℝ)) :=
  measurable_from_top


/-- A function that factors through `g` is measurable for the σ-algebra `g`
pulls back. -/
theorem measurable_comap_comp {α β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {g : α → β} {f : β → γ} (hf : Measurable f) :
    Measurable[MeasurableSpace.comap g inferInstance] (fun a ↦ f (g a)) :=
  fun _ hs ↦ ⟨f ⁻¹' _, hf hs, rfl⟩

/-- The coordinate `ω s` is `𝓕_t`-measurable as soon as round `s` is among the
first `t`. -/
theorem measurable_trajCoord {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ ω s) := by
  have : (fun ω : ℕ → Fin k × ℝ ↦ ω s) =
      (fun h : BanditHistory k t ↦ h ⟨s, hs⟩) ∘ banditTrajPrefix k t := rfl
  rw [this]
  exact measurable_comap_comp (measurable_pi_apply _)

/-- The arm played in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajArm {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).1) :=
  measurable_fst.comp (measurable_trajCoord hs)

/-- The reward observed in round `s` is `𝓕_t`-measurable for `s < t`. -/
theorem measurable_trajReward {t s : ℕ} (hs : s < t) :
    Measurable[banditFiltration k t] (fun ω : ℕ → Fin k × ℝ ↦ (ω s).2) :=
  measurable_snd.comp (measurable_trajCoord hs)

/-! ## 2. The elementary statistics -/

/-- `T_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajPullCount (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPullCount i t) := by
  classical
  -- the count is a finite sum of indicators of `𝓕_t`-measurable events
  have hrw : trajPullCount i t =
      fun ω : ℕ → Fin k × ℝ ↦ ∑ s ∈ Finset.range t, if (ω s).1 = i then 1 else 0 := by
    funext ω
    rw [trajPullCount, Finset.card_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurable_trajArm hs') (measurableSet_singleton i)

/-- The running sum of the rewards collected from arm `i` is `𝓕_t`-measurable. -/
theorem measurable_trajRewardSum (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) := by
  classical
  have hrw : (fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) =
      fun ω : ℕ → Fin k × ℝ ↦
        ∑ s ∈ Finset.range t, if (ω s).1 = i then (ω s).2 else 0 := by
    funext ω
    rw [Finset.sum_filter]
  rw [hrw]
  refine Finset.measurable_sum _ fun s hs ↦ ?_
  have hs' : s < t := Finset.mem_range.mp hs
  exact Measurable.ite ((measurable_trajArm hs') (measurableSet_singleton i))
    (measurable_trajReward hs') measurable_const

/-- `μ̂_i(t)` is `𝓕_t`-measurable. -/
theorem measurable_trajEmpiricalMean (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajEmpiricalMean i t) := by
  have hrw : trajEmpiricalMean i t = fun ω : ℕ → Fin k × ℝ ↦
      (∑ s ∈ (Finset.range t).filter fun s ↦ (ω s).1 = i, (ω s).2) /
        ((trajPullCount i t ω : ℕ) : ℝ) := rfl
  rw [hrw]
  exact (measurable_trajRewardSum i t).div
    (measurable_natCast_real.comp (measurable_trajPullCount i t))

/-- `T_i(t)/t` is `𝓕_t`-measurable. -/
theorem measurable_trajAllocation (i : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajAllocation i t) := by
  have hrw : trajAllocation i t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount i t ω : ℕ) : ℝ) / (t : ℝ) := rfl
  rw [hrw]
  exact (measurable_natCast_real.comp (measurable_trajPullCount i t)).div measurable_const

/-- The pairwise GLR statistic is `𝓕_t`-measurable. -/
theorem measurable_trajPairGLR (a b : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajPairGLR a b t) := by
  have hrw : trajPairGLR a b t = fun ω : ℕ → Fin k × ℝ ↦
      ((trajPullCount a t ω : ℕ) : ℝ) * ((trajPullCount b t ω : ℕ) : ℝ) /
          (((trajPullCount a t ω : ℕ) : ℝ) + ((trajPullCount b t ω : ℕ) : ℝ)) *
        (trajEmpiricalMean a t ω - trajEmpiricalMean b t ω) ^ 2 / 2 := rfl
  rw [hrw]
  have hTa : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount a t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount a t)
  have hTb : Measurable[banditFiltration k t]
      (fun ω : ℕ → Fin k × ℝ ↦ ((trajPullCount b t ω : ℕ) : ℝ)) :=
    measurable_natCast_real.comp (measurable_trajPullCount b t)
  exact ((((hTa.mul hTb).div (hTa.add hTb)).mul
    (((measurable_trajEmpiricalMean a t).sub
      (measurable_trajEmpiricalMean b t)).pow_const 2)).div measurable_const)

/-! ## 3. The canonical maximiser and tie-independence of `Z_t` -/

section Argmax

variable [NeZero k]

/-- The *canonical* empirical best arm: the least index at which the empirical
mean is maximal.  Unlike `trajEmpiricalBestArm`, which is defined through
`Classical.choose`, this one is measurable. -/
noncomputable def trajArgmax (t : ℕ) (ω : ℕ → Fin k × ℝ) : Fin k :=
  ((Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω).min'
    (by
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
        (fun i ↦ trajEmpiricalMean i t ω) Finset.univ_nonempty
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j ↦ hi j (Finset.mem_univ j)⟩⟩)

theorem trajArgmax_mem_filter (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajArgmax t ω ∈ (Finset.univ : Finset (Fin k)).filter fun i ↦
      ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω :=
  Finset.min'_mem _ _

/-- `trajArgmax` is a maximiser. -/
theorem trajArgmax_spec (t : ℕ) (ω : ℕ → Fin k × ℝ) (j : Fin k) :
    trajEmpiricalMean j t ω ≤ trajEmpiricalMean (trajArgmax t ω) t ω :=
  (Finset.mem_filter.mp (trajArgmax_mem_filter t ω)).2 j

/-- `trajArgmax` is the *least* maximiser. -/
theorem trajArgmax_le (t : ℕ) (ω : ℕ → Fin k × ℝ) {i : Fin k}
    (hi : ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω) :
    trajArgmax t ω ≤ i :=
  Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

/-- The canonical maximiser is measurable: its level sets are cut out by finitely
many inequalities between the (measurable) empirical means. -/
theorem measurable_trajArgmax (t : ℕ) :
    Measurable[banditFiltration k t] (trajArgmax (k := k) t) := by
  classical
  have hle : ∀ a b : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | trajEmpiricalMean a t ω ≤ trajEmpiricalMean b t ω} := fun a b ↦
    measurableSet_le (measurable_trajEmpiricalMean a t) (measurable_trajEmpiricalMean b t)
  have hmax : ∀ i : Fin k, MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
    intro i
    have hrw : {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω}
        = ⋂ j : Fin k,
          {ω : ℕ → Fin k × ℝ | trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} := by
      ext ω; simp
    rw [hrw]
    exact MeasurableSet.iInter fun j ↦ hle j i
  refine @measurable_to_countable' (Fin k) _ _ _ (banditFiltration k t) _ fun i ↦ ?_
  have hset : (trajArgmax (k := k) t) ⁻¹' {i} =
      {ω : ℕ → Fin k × ℝ | ∀ j, trajEmpiricalMean j t ω ≤ trajEmpiricalMean i t ω} ∩
        ⋂ j ∈ {j : Fin k | j < i},
          {ω : ℕ → Fin k × ℝ | ∀ l, trajEmpiricalMean l t ω ≤ trajEmpiricalMean j t ω}ᶜ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor
    · rintro rfl
      refine ⟨trajArgmax_spec t ω, fun j hj hjmax ↦ ?_⟩
      exact absurd (trajArgmax_le t ω hjmax) (not_le.mpr hj)
    · rintro ⟨himax, hmin⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hmin _ h (trajArgmax_spec t ω)
      · exact absurd (trajArgmax_le t ω himax) (not_le.mpr h)
  rw [hset]
  refine (hmax i).inter (MeasurableSet.biInter (Set.to_countable _) fun j _ ↦ (hmax j).compl)

end Argmax

end BanditAlgorithm

/-!
# The GLR statistic `Z_t` is tie-independent, and measurable

`trajGLR` is written in terms of `trajEmpiricalBestArm`, which is produced by
`Classical.choose` and therefore carries no measurability.  This file shows that
`trajGLR` does not in fact depend on which maximiser is chosen — replacing
`trajEmpiricalBestArm` by the canonical least-index maximiser `trajArgmax` leaves
it unchanged — and concludes that `trajGLR t` is `banditFiltration k t`-measurable.

The mechanism is the same one L&S use in the proof of Lemma 33.7: if the
empirical maximum is attained twice then `Z_t = 0`, because the pair term for two
tied maximisers vanishes.  So the two candidate values of `Z_t` agree: either the
maximiser is unique, and then both formulas use the same arm, or it is not, and
then both formulas return `0`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. A generic "measurable finite case split" -/

/-- If `h` is a measurable map into a countable discrete space and each `G a` is
measurable, then so is `ω ↦ G (h ω) ω`. -/
theorem measurable_dep_of_countable {Ω γ ι : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace γ] [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    {h : Ω → ι} (hh : Measurable[m] h) {G : ι → Ω → γ} (hG : ∀ a, Measurable[m] (G a)) :
    Measurable[m] fun ω ↦ G (h ω) ω := by
  intro s hs
  have hrw : (fun ω ↦ G (h ω) ω) ⁻¹' s = ⋃ a : ι, (h ⁻¹' {a} ∩ (G a) ⁻¹' s) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    exact ⟨fun hω ↦ ⟨h ω, rfl, hω⟩, fun ⟨a, ha, hω⟩ ↦ by rw [← ha] at hω; exact hω⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun a ↦ (hh (measurableSet_singleton a)).inter (hG a hs)

/-! ## 2. Tie-independence -/

section Ties

variable [NeZero k]

/-- The GLR statistic computed at an arbitrary reference arm `a`. -/
noncomputable def trajGLRat (a : Fin k) (t : ℕ) (ω : ℕ → Fin k × ℝ) : ℝ≥0∞ :=
  ⨅ j ∈ {j : Fin k | j ≠ a}, ENNReal.ofReal (trajPairGLR a j t ω)

theorem trajGLR_eq_trajGLRat (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajEmpiricalBestArm t ω) t ω := rfl

/-- The pair term between two arms with equal empirical means vanishes. -/
theorem trajPairGLR_eq_zero_of_mean_eq {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (h : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajPairGLR a b t ω = 0 := by
  simp [trajPairGLR, h]

/-- If the empirical maximum is attained at two distinct arms, the GLR statistic
computed at either of them is `0`. -/
theorem trajGLRat_eq_zero_of_tie {a b : Fin k} {t : ℕ} {ω : ℕ → Fin k × ℝ}
    (hab : a ≠ b) (hmean : trajEmpiricalMean a t ω = trajEmpiricalMean b t ω) :
    trajGLRat a t ω = 0 := by
  refine le_antisymm ?_ bot_le
  refine le_trans (iInf_le_of_le b (iInf_le _ (Ne.symm hab))) (le_of_eq ?_)
  rw [trajPairGLR_eq_zero_of_mean_eq hmean, ENNReal.ofReal_zero]

/-- **Tie-independence.** `Z_t` is unchanged if the arbitrary maximiser produced by
`Classical.choose` is replaced by the canonical least-index maximiser. -/
theorem trajGLR_eq_at_argmax (t : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajGLR t ω = trajGLRat (trajArgmax t ω) t ω := by
  rw [trajGLR_eq_trajGLRat]
  by_cases h : trajEmpiricalBestArm t ω = trajArgmax t ω
  · rw [h]
  · -- both are maximisers, so their empirical means agree and both sides vanish
    have hmean : trajEmpiricalMean (trajEmpiricalBestArm t ω) t ω
        = trajEmpiricalMean (trajArgmax t ω) t ω :=
      le_antisymm (trajArgmax_spec t ω _) (trajEmpiricalBestArm_spec t ω _)
    rw [trajGLRat_eq_zero_of_tie h hmean, trajGLRat_eq_zero_of_tie (Ne.symm h) hmean.symm]

/-- If the empirical maximum is attained twice, `Z_t = 0`. -/
theorem trajGLR_eq_zero_of_not_unique (t : ℕ) (ω : ℕ → Fin k × ℝ) {b : Fin k}
    (hb : b ≠ trajArgmax t ω) (hmax : ∀ i, trajEmpiricalMean i t ω ≤ trajEmpiricalMean b t ω) :
    trajGLR t ω = 0 := by
  have hmean : trajEmpiricalMean (trajArgmax t ω) t ω = trajEmpiricalMean b t ω :=
    le_antisymm (hmax _) (trajArgmax_spec t ω b)
  rw [trajGLR_eq_at_argmax]
  exact trajGLRat_eq_zero_of_tie (Ne.symm hb) hmean

/-- **Uniqueness from a positive GLR.** If `Z_t ≠ 0` then the empirical maximiser
is unique, so the arbitrary choice made by `trajEmpiricalBestArm` agrees with the
canonical one. -/
theorem trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero (t : ℕ) (ω : ℕ → Fin k × ℝ)
    (h : trajGLR t ω ≠ 0) : trajEmpiricalBestArm t ω = trajArgmax t ω := by
  by_contra hne
  exact h (trajGLR_eq_zero_of_not_unique t ω hne (trajEmpiricalBestArm_spec t ω))

/-! ## 3. Measurability of `Z_t` -/

theorem measurable_trajGLRat (a : Fin k) (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLRat a t) := by
  have hrw : trajGLRat a t = fun ω ↦ ⨅ j ∈ {j : Fin k | j ≠ a},
      ENNReal.ofReal (trajPairGLR a j t ω) := rfl
  rw [hrw]
  refine Measurable.iInf fun j ↦ ?_
  refine Measurable.iInf fun _ ↦ ?_
  exact ENNReal.measurable_ofReal.comp (measurable_trajPairGLR a j t)

/-- `Z_t` is `𝓕_t`-measurable. -/
theorem measurable_trajGLR (t : ℕ) :
    Measurable[banditFiltration k t] (trajGLR (k := k) t) := by
  have hrw : trajGLR (k := k) t = fun ω ↦ trajGLRat (trajArgmax t ω) t ω := by
    funext ω; exact trajGLR_eq_at_argmax t ω
  rw [hrw]
  exact measurable_dep_of_countable (measurable_trajArgmax t) fun a ↦ measurable_trajGLRat a t

/-- The event "Chernoff's rule fires in round `t`" is `𝓕_t`-measurable. -/
theorem measurableSet_chernoffFires (δ : ℝ) (t : ℕ) :
    MeasurableSet[banditFiltration k t]
      {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ t) ≤ trajGLR t ω} :=
  measurableSet_le measurable_const (measurable_trajGLR t)

end Ties

end BanditAlgorithm

/-!
# Chernoff's stopping rule: threshold arithmetic and the stopping-time property

This file establishes the two *structural* clauses of L&S Lemma 33.7 — everything
about `τ_δ` and `ψ_δ` except the probability bound itself:

* `chernoffInverse_ge`, `chernoffThreshold_pos` — the threshold `β_t(δ)` is
  strictly positive.  This is what forces the empirical maximiser to be unique
  whenever the learner stops, which is in turn what makes the recommendation
  measurable at all (`chernoffRecommendation` is built from the `Classical.choose`
  maximiser `trajEmpiricalBestArm`).
* `isBanditStoppingTime_chernoffStoppingTime` — `τ_δ` is a stopping time of the
  natural filtration.
* `measurable_chernoffRecommendation` — `ψ_δ` is `𝓕_{τ_δ}`-measurable.

The positivity argument is the one implicit in L&S p. 410: `f⁻¹(δ)` is the least
`x ≥ k` with `f(x) ≤ δ`, so `f⁻¹(δ) ≥ k ≥ 1` as soon as that set is nonempty —
which it is, because `f(x) = e^{k-x}(x/k)^k → 0` as `x → ∞`.
-/

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. The Chernoff function and its inverse -/

/-- `f(k) = 1`. -/
theorem chernoffF_self (hk : 0 < k) : chernoffF k (k : ℝ) = 1 := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  simp [chernoffF, div_self hk']

/-- `f(x) = e^{k-x}(x/k)^k` tends to `0` as `x → ∞`. -/
theorem tendsto_chernoffF (hk : 0 < k) :
    Tendsto (chernoffF k) atTop (nhds 0) := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hrw : chernoffF k = fun x : ℝ ↦
      (Real.exp (k : ℝ) / ((k : ℝ) ^ k)) * (x ^ k * Real.exp (-x)) := by
    funext x
    rw [chernoffF, div_pow, sub_eq_add_neg, Real.exp_add]
    field_simp
  rw [hrw]
  simpa using tendsto_const_nhds.mul (tendsto_pow_mul_exp_neg_atTop_nhds_zero k)

/-- The set defining `f⁻¹(δ)` is nonempty for every `δ > 0`. -/
theorem chernoffInverse_set_nonempty (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}.Nonempty := by
  have h1 : ∀ᶠ x : ℝ in atTop, chernoffF k x ≤ δ :=
    (tendsto_chernoffF hk).eventually (eventually_le_nhds hδ)
  have h2 : ∀ᶠ x : ℝ in atTop, (k : ℝ) ≤ x := eventually_ge_atTop _
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  exact ⟨x, hx2, hx1⟩

theorem chernoffInverse_set_bddBelow {δ : ℝ} :
    BddBelow {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  ⟨(k : ℝ), fun _ hx ↦ hx.1⟩

/-- `f⁻¹(δ) ≥ k`. -/
theorem chernoffInverse_ge (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ :=
  le_csInf (chernoffInverse_set_nonempty hk hδ) fun _ hx ↦ hx.1

/-- `f⁻¹(δ) > 0`. -/
theorem chernoffInverse_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (chernoffInverse_ge hk hδ)

/-- The threshold `β_t(δ) = k log(t² + t) + f⁻¹(δ)` is strictly positive. -/
theorem chernoffThreshold_pos (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (t : ℕ) :
    0 < chernoffThreshold k δ t := by
  have hlog : 0 ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ)) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · norm_num
    · refine mul_nonneg (Nat.cast_nonneg k) (Real.log_nonneg ?_)
      have h1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
      nlinarith
  have hinv := chernoffInverse_pos hk hδ
  rw [chernoffThreshold]
  linarith

/-! ## 2. The stopping-time property -/

section Stop

variable [NeZero k]

/-- Unfolding of the stopping rule: the learner has stopped by round `n` exactly
when the firing condition has held at some round `m ≤ n`. -/
theorem chernoffStoppingTime_le_iff (δ : ℝ) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    chernoffStoppingTime (k := k) δ ω ≤ (n : ℕ∞) ↔
      ∃ m ≤ n, ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω := by
  constructor
  · intro hle
    by_contra hcon
    push_neg at hcon
    -- every element of the defining set exceeds `n`, hence is `≥ n + 1`
    have hlb : ((n : ℕ∞) + 1) ≤ chernoffStoppingTime (k := k) δ ω := by
      refine le_sInf ?_
      rintro t ⟨m, rfl, hm⟩
      have hmn : n < m := by
        by_contra h
        exact absurd hm (not_le.mpr (hcon m (not_lt.mp h)))
      have : ((n + 1 : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.succ_le_of_lt hmn
      simpa using this
    have hcontr : ((n + 1 : ℕ) : ℕ∞) ≤ ((n : ℕ) : ℕ∞) := by
      push_cast
      exact le_trans hlb hle
    exact absurd (by exact_mod_cast hcontr : n + 1 ≤ n) (Nat.not_succ_le_self n)
  · rintro ⟨m, hmn, hm⟩
    refine le_trans (sInf_le ⟨m, rfl, hm⟩) ?_
    exact_mod_cast hmn

/-- **Chernoff's rule is a stopping time.** -/
theorem isBanditStoppingTime_chernoffStoppingTime (δ : ℝ) :
    IsBanditStoppingTime (chernoffStoppingTime (k := k) δ) := by
  intro n
  show MeasurableSet[banditFiltration k n]
    {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)}
  have hrw : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        {ω : ℕ → Fin k × ℝ | ENNReal.ofReal (chernoffThreshold k δ m) ≤ trajGLR m ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
    exact chernoffStoppingTime_le_iff δ n ω
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact (banditFiltration k).mono hmn _ (measurableSet_chernoffFires δ m)

/-- `{τ_δ = m}` is `𝓕_m`-measurable. -/
theorem measurableSet_chernoffStoppingTime_eq (δ : ℝ) (m : ℕ) :
    MeasurableSet[banditFiltration k m]
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hset : {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} =
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((m : ℕ) : ℕ∞)} \
        ⋃ l ∈ Finset.range m,
          {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((l : ℕ) : ℕ∞)} := by
    ext ω
    simp only [Set.mem_diff, Set.mem_iUnion, Finset.mem_range, Set.mem_setOf_eq,
      exists_prop, not_exists, not_and]
    constructor
    · rintro h
      refine ⟨le_of_eq h, fun l hl hle ↦ ?_⟩
      rw [h] at hle
      exact absurd (by exact_mod_cast hle : m ≤ l) (not_le.mpr hl)
    · rintro ⟨hle, hlt⟩
      rcases lt_or_eq_of_le hle with h | h
      · exfalso
        obtain ⟨l, hl⟩ : ∃ l : ℕ, ((l : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
          ENat.ne_top_iff_exists.mp fun htop ↦ by
            rw [htop] at hle; exact absurd hle (by simp)
        rw [← hl] at h
        exact hlt l (by exact_mod_cast h) (le_of_eq hl.symm)
      · exact h
  rw [hset]
  refine MeasurableSet.diff (hτ m) ?_
  refine MeasurableSet.biUnion (Set.to_countable _) fun l hl ↦ ?_
  exact (banditFiltration k).mono (le_of_lt (Finset.mem_range.mp hl)) _ (hτ l)

/-- `τ_δ` is measurable for the ambient σ-algebra. -/
theorem measurable_chernoffStoppingTime (δ : ℝ) :
    Measurable (chernoffStoppingTime (k := k) δ) := by
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  refine @measurable_to_countable' ℕ∞ _ _ _ _ _ fun c ↦ ?_
  rcases eq_or_ne c ⊤ with rfl | hc
  · have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {(⊤ : ℕ∞)} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ |
          chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        Set.mem_setOf_eq, not_exists, not_le]
      constructor
      · intro h n; rw [h]; exact ENat.coe_lt_top n
      · intro h
        by_contra hne
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
        rw [← hn] at h
        exact absurd (h n) (lt_irrefl _)
    rw [hrw]
    exact (MeasurableSet.iUnion fun n ↦ (banditFiltration k).le n _ (hτ n)).compl
  · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hc
    have hrw : (chernoffStoppingTime (k := k) δ) ⁻¹' {((m : ℕ) : ℕ∞)} =
        {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} := rfl
    rw [hrw]
    exact (banditFiltration k).le m _ (measurableSet_chernoffStoppingTime_eq δ m)

/-! ## 3. Measurability of the recommendation -/

/-- If the learner stops in round `n`, the firing condition holds in round `n`
(it holds at some `m ≤ n` by definition, and `n` is the least such `m`). -/
theorem chernoffStoppingTime_fires {δ : ℝ} {n : ℕ} {ω : ℕ → Fin k × ℝ}
    (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω := by
  obtain ⟨m, hmn, hm⟩ := (chernoffStoppingTime_le_iff δ n ω).mp (le_of_eq hn)
  have hnm : ((n : ℕ) : ℕ∞) ≤ ((m : ℕ) : ℕ∞) := hn ▸ sInf_le ⟨m, rfl, hm⟩
  have hnm' : n = m := le_antisymm (by exact_mod_cast hnm) hmn
  exact hnm' ▸ hm

/-- On the event that the learner stops in round `n`, the empirical maximiser is
unique, so the recommendation is the canonical maximiser. -/
theorem chernoffRecommendation_eq_argmax (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} {ω : ℕ → Fin k × ℝ} (hn : chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)) :
    chernoffRecommendation (k := k) δ ω = trajArgmax n ω := by
  have hfire : ENNReal.ofReal (chernoffThreshold k δ n) ≤ trajGLR n ω :=
    chernoffStoppingTime_fires hn
  have hpos : trajGLR n ω ≠ 0 := by
    intro h0
    rw [h0, le_zero_iff, ENNReal.ofReal_eq_zero] at hfire
    exact absurd hfire (not_le.mpr (chernoffThreshold_pos hk hδ n))
  have hrec : chernoffRecommendation (k := k) δ ω = trajEmpiricalBestArm n ω := by
    rw [chernoffRecommendation, hn]
  rw [hrec, trajEmpiricalBestArm_eq_argmax_of_trajGLR_ne_zero n ω hpos]

omit [NeZero k] in
/-- `Exists.choose` depends only on the proposition, so a maximiser chosen from
equal data is the same arm. -/
theorem exists_max_image_choose_congr {f g : Fin k → ℝ} (h : f = g)
    (hf : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), f x' ≤ f x)
    (hg : ∃ x ∈ (Finset.univ : Finset (Fin k)),
      ∀ x' ∈ (Finset.univ : Finset (Fin k)), g x' ≤ g x) :
    hf.choose = hg.choose := by
  subst h; rfl

/-- Two trajectories with the same empirical means at time `t` produce the same
(arbitrarily chosen) empirical best arm. -/
theorem trajEmpiricalBestArm_congr {t t' : ℕ} {ω ω' : ℕ → Fin k × ℝ}
    (h : (fun i : Fin k ↦ trajEmpiricalMean i t ω)
      = fun i : Fin k ↦ trajEmpiricalMean i t' ω') :
    trajEmpiricalBestArm t ω = trajEmpiricalBestArm t' ω' :=
  exists_max_image_choose_congr h _ _

/-- At time `0` all empirical means are the junk value `0`, so the fallback
recommendation is a constant. -/
theorem trajEmpiricalBestArm_zero_const (ω ω' : ℕ → Fin k × ℝ) :
    trajEmpiricalBestArm (k := k) 0 ω = trajEmpiricalBestArm (k := k) 0 ω' := by
  refine trajEmpiricalBestArm_congr ?_
  funext i
  simp [trajEmpiricalMean, trajPullCount]

/-- The ambient product σ-algebra is generated by the natural filtration. -/
theorem pi_le_iSup_banditFiltration (k : ℕ) :
    (inferInstance : MeasurableSpace (ℕ → Fin k × ℝ)) ≤
      ⨆ t, (banditFiltration k t : MeasurableSpace _) := by
  refine iSup_le (ι := ℕ)
    (f := fun n : ℕ ↦ MeasurableSpace.comap (fun ω : ℕ → Fin k × ℝ ↦ ω n) inferInstance)
    fun n ↦ ?_
  refine le_trans ?_ (le_iSup (fun t ↦ (banditFiltration k t : MeasurableSpace _)) (n + 1))
  show MeasurableSpace.comap (fun ω : ℕ → Fin k × ℝ ↦ ω n) inferInstance ≤
    MeasurableSpace.comap (banditTrajPrefix k (n + 1)) inferInstance
  have h : (fun ω : ℕ → Fin k × ℝ ↦ ω n) =
      (fun h : BanditHistory k (n + 1) ↦ h (Fin.last n)) ∘ banditTrajPrefix k (n + 1) := rfl
  rw [h, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- **The recommendation is `𝓕_τ`-measurable.** -/
theorem measurable_chernoffRecommendation (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    Measurable[(isBanditStoppingTime_chernoffStoppingTime (k := k) δ).measurableSpace]
      (chernoffRecommendation (k := k) δ) := by
  classical
  have hτ := isBanditStoppingTime_chernoffStoppingTime (k := k) δ
  have hτm := measurable_chernoffStoppingTime (k := k) δ
  -- ambient measurability
  have hamb : Measurable (chernoffRecommendation (k := k) δ) := by
    refine @measurable_to_countable' (Fin k) _ _ _ _ _ fun a ↦ ?_
    have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {a} =
        (⋃ n : ℕ, {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((n : ℕ) : ℕ∞)} ∩
            {ω : ℕ → Fin k × ℝ | trajArgmax n ω = a}) ∪
          ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ⊤} ∩
            {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_iUnion,
        Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · intro hω
        rcases eq_or_ne (chernoffStoppingTime (k := k) δ ω) ⊤ with htop | hne
        · refine Or.inr ⟨htop, ?_⟩
          rw [← hω, chernoffRecommendation, htop]
          rfl
        · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
          exact Or.inl ⟨n, hn.symm, by rw [← hω, chernoffRecommendation_eq_argmax hk hδ hn.symm]⟩
      · rintro (⟨n, hn, ha⟩ | ⟨hn, ha⟩)
        · rw [chernoffRecommendation_eq_argmax hk hδ hn, ha]
        · rw [chernoffRecommendation, hn]
          exact ha
    rw [hrw]
    refine MeasurableSet.union (MeasurableSet.iUnion fun n ↦ ?_) ?_
    · exact (hτm (measurableSet_singleton _)).inter
        ((banditFiltration k).le n _ ((measurable_trajArgmax n) (measurableSet_singleton a)))
    · rcases isEmpty_or_nonempty (ℕ → Fin k × ℝ) with _ | ⟨⟨ω₀⟩⟩
      · exact Subsingleton.measurableSet
      · by_cases hval : trajEmpiricalBestArm (k := k) 0 ω₀ = a
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = Set.univ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_univ]
          exact hτm (measurableSet_singleton _)
        · have h : {ω : ℕ → Fin k × ℝ | trajEmpiricalBestArm (k := k) 0 ω = a} = ∅ := by
            ext ω; simp [trajEmpiricalBestArm_zero_const ω ω₀, hval]
          rw [h, Set.inter_empty]
          exact MeasurableSet.empty
  refine @measurable_to_countable' (Fin k) _ _ _ hτ.measurableSpace _ fun i ↦ ?_
  refine ⟨pi_le_iSup_banditFiltration k _ (hamb (measurableSet_singleton i)), fun n ↦ ?_⟩
  show MeasurableSet[banditFiltration k n]
    ((chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)})
  have hrw : (chernoffRecommendation (k := k) δ) ⁻¹' {i} ∩
      {ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω ≤ ((n : ℕ) : ℕ∞)} =
      ⋃ m ∈ Finset.range (n + 1),
        ({ω : ℕ → Fin k × ℝ | chernoffStoppingTime (k := k) δ ω = ((m : ℕ) : ℕ∞)} ∩
          {ω : ℕ → Fin k × ℝ | trajArgmax m ω = i}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
      Finset.mem_range, Nat.lt_succ_iff, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨hi, hle⟩
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m : ℕ) : ℕ∞) = chernoffStoppingTime (k := k) δ ω :=
        ENat.ne_top_iff_exists.mp fun htop ↦ by
          rw [htop] at hle; exact absurd hle (by simp)
      refine ⟨m, ?_, hm.symm, ?_⟩
      · rw [← hm] at hle; exact_mod_cast hle
      · rw [← hi, chernoffRecommendation_eq_argmax hk hδ hm.symm]
    · rintro ⟨m, hmn, hm, hi⟩
      refine ⟨by rw [chernoffRecommendation_eq_argmax hk hδ hm, hi], ?_⟩
      rw [hm]; exact_mod_cast hmn
  rw [hrw]
  refine MeasurableSet.biUnion (Set.to_countable _) fun m hm ↦ ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  exact ((banditFiltration k).mono hmn _ (measurableSet_chernoffStoppingTime_eq δ m)).inter
    ((banditFiltration k).mono hmn _ ((measurable_trajArgmax m) (measurableSet_singleton i)))

end Stop

end BanditAlgorithm

/-!
# The Chernoff inverse `f⁻¹(δ)`

`f(x) = e^{k−x}(x/k)^k` is continuous, equal to `1` at `x = k`, strictly
decreasing on `[k, ∞)`, and tends to `0`.  `chernoffInverse k δ` is defined as the
infimum of `{x ≥ k : f(x) ≤ δ}`, and this file proves the facts that make that
definition behave like an inverse:

* `chernoffF_chernoffInverse_le` — the infimum is attained, so `f(f⁻¹(δ)) ≤ δ`.
  This is what the soundness proof of L&S Lemma 33.7 actually consumes: the
  threshold really does deliver the promised confidence level.
* `chernoffInverse_le_of_le` — any admissible `x` bounds `f⁻¹(δ)` from above, so
  explicit thresholds can be plugged in.
* `chernoffInverse_antitone` — smaller confidence level, larger threshold.
* `chernoffF_antitoneOn` — `f` is decreasing on `[k, ∞)`, which is what makes
  `f⁻¹` an inverse rather than merely a lower bound.

Together with `chernoffThreshold_pos` these are all the properties of `β_t(δ)`
used anywhere in the Track-and-Stop analysis.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real Set

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## 1. Continuity and monotonicity of `f` -/

theorem continuous_chernoffF (k : ℕ) : Continuous (chernoffF k) := by
  unfold chernoffF
  fun_prop

/-- `f` is strictly decreasing on `[k, ∞)`: its logarithmic derivative is
`k/x − 1 < 0` there.  We prove the (equivalent, and sufficient) statement that
`f` is antitone on `[k, ∞)` directly from `log x ≤ x − 1`. -/
theorem chernoffF_le_chernoffF_of_le (hk : 0 < k) {x y : ℝ} (hx : (k : ℝ) ≤ x)
    (hxy : x ≤ y) : chernoffF k y ≤ chernoffF k x := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hkR hx
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx0 hxy
  -- compare logarithms
  have hlog : Real.log (chernoffF k y) ≤ Real.log (chernoffF k x) := by
    have hlx : Real.log (chernoffF k x)
        = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hx0.ne' hkR.ne']
    have hly : Real.log (chernoffF k y)
        = ((k : ℝ) - y) + k * (Real.log y - Real.log k) := by
      rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
        Real.log_pow, Real.log_div hy0.ne' hkR.ne']
    rw [hlx, hly]
    -- `k (log y − log x) ≤ y − x` because `log(y/x) ≤ y/x − 1` and `x ≥ k`
    have hratio : Real.log y - Real.log x ≤ y / x - 1 := by
      rw [← Real.log_div hy0.ne' hx0.ne']
      exact Real.log_le_sub_one_of_pos (by positivity)
    have hkx : (k : ℝ) * (y / x - 1) ≤ y - x := by
      have hyx : 0 ≤ y / x - 1 := by
        rw [sub_nonneg, le_div_iff₀ hx0]
        linarith
      calc (k : ℝ) * (y / x - 1) ≤ x * (y / x - 1) := by
            exact mul_le_mul_of_nonneg_right (le_trans hx (le_refl x)) hyx
        _ = y - x := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hratio (le_of_lt hkR)]
  have hposx : 0 < chernoffF k x := by
    rw [chernoffF]; positivity
  have hposy : 0 < chernoffF k y := by
    rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hposy hposx).mp hlog

/-! ## 2. The infimum is attained -/

theorem isClosed_chernoffInverse_set (k : ℕ) (δ : ℝ) :
    IsClosed {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} := by
  have h : {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ}
      = Set.Ici (k : ℝ) ∩ chernoffF k ⁻¹' Set.Iic δ := by
    ext x; simp [and_comm]
  rw [h]
  exact isClosed_Ici.inter (isClosed_Iic.preimage (continuous_chernoffF k))

/-- **The infimum defining `f⁻¹(δ)` is attained.** -/
theorem chernoffInverse_mem (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffInverse k δ ∈ {x : ℝ | (k : ℝ) ≤ x ∧ chernoffF k x ≤ δ} :=
  IsClosed.csInf_mem (isClosed_chernoffInverse_set k δ)
    (chernoffInverse_set_nonempty hk hδ) chernoffInverse_set_bddBelow

/-- **`f⁻¹(δ)` really is a threshold at confidence `δ`.** -/
theorem chernoffF_chernoffInverse_le (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    chernoffF k (chernoffInverse k δ) ≤ δ :=
  (chernoffInverse_mem hk hδ).2

/-- Above the threshold the Chernoff function stays below `δ`. -/
theorem chernoffF_le_of_chernoffInverse_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ)
    (hx : chernoffInverse k δ ≤ x) : chernoffF k x ≤ δ :=
  le_trans (chernoffF_le_chernoffF_of_le hk (chernoffInverse_mem hk hδ).1 hx)
    (chernoffF_chernoffInverse_le hk hδ)

/-! ## 3. Comparison -/

/-- Any admissible point bounds the threshold. -/
theorem chernoffInverse_le_of_le {δ x : ℝ} (hx : (k : ℝ) ≤ x) (hfx : chernoffF k x ≤ δ) :
    chernoffInverse k δ ≤ x :=
  csInf_le chernoffInverse_set_bddBelow ⟨hx, hfx⟩

/-- Smaller confidence level, larger threshold. -/
theorem chernoffInverse_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ') :
    chernoffInverse k δ' ≤ chernoffInverse k δ :=
  chernoffInverse_le_of_le (chernoffInverse_mem hk hδ).1
    (le_trans (chernoffF_chernoffInverse_le hk hδ) h)

/-- The threshold is `k` exactly at confidence level `1`, and at least `k`
always. -/
theorem chernoffInverse_one (hk : 0 < k) : chernoffInverse k 1 = (k : ℝ) :=
  le_antisymm (chernoffInverse_le_of_le le_rfl (le_of_eq (chernoffF_self hk)))
    (chernoffInverse_ge hk one_pos)

/-! ## 4. Monotonicity of the whole threshold -/

theorem chernoffThreshold_antitone (hk : 0 < k) {δ δ' : ℝ} (hδ : 0 < δ) (h : δ ≤ δ')
    (t : ℕ) : chernoffThreshold k δ' t ≤ chernoffThreshold k δ t := by
  unfold chernoffThreshold
  exact add_le_add_right (chernoffInverse_antitone hk hδ h) _

end BanditAlgorithm

/-!
# An explicit `O(log(1/δ))` bound on the Chernoff inverse

L&S use `f⁻¹(δ) = (1 + o(1)) log(1/δ)` to keep the leading constant of
Theorem 33.6 exact.  The `o(1)` is delicate, but the *order* is elementary and is
what every finiteness argument needs:

  `f⁻¹(δ) ≤ (k + log(1/δ)) / (1 − 1/e)`.

The proof is one application of `log y ≤ y/e` (itself `log(y/e) ≤ y/e − 1`):

  `log f(x) = (k − x) + k log(x/k) ≤ (k − x) + x/e = k − x(1 − 1/e)`,

so `f(x) ≤ δ` as soon as `x (1 − 1/e) ≥ k + log(1/δ)`; and any such `x` is
automatically `≥ k`, because `1 − 1/e < 1` and `log(1/δ) ≥ 0` for `δ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory NNReal ENNReal Filter Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `log y ≤ y / e`. -/
theorem log_le_div_exp_one {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (x := y / Real.exp 1)
    (div_pos hy (Real.exp_pos 1))
  rw [Real.log_div hy.ne' (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

/-- The explicit form of `log f(x)` for `x > 0`. -/
theorem log_chernoffF (hk : 0 < k) {x : ℝ} (hx : 0 < x) :
    Real.log (chernoffF k x) = ((k : ℝ) - x) + k * (Real.log x - Real.log k) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  rw [chernoffF, Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    Real.log_pow, Real.log_div hx.ne' hkR.ne']

/-- **The order bound.**  Every `x` with `x (1 − 1/e) ≥ k + log(1/δ)` is an
admissible threshold. -/
theorem chernoffF_le_of_le (hk : 0 < k) {δ x : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : (k : ℝ) + Real.log (1 / δ) ≤ x * (1 - (Real.exp 1)⁻¹)) :
    chernoffF k x ≤ δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  have hx0 : 0 < x := by
    by_contra hcon
    push_neg at hcon
    have : x * (1 - (Real.exp 1)⁻¹) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcon hfac.le
    linarith
  -- the key logarithmic estimate
  have hlog : Real.log (chernoffF k x) ≤ Real.log δ := by
    rw [log_chernoffF hk hx0]
    have hbound : (k : ℝ) * (Real.log x - Real.log k) ≤ x * (Real.exp 1)⁻¹ := by
      have h := log_le_div_exp_one (y := x / (k : ℝ)) (by positivity)
      rw [Real.log_div hx0.ne' hkR.ne'] at h
      calc (k : ℝ) * (Real.log x - Real.log k) ≤ (k : ℝ) * (x / (k : ℝ) / Real.exp 1) :=
            mul_le_mul_of_nonneg_left h hkR.le
        _ = x * (Real.exp 1)⁻¹ := by field_simp
    have hδlog : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    rw [hδlog] at hx
    nlinarith
  have hpos : 0 < chernoffF k x := by rw [chernoffF]; positivity
  exact (Real.log_le_log_iff hpos hδ).mp hlog

/-- **`f⁻¹(δ) = O(k + log(1/δ))`.** -/
theorem chernoffInverse_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    chernoffInverse k δ ≤ ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have he : (1 : ℝ) < Real.exp 1 := by
    simpa using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
  have hfac : (0 : ℝ) < 1 - (Real.exp 1)⁻¹ := by
    have : (Real.exp 1)⁻¹ < 1 := by
      rw [inv_lt_one_iff₀]; right; exact he
    linarith
  have hfac1 : 1 - (Real.exp 1)⁻¹ ≤ 1 := by
    have : (0 : ℝ) < (Real.exp 1)⁻¹ := by positivity
    linarith
  have hlogδ : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv_iff₀).mpr ⟨hδ, hδ1⟩)
  set x : ℝ := ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) with hxdef
  have hxk : (k : ℝ) ≤ x := by
    rw [hxdef, le_div_iff₀ hfac]
    nlinarith
  refine chernoffInverse_le_of_le hxk (chernoffF_le_of_le hk hδ hδ1 ?_)
  rw [hxdef, div_mul_cancel₀ _ (ne_of_gt hfac)]

/-- Consequently the whole threshold is `O(k log(t²+t) + k + log(1/δ))`. -/
theorem chernoffThreshold_le_explicit (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (t : ℕ) :
    chernoffThreshold k δ t
      ≤ (k : ℝ) * Real.log ((t : ℝ) ^ 2 + (t : ℝ))
        + ((k : ℝ) + Real.log (1 / δ)) / (1 - (Real.exp 1)⁻¹) := by
  rw [chernoffThreshold]
  exact add_le_add_right (chernoffInverse_le_explicit hk hδ hδ1) _

end BanditAlgorithm

/-!
# The sharp lower bound on the threshold constant

`Solutions/ChernoffInverseBound.lean` bounds `f⁻¹(δ)` from *above* by
`(k + log(1/δ))/(1 − e⁻¹)`, which is what shows the sample complexity of
Chernoff's rule is `O(log(1/δ))`.  Turning the mixture martingale into the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7 needs
the opposite estimate, and needs it sharp.

Taking logarithms in `f(f⁻¹(δ)) ≤ δ` — that is, in
`e^{k−f⁻¹(δ)}(f⁻¹(δ)/k)^k ≤ δ` — gives directly

  `f⁻¹(δ) ≥ k + log(1/δ) + k·log(f⁻¹(δ)/k)`.

Dropping the last term (nonnegative, since `f⁻¹(δ) ≥ k`) recovers the crude
`f⁻¹(δ) ≥ k + log(1/δ)`, but the last term is exactly what one cannot afford to
drop: it grows like `k log log(1/δ)`, and that is the slack which pays for the
`½log(1 + cT)` prices of the mixture at prior variance `c ≈ log(1/δ)/k`.  Without
it the mixture argument fails for small `δ`, no matter how the variance is tuned.
-/

open Real

namespace BanditAlgorithm

variable {k : ℕ}

/-- `f⁻¹(δ) ≥ k`, restated. -/
theorem le_chernoffInverse (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) ≤ chernoffInverse k δ := (chernoffInverse_mem hk hδ).1

theorem chernoffInverse_pos' (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    0 < chernoffInverse k δ :=
  lt_of_lt_of_le (by exact_mod_cast hk) (le_chernoffInverse hk hδ)

/-- **The sharp lower bound on the threshold constant.**  Taking logarithms in
`f(f⁻¹(δ)) ≤ δ`. -/
theorem chernoffInverse_ge_sharp (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (chernoffInverse k δ / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  set β := chernoffInverse k δ with hβ
  have hβpos : 0 < β := chernoffInverse_pos' hk hδ
  have hf : chernoffF k β ≤ δ := chernoffF_chernoffInverse_le hk hδ
  have hfpos : 0 < chernoffF k β := by
    unfold chernoffF
    have : (0 : ℝ) < β / (k : ℝ) := by positivity
    positivity
  -- take logarithms
  have hlog : Real.log (chernoffF k β) ≤ Real.log δ := Real.log_le_log hfpos hf
  rw [log_chernoffF hk hβpos] at hlog
  have hdiv : Real.log (β / (k : ℝ)) = Real.log β - Real.log (k : ℝ) :=
    Real.log_div hβpos.ne' hkR.ne'
  have hinv : Real.log (1 / δ) = -Real.log δ := by
    rw [one_div, Real.log_inv]
  rw [hdiv, hinv]
  linarith

/-- The crude consequence: `f⁻¹(δ) ≥ k + log(1/δ)`. -/
theorem chernoffInverse_ge_add_log (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ) ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hsharp := chernoffInverse_ge_sharp hk hδ
  have hge : (1 : ℝ) ≤ chernoffInverse k δ / (k : ℝ) :=
    (one_le_div hkR).mpr (le_chernoffInverse hk hδ)
  have hlog : 0 ≤ Real.log (chernoffInverse k δ / (k : ℝ)) := Real.log_nonneg hge
  nlinarith [mul_nonneg hkR.le hlog]

/-- The logarithmic slack, isolated: `f⁻¹(δ) − k − log(1/δ) ≥ k log(f⁻¹(δ)/k)`, and
`f⁻¹(δ)/k ≥ 1 + log(1/δ)/k`, so the slack is at least `k log(1 + log(1/δ)/k)`. -/
theorem chernoffInverse_slack (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (k : ℝ) + Real.log (1 / δ)
        + k * Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ chernoffInverse k δ := by
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hL : 0 ≤ Real.log (1 / δ) := by
    rw [one_div]
    exact Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1)
  have hsharp := chernoffInverse_ge_sharp hk hδ
  -- `f⁻¹(δ)/k ≥ 1 + log(1/δ)/k` from the crude bound
  have hcrude := chernoffInverse_ge_add_log hk hδ hδ1
  have hratio : 1 + Real.log (1 / δ) / (k : ℝ) ≤ chernoffInverse k δ / (k : ℝ) := by
    rw [le_div_iff₀ hkR, add_mul, one_mul, div_mul_cancel₀ _ hkR.ne']
    exact hcrude

  have hmono : Real.log (1 + Real.log (1 / δ) / (k : ℝ))
      ≤ Real.log (chernoffInverse k δ / (k : ℝ)) :=
    Real.log_le_log (by positivity) hratio
  nlinarith [mul_le_mul_of_nonneg_left hmono hkR.le]

end BanditAlgorithm

/-!
# The threshold inequality

This is the quantitative step that turns the mixture martingale into the
threshold `β_t(δ) = k log(t²+t) + f⁻¹(δ)` of Lattimore--Szepesvári Lemma 33.7.

Running the pair mixture at prior variance `c` controls the statistic
`Z_i²/(2(T_i + 1/c))` at the price `½log(1+cT_i)` per arm, plus `log(1/δ')` where
`δ'` is the confidence budget of a single pair.  Converting that into a statement
about the true statistic `Z_i²/(2T_i)` at threshold `β_n(δ)` requires

  `(c/(c+1)) · (k log(n²+n) + β₀)  ≥  log(1/δ) + log(k(k−1)) + log(1+c/2) + log n`

for every `n ≥ 1`, where `β₀ = f⁻¹(δ)`: the factor `c/(c+1)` is the loss from the
shift `T ↦ T + 1/c`, the `log(k(k−1))` is the union over ordered pairs of arms, and
`log(1+c/2) + log n` bounds the two `½log(1+cT_i)` prices.

**The choice of variance is `c = β₀`.**  This is what makes the inequality true,
and it is not arbitrary: the loss `c/(c+1)` must be within `O(1/β₀)` of `1`
because the whole budget `log(1/δ)` passes through it, while the price
`½log(1+c)` must stay within the slack of `β₀` over `k + log(1/δ)`.  That slack is
`k log(β₀/k)` — the sharp lower bound of `Solutions/ChernoffInverseSharp.lean` —
and it grows like `k log log(1/δ)`, exactly matching `log c`.  Neither a bounded
`c` nor a `c` growing faster than polynomially in `β₀` works.

After substituting the sharp bound on `β₀` and clearing the denominator the
inequality reduces to `b·P + Q ≥ 0` where

  `P = k log 2 + k − 1 − 2 log k − log(k−1)`,   `Q = k − 2 log k − log(k−1)`,

and both `P ≥ 0` and `2P + Q ≥ 0` follow from `log x ≤ x/e` alone.
-/

open Real

namespace BanditAlgorithm

/-! ## The two elementary positivity facts -/

/-- `P ≥ 0`: the coefficient of `b` after clearing denominators. -/
theorem threshold_coeff_P_nonneg {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ (k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlkNN : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hlk1NN : 0 ≤ Real.log ((k : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hlk' : Real.log (k : ℝ) * 2.7182818283 ≤ (k : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlkNN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk0))
  have hlk1' : Real.log ((k : ℝ) - 1) * 2.7182818283 ≤ (k : ℝ) - 1 :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlk1NN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk10))
  have hkL2 : (0.6931471803 : ℝ) * (k : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hl2.le hk0.le
  linarith [hlk', hlk1', hkL2, hkR]

/-- `2P + Q ≥ 0`: the value at the smallest admissible `b = 2`. -/
theorem threshold_coeff_PQ_nonneg {k : ℕ} (hk2 : 2 ≤ k) :
    0 ≤ 2 * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
          - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1))
        + ((k : ℝ) - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlkNN : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by linarith)
  have hlk1NN : 0 ≤ Real.log ((k : ℝ) - 1) := Real.log_nonneg (by linarith)
  have hlk' : Real.log (k : ℝ) * 2.7182818283 ≤ (k : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlkNN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk0))
  have hlk1' : Real.log ((k : ℝ) - 1) * 2.7182818283 ≤ (k : ℝ) - 1 :=
    le_trans (mul_le_mul_of_nonneg_left he.le hlk1NN)
      ((le_div_iff₀ (Real.exp_pos 1)).mp (log_le_div_exp_one hk10))
  have hkL2 : (0.6931471803 : ℝ) * (k : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hl2.le hk0.le
  linarith [hlk', hlk1', hkL2, hkR]

/-! ## The threshold inequality -/

/-- **The threshold inequality.**  With the prior variance set to `b = f⁻¹(δ)`, the
mixture budget covers the Chernoff threshold at every round `n ≥ 1`. -/
theorem threshold_master {k : ℕ} (hk2 : 2 ≤ k) {b L : ℝ} (hbk : (k : ℝ) ≤ b)
    (hL0 : 0 ≤ L) (hLb : (k : ℝ) + L + (k : ℝ) * Real.log (b / (k : ℝ)) ≤ b)
    {n : ℕ} (hn : 1 ≤ n) :
    L + Real.log ((k : ℝ) * ((k : ℝ) - 1)) + Real.log (1 + b / 2) + Real.log (n : ℝ)
      ≤ b / (b + 1) * ((k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + b) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hb2 : (2 : ℝ) ≤ b := le_trans hkR hbk
  have hb0 : (0 : ℝ) < b := by linarith
  have hb1 : (0 : ℝ) < b + 1 := by linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- the logarithms appearing
  have hA : Real.log ((n : ℝ) ^ 2 + (n : ℝ))
      = Real.log (n : ℝ) + Real.log ((n : ℝ) + 1) := by
    rw [show (n : ℝ) ^ 2 + (n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) by ring,
      Real.log_mul hn0.ne' (by linarith)]
  have hkk : Real.log ((k : ℝ) * ((k : ℝ) - 1))
      = Real.log (k : ℝ) + Real.log ((k : ℝ) - 1) := Real.log_mul hk0.ne' hk10.ne'
  have hbdiv : Real.log (b / (k : ℝ)) = Real.log b - Real.log (k : ℝ) :=
    Real.log_div hb0.ne' hk0.ne'
  have hhalf : Real.log (1 + b / 2) ≤ Real.log b :=
    Real.log_le_log (by linarith) (by linarith)
  have hLn0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hLn1 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLbk : Real.log (k : ℝ) ≤ Real.log b := Real.log_le_log hk0 hbk
  have hL2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the two positivity facts
  have hP := threshold_coeff_P_nonneg hk2
  have hPQ := threshold_coeff_PQ_nonneg hk2
  -- clear the denominator
  rw [div_mul_eq_mul_div, le_div_iff₀ hb1]
  rw [hkk, hA]
  -- the bound on `L`
  have hLub : L ≤ b - (k : ℝ) - (k : ℝ) * (Real.log b - Real.log (k : ℝ)) := by
    rw [hbdiv] at hLb
    linarith
  -- the leading `log n` coefficient is nonnegative
  have hcoefn : 0 ≤ (b * (k : ℝ) - b - 1) * Real.log (n : ℝ) := by
    have : (0 : ℝ) ≤ b * (k : ℝ) - b - 1 := by nlinarith
    exact mul_nonneg this hLn0
  -- the `log(n+1)` term dominates `log 2`
  have hcoefn1 : b * (k : ℝ) * Real.log 2 ≤ b * (k : ℝ) * Real.log ((n : ℝ) + 1) := by
    have hbk0 : (0 : ℝ) ≤ b * (k : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hLn1 hbk0
  -- `log b ≥ log k`, weighted
  have hcoefb : (b + 1) * ((k : ℝ) - 1) * Real.log (k : ℝ)
      ≤ (b + 1) * ((k : ℝ) - 1) * Real.log b := by
    have : (0 : ℝ) ≤ (b + 1) * ((k : ℝ) - 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left hLbk this
  -- `b · P ≥ 2 · P`
  have hbP : 2 * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1))
      ≤ b * ((k : ℝ) * Real.log 2 + (k : ℝ) - 1
        - 2 * Real.log (k : ℝ) - Real.log ((k : ℝ) - 1)) := by
    nlinarith [hP, hb2]
  nlinarith [hLub, hcoefn, hcoefn1, hcoefb, hbP, hPQ, hhalf, hb1, hb2, hLn0, hL2pos]

end BanditAlgorithm

/-!
# From the mixture exponent to the Chernoff statistic

Chernoff's stopping rule compares its threshold against

  `S_{a,b}(n) = T_a(n)(μ̂_a(n) − μ_a)²/2 + T_b(n)(μ̂_b(n) − μ_b)²/2`,

whereas the scaled pair mixture of `Solutions/PairMixtureScaled.lean` controls

  `E_{a,b}(n) = Σ_{i∈{a,b}} [ c Z_i(n)²/(2(1+c T_i(n))) − ½log(1+c T_i(n)) ]`.

This file bridges the two:

* `pullCount_mul_sq_dev_eq` identifies `T_i(μ̂_i − μ_i)²/2` with `Z_i²/(2T_i)`,
  including the degenerate case `T_i = 0` where Lean's `x/0 = 0` convention makes
  both sides vanish — which is exactly right, since an arm that has never been
  played contributes no deviation;
* `pair_log_price_le` bounds the two `½log(1+cT_i)` prices by
  `log(1+c/2) + log n`, using only `T_a + T_b ≤ n`;
* `mixtureExponent_ge_of_threshold` puts these together with the scale loss and
  the threshold inequality, showing that crossing the Chernoff threshold at round
  `n` forces the mixture exponent past `log(k(k−1)/δ)`.

The last statement is the whole reduction: with the prior variance set to
`c = f⁻¹(δ)`, the Chernoff event for a pair is contained in the crossing event of
the pair mixture martingale at level `k(k−1)/δ`.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-! ## Elementary facts about the pull counts -/

/-- A pull count is either zero or at least one, as a real number. -/
theorem trajPullCount_cast_zero_or_one (a : Fin k) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    (trajPullCount a n ω : ℝ) = 0 ∨ 1 ≤ (trajPullCount a n ω : ℝ) := by
  rcases Nat.eq_zero_or_pos (trajPullCount a n ω) with h | h
  · left; rw [h]; norm_num
  · right; exact_mod_cast h

/-- Two distinct arms cannot have been played more than `n` times between them. -/
theorem trajPullCount_pair_le {a b : Fin k} (hab : a ≠ b) (n : ℕ) (ω : ℕ → Fin k × ℝ) :
    trajPullCount a n ω + trajPullCount b n ω ≤ n := by
  classical
  calc trajPullCount a n ω + trajPullCount b n ω
      = ∑ i ∈ ({a, b} : Finset (Fin k)), trajPullCount i n ω :=
        (Finset.sum_pair (f := fun i ↦ trajPullCount i n ω) hab).symm
    _ ≤ ∑ i : Fin k, trajPullCount i n ω :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = n := sum_trajPullCount n ω

/-! ## The statistic in centred form -/

/-- `T(μ̂ − μ)²/2 = Z²/(2T)`, including at `T = 0` where both sides vanish. -/
theorem pullCount_mul_sq_dev_eq (μvec : Fin k → ℝ) (a : Fin k) (n : ℕ)
    (ω : ℕ → Fin k × ℝ) :
    (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
      = (centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ)) := by
  rcases Nat.eq_zero_or_pos (trajPullCount a n ω) with h0 | hpos
  · -- an arm that was never played contributes nothing on either side
    have hz : centredSum μvec a n ω = 0 := by
      unfold centredSum
      rw [h0]
      have : trajRewardSum a n ω = 0 := by
        unfold trajRewardSum
        have hcard : ((Finset.range n).filter fun s ↦ (ω s).1 = a).card = 0 := h0
        rw [Finset.card_eq_zero.mp hcard, Finset.sum_empty]
      rw [this]
      norm_num
    rw [h0, hz]
    norm_num
  · have hT : (0 : ℝ) < (trajPullCount a n ω : ℝ) := by exact_mod_cast hpos
    have hmean : trajEmpiricalMean a n ω
        = trajRewardSum a n ω / (trajPullCount a n ω : ℝ) := rfl
    unfold centredSum
    rw [hmean]
    field_simp

/-! ## The logarithmic price of the two pull counts -/

/-- Two `½log(1+c·)` prices with total mass at most `n` cost at most `log(1+cn/2)`. -/
theorem pair_log_price_le_half {c x y m : ℝ} (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsum : x + y ≤ m) :
    Real.log (1 + c * x) / 2 + Real.log (1 + c * y) / 2
      ≤ Real.log (1 + c * m / 2) := by
  have hx1 : (0 : ℝ) < 1 + c * x := by positivity
  have hy1 : (0 : ℝ) < 1 + c * y := by positivity
  have hm0 : (0 : ℝ) ≤ m := le_trans (by linarith) hsum
  have hm1 : (0 : ℝ) < 1 + c * m / 2 := by positivity
  -- `(1+cx)(1+cy) ≤ (1 + c(x+y)/2)² ≤ (1 + cm/2)²`
  have hxy : 4 * (x * y) ≤ m ^ 2 := by nlinarith [sq_nonneg (x - y)]
  have e1 : c * (x + y) ≤ c * m := mul_le_mul_of_nonneg_left hsum hc.le
  have e2 : c ^ 2 * (4 * (x * y)) ≤ c ^ 2 * m ^ 2 :=
    mul_le_mul_of_nonneg_left hxy (sq_nonneg c)
  have hprod : (1 + c * x) * (1 + c * y) ≤ (1 + c * m / 2) ^ 2 := by nlinarith [e1, e2]
  have hlog : Real.log ((1 + c * x) * (1 + c * y)) ≤ Real.log ((1 + c * m / 2) ^ 2) :=
    Real.log_le_log (by positivity) hprod
  rw [Real.log_mul hx1.ne' hy1.ne', Real.log_pow] at hlog
  push_cast at hlog
  linarith

/-- For `n ≥ 1` the price splits as `log(1+c/2) + log n`. -/
theorem log_one_add_half_mul_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    Real.log (1 + c * (n : ℝ) / 2) ≤ Real.log (1 + c / 2) + Real.log (n : ℝ) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hle : 1 + c * (n : ℝ) / 2 ≤ (1 + c / 2) * (n : ℝ) := by nlinarith
  calc Real.log (1 + c * (n : ℝ) / 2)
      ≤ Real.log ((1 + c / 2) * (n : ℝ)) := Real.log_le_log (by positivity) hle
    _ = Real.log (1 + c / 2) + Real.log (n : ℝ) :=
        Real.log_mul (by positivity) hn0.ne'

/-! ## The reduction -/

/-- **Crossing the Chernoff threshold forces the mixture exponent past
`log(k(k−1)/δ)`.**  This is the whole reduction, at a fixed round and a fixed
pair of arms, with the prior variance set to `c = f⁻¹(δ)`. -/
theorem mixtureExponent_ge_of_threshold (hk2 : 2 ≤ k) (μvec : Fin k → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {a b : Fin k} (hab : a ≠ b) (n : ℕ)
    (ω : ℕ → Fin k × ℝ)
    (hcross : chernoffThreshold k δ n
      ≤ (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
        + (trajPullCount b n ω : ℝ) * ((trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)) :
    Real.log (1 / (δ / ((k : ℝ) * ((k : ℝ) - 1))))
      ≤ scaledMixtureExponent μvec (chernoffInverse k δ) a n ω
        + scaledMixtureExponent μvec (chernoffInverse k δ) b n ω := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  set c : ℝ := chernoffInverse k δ with hcdef
  have hck : (k : ℝ) ≤ c := le_chernoffInverse hk0 hδ
  have hc2 : (2 : ℝ) ≤ c := le_trans hkR hck
  have hc0 : (0 : ℝ) < c := by linarith
  -- `n = 0` is impossible: the statistic vanishes but the threshold is positive
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    subst hn0
    simp only [trajPullCount_zero, Nat.cast_zero, zero_mul, add_zero] at hcross
    have hzero : chernoffThreshold k δ 0 = c := by
      unfold chernoffThreshold
      rw [← hcdef]
      simp
    rw [hzero] at hcross
    linarith
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  -- the statistic, in centred form
  rw [pullCount_mul_sq_dev_eq, pullCount_mul_sq_dev_eq] at hcross
  -- the scale loss
  have hTa : (0 : ℝ) ≤ (trajPullCount a n ω : ℝ) := Nat.cast_nonneg _
  have hTb : (0 : ℝ) ≤ (trajPullCount b n ω : ℝ) := Nat.cast_nonneg _
  have hloss : c / (c + 1)
        * ((centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ))
            + (centredSum μvec b n ω) ^ 2 / (2 * (trajPullCount b n ω : ℝ)))
      ≤ c * (centredSum μvec a n ω) ^ 2 / (2 * (1 + c * (trajPullCount a n ω : ℝ)))
        + c * (centredSum μvec b n ω) ^ 2 / (2 * (1 + c * (trajPullCount b n ω : ℝ))) := by
    have ha := selfnormalised_scale_loss_zero_or_one (c := c)
      (T := (trajPullCount a n ω : ℝ)) (z := centredSum μvec a n ω) hc0
      (trajPullCount_cast_zero_or_one a n ω)
    have hb := selfnormalised_scale_loss_zero_or_one (c := c)
      (T := (trajPullCount b n ω : ℝ)) (z := centredSum μvec b n ω) hc0
      (trajPullCount_cast_zero_or_one b n ω)
    have hrw : c / (c + 1)
        * ((centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ))
            + (centredSum μvec b n ω) ^ 2 / (2 * (trajPullCount b n ω : ℝ)))
        = c / (c + 1) * ((centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ)))
          + c / (c + 1) * ((centredSum μvec b n ω) ^ 2
              / (2 * (trajPullCount b n ω : ℝ))) := by ring
    rw [hrw]
    exact add_le_add ha hb
  -- the price of the two pull counts
  have hsum : (trajPullCount a n ω : ℝ) + (trajPullCount b n ω : ℝ) ≤ (n : ℝ) := by
    have := trajPullCount_pair_le hab n ω
    exact_mod_cast this
  have hprice : Real.log (1 + c * (trajPullCount a n ω : ℝ)) / 2
        + Real.log (1 + c * (trajPullCount b n ω : ℝ)) / 2
      ≤ Real.log (1 + c / 2) + Real.log (n : ℝ) :=
    le_trans (pair_log_price_le_half hc0 hTa hTb hsum)
      (log_one_add_half_mul_le hc0 hn1)
  -- the threshold inequality
  have hmaster := threshold_master (k := k) hk2 (b := c) (L := Real.log (1 / δ)) hck
    (by
      rw [one_div]
      exact Real.log_nonneg ((one_le_inv₀ hδ).mpr hδ1))
    (by
      have := chernoffInverse_ge_sharp hk0 hδ
      rw [← hcdef] at this
      linarith) hn1
  -- the threshold in explicit form
  have hthr : chernoffThreshold k δ n = (k : ℝ) * Real.log ((n : ℝ) ^ 2 + (n : ℝ)) + c := by
    unfold chernoffThreshold
    rw [← hcdef]
  -- the target confidence, in explicit form
  have hδ' : Real.log (1 / (δ / ((k : ℝ) * ((k : ℝ) - 1))))
      = Real.log (1 / δ) + Real.log ((k : ℝ) * ((k : ℝ) - 1)) := by
    have hkk : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
    rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_div hδ.ne' hkk.ne']
    ring
  -- the scale factor is at most one
  have hfrac : c / (c + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hstat_nonneg : (0 : ℝ)
      ≤ (centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ))
        + (centredSum μvec b n ω) ^ 2 / (2 * (trajPullCount b n ω : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ)) := by
      positivity
    have h2 : (0 : ℝ) ≤ (centredSum μvec b n ω) ^ 2 / (2 * (trajPullCount b n ω : ℝ)) := by
      positivity
    linarith
  have hscaled : c / (c + 1) * chernoffThreshold k δ n
      ≤ c / (c + 1)
        * ((centredSum μvec a n ω) ^ 2 / (2 * (trajPullCount a n ω : ℝ))
            + (centredSum μvec b n ω) ^ 2 / (2 * (trajPullCount b n ω : ℝ))) := by
    have hfrac0 : (0 : ℝ) ≤ c / (c + 1) := by positivity
    exact mul_le_mul_of_nonneg_left hcross hfrac0
  unfold scaledMixtureExponent
  rw [hδ']
  rw [hthr] at hscaled
  linarith

end BanditAlgorithm

/-!
# The probabilistic core of Lemma 33.7

The pairwise self-normalised deviation bound: for a unit-variance Gaussian bandit
and an arbitrary sampling rule,

  `P( ∃ n, ∃ a ≠ b,  T_a(n)(μ̂_a(n)−μ_a)²/2 + T_b(n)(μ̂_b(n)−μ_b)²/2 ≥ β_n(δ) )  ≤  δ`,

with `β_n(δ) = k log(n²+n) + f⁻¹(δ)` and `f(x) = e^{k−x}(x/k)^k`.  This is what
makes Chernoff's stopping rule sound at confidence `δ`.

Everything is now in place:

* the pair mixture martingale at prior variance `c` (`Solutions/PairMixtureScaled.lean`)
  and Ville's inequality (`Solutions/VilleEngine.lean`) give, for each fixed pair,
  a time-uniform bound at confidence `δ'`;
* `mixtureExponent_ge_of_threshold` (`Solutions/PairStatisticBridge.lean`) shows
  that crossing `β_n(δ)` forces the mixture exponent past `log(1/δ')`, once the
  variance is set to `c = f⁻¹(δ)`;
* a union over the `k(k−1)` ordered pairs of distinct arms, with the budget
  `δ' = δ/(k(k−1))`, assembles the whole statement.

The case `k = 1` is separate and vacuous: there is no pair of distinct arms, so
the event is empty.
-/

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

namespace BanditAlgorithm

variable {k : ℕ}

/-- The confidence budget of a single ordered pair of arms. -/
noncomputable def pairBudget (k : ℕ) (δ : ℝ) : ℝ := δ / ((k : ℝ) * ((k : ℝ) - 1))

theorem pairBudget_pos (hk2 : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) : 0 < pairBudget k δ := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  unfold pairBudget
  have : (0 : ℝ) < (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
  positivity

/-- The `k(k−1)` pair budgets add up to `δ`. -/
theorem card_offDiag_mul_pairBudget (hk2 : 2 ≤ k) {δ : ℝ} (hδ : 0 < δ) :
    (((Finset.univ : Finset (Fin k)).offDiag.card : ℕ) : ℝ≥0∞)
        * ENNReal.ofReal (pairBudget k δ)
      = ENNReal.ofReal δ := by
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk2
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hcard : ((Finset.univ : Finset (Fin k)).offDiag.card : ℕ) = k * k - k := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hle : k ≤ k * k := Nat.le_mul_of_pos_left k hk0
  have hmR : ((k * k - k : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    push_cast [Nat.cast_sub hle]
    ring
  rw [hcard, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  congr 1
  rw [hmR]
  unfold pairBudget
  have hk1 : ((k : ℝ) - 1) ≠ 0 := by intro h; nlinarith
  have hkne : (k : ℝ) ≠ 0 := by intro h; nlinarith
  field_simp

/-- **The pairwise self-normalised deviation bound.** -/
theorem chernoff_pairwise_deviation_bound [NeZero k] {δ : ℝ}
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (pol : BanditPolicy k) (μvec : Fin k → ℝ) :
    banditTrajMeasure (gaussianBandit μvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
          chernoffThreshold k δ n
            ≤ (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
              + (trajPullCount b n ω : ℝ)
                * ((trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)}
      ≤ ENNReal.ofReal δ := by
  classical
  obtain ⟨hδ0, hδ1⟩ := hδ
  rcases lt_or_ge k 2 with hk1 | hk2
  · -- `k = 1`: no pair of distinct arms exists, so the event is empty
    have hempty : {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
        chernoffThreshold k δ n
          ≤ (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
            + (trajPullCount b n ω : ℝ)
              * ((trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)} = ∅ := by
      have hk : k = 1 := by
        have := NeZero.pos k
        omega
      subst hk
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, a, b, hne, -⟩
      exact hne (Subsingleton.elim a b)
    rw [hempty, measure_empty]
    exact zero_le'
  · -- the substantive case
    set c : ℝ := chernoffInverse k δ with hcdef
    have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk2
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
    have hck : (k : ℝ) ≤ c := le_chernoffInverse hk0 hδ0
    have hc0 : (0 : ℝ) < c := by linarith
    have hbudget := pairBudget_pos hk2 hδ0
    -- the event is contained in the union of the pairwise crossing events
    have hsub : {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
          chernoffThreshold k δ n
            ≤ (trajPullCount a n ω : ℝ) * ((trajEmpiricalMean a n ω - μvec a) ^ 2 / 2)
              + (trajPullCount b n ω : ℝ)
                * ((trajEmpiricalMean b n ω - μvec b) ^ 2 / 2)}
        ⊆ ⋃ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
            {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
              Real.log (1 / pairBudget k δ)
                ≤ scaledMixtureExponent μvec c p.1 n ω
                  + scaledMixtureExponent μvec c p.2 n ω} := by
      rintro ω ⟨n, a, b, hab, hcross⟩
      simp only [Set.mem_iUnion, Finset.mem_coe, Set.mem_setOf_eq, exists_prop]
      refine ⟨(a, b), ?_, n, ?_⟩
      · simp [Finset.mem_offDiag, hab]
      · exact mixtureExponent_ge_of_threshold hk2 μvec hδ0 hδ1.le hab n ω hcross
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    -- each pair costs at most its budget
    have hterm : ∀ p ∈ (Finset.univ : Finset (Fin k)).offDiag,
        banditTrajMeasure (gaussianBandit μvec) pol
            {ω : ℕ → Fin k × ℝ | ∃ n : ℕ,
              Real.log (1 / pairBudget k δ)
                ≤ scaledMixtureExponent μvec c p.1 n ω
                  + scaledMixtureExponent μvec c p.2 n ω}
          ≤ ENNReal.ofReal (pairBudget k δ) := by
      intro p hp
      have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
      exact bandit_pair_selfnormalised_time_uniform_scaled μvec pol hc0 hne hbudget
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact le_of_eq (card_offDiag_mul_pairBudget hk2 hδ0)

end BanditAlgorithm

theorem _root_.solution {k : ℕ} [NeZero k]
    (delta : ℝ) (hdelta : delta ∈ Set.Ioo (0 : ℝ) 1)
    (pol : BanditAlgorithm.BanditPolicy k) (muvec : Fin k → ℝ) :
    BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit muvec) pol
        {ω : ℕ → Fin k × ℝ | ∃ n : ℕ, ∃ a b : Fin k, a ≠ b ∧
          BanditAlgorithm.chernoffThreshold k delta n
            ≤ (BanditAlgorithm.trajPullCount a n ω : ℝ)
                * ((BanditAlgorithm.trajEmpiricalMean a n ω - muvec a) ^ 2 / 2)
              + (BanditAlgorithm.trajPullCount b n ω : ℝ)
                * ((BanditAlgorithm.trajEmpiricalMean b n ω - muvec b) ^ 2 / 2)}
      ≤ ENNReal.ofReal delta :=
  BanditAlgorithm.chernoff_pairwise_deviation_bound hdelta pol muvec
