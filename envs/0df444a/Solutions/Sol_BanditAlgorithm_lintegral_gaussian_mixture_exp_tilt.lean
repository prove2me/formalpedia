-- Prove2me | solution 1 for BanditAlgorithm.lintegral_gaussian_mixture_exp_tilt
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T21:28:46.788776+00:00
-- url     : https://prove2.me/submissions/50b0b7f6-76fc-423d-bf77-1ea9d04325e7

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

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

theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (z : ℝ) :
    ∫⁻ lam : ℝ, ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(lam ^ 2) / 2)
        * Real.exp (lam * z - lam ^ 2 * t / 2))
      = ENNReal.ofReal ((Real.sqrt (1 + t))⁻¹ * Real.exp (z ^ 2 / (2 * (1 + t)))) :=
  BanditAlgorithm.lintegral_tilt_mixture ht z
