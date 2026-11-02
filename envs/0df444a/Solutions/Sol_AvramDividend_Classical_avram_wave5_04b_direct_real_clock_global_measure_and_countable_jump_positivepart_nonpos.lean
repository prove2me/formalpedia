-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_direct_real_clock_global_measure_and_countable_jump_positivepart_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:05:41.679557+00:00
-- url     : https://prove2.me/submissions/cff992b6-beb7-411b-ba82-b3731f27c8be

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Summability-free real-clock joint nonpositive control of the complete actual closed-horizon Stieltjes mass and the absolutely summable countable explicit-w right-payment correction, with no reserve-interior localisation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω)
    (hjump : ∀ t : ℝ≥0,
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (A : Set ℝ) (hCount : A.Countable)
    (hNonneg : ∀ t : A, 0 ≤ (t : ℝ))
    (hA : ∀ t : A,
      ((t : ℝ).toNNReal) = 0 ∨
        (((t : ℝ).toNNReal) : ℝ≥0∞) < ruinTime X x D ω)
    : ((∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω))) +
    (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))).toReal ≤ 0 := by
  have hContinuous := avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
    X x C hC q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD ω T hPre
  have hTerm : ∀ t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω))) = 0 := by
    intro t
    have hDrop := hjump ((t : ℝ).toNNReal) (hA t)
    have hResidual :
        (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
          w (riskProcess X x D ((t : ℝ).toNNReal) ω -
            (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
          w (riskProcess X x D ((t : ℝ).toNNReal) ω) ≤ 0 := by
      linarith only [hDrop]
    apply ENNReal.ofReal_eq_zero.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual
  have hZero : (∑' t : A, ENNReal.ofReal (Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω) +
        w (riskProcess X x D ((t : ℝ).toNNReal) ω -
          (rightLimit D ((t : ℝ).toNNReal) ω - D ((t : ℝ).toNNReal) ω)) -
        w (riskProcess X x D ((t : ℝ).toNNReal) ω)))) = 0 := by
    simp [hTerm]
  simpa [hZero] using hContinuous
