-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_lintegral_bound_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:42:34.113588+00:00
-- url     : https://prove2.me/submissions/e1e8ef02-722f-4e6a-9a70-433545fae719

import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_lintegral_l2_ae_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! Any finite squared ENNReal moment envelope suffices for real expectation convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (K : ENNReal)
    (hK : K ≠ ⊤)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤ K)
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  let B : ℝ≥0 := NNReal.sqrt K.toNNReal
  have hKsq : K = (B : ENNReal) ^ 2 := by
    calc
      K = (K.toNNReal : ENNReal) := (ENNReal.coe_toNNReal hK).symm
      _ = (((NNReal.sqrt K.toNNReal) ^ 2 : ℝ≥0) : ENNReal) := by
        exact congrArg (fun x : ℝ≥0 => (x : ENNReal))
          (NNReal.sq_sqrt K.toNNReal).symm
      _ = (B : ENNReal) ^ 2 := by
        rw [← ENNReal.coe_pow]
  have hBound : ∀ n,
      (∫⁻ ω, ‖Y n ω‖ₑ ^ (2 : ℝ) ∂P) ≤ (B : ENNReal) ^ 2 := by
    intro n
    simpa only [← hKsq] using hB n
  exact avram_p2_j_ui_lintegral_l2_ae_expectations P Y Z B hm hBound hae
