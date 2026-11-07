-- Prove2me | solution 1 for AvramDividend.Classical.avram_route9_nonintegrable_drift_signed_L1_fatou_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:52:25.938029+00:00
-- url     : https://prove2.me/submissions/bb9b6c0a-027b-4d7c-94e5-2500d5d9ce1d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_signed_L1_mesh_error_fatou
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A nonintegrable nonpositive drift can be dropped before signed Fatou. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (a : ℝ) (Y : Ω → ℝ) (F M B E : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P) (hYPos : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hM : ∀ n, Integrable (M n) P ∧
      (∫ ω, M n ω ∂P) = 0)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hEMean : Tendsto
      (fun n => ∫ ω, max (E n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ a := by
  have hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + max (E n ω) 0 := by
    intro n
    filter_upwards [hPath n, hB n] with ω hp hb
    linarith
  exact avram_p3_2_signed_L1_mesh_error_fatou
    P a Y F M (fun n ω => max (E n ω) 0)
    hYInt hYPos hFMeas hFInt hFPos
    (fun n => ⟨(hM n).1, le_of_eq (hM n).2⟩)
    hE hEMean hBound hFatou
