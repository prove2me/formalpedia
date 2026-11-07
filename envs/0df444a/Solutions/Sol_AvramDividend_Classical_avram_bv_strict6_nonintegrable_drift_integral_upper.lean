-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_nonintegrable_drift_integral_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:41:08.336018+00:00
-- url     : https://prove2.me/submissions/3637d2db-14d6-43aa-a430-4c354fc42f24

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The nonpositive original drift is discarded before integrating the reward. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, (∫ ω, F n ω ∂P) ≤
      a + (∫ ω, max (E n ω) 0 ∂P) := by
  intro n
  have hDrop : ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + max (E n ω) 0 := by
    filter_upwards [hPath n, hB n] with ω hp hb
    linarith
  have hConst : Integrable (fun _ : Ω => a) P := integrable_const _
  have hSM : Integrable (fun ω => a + M n ω) P :=
    hConst.add (hM n).1
  have hTotal : Integrable (fun ω => a + M n ω + max (E n ω) 0) P :=
    hSM.add (hE n)
  have hCmp : (∫ ω, F n ω ∂P) ≤
      ∫ ω, a + M n ω + max (E n ω) 0 ∂P :=
    integral_mono_ae (hF n) hTotal hDrop
  have hEval :
      (∫ ω, a + M n ω + max (E n ω) 0 ∂P) =
        a + (∫ ω, max (E n ω) 0 ∂P) := by
    rw [integral_add hSM (hE n), integral_add hConst (hM n).1]
    simp [(hM n).2]
  exact le_trans hCmp (le_of_eq hEval)
