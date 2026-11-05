-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep9_original_predictable_HJB_drift_L1_without_prestate_assumption
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T15:39:30.029117+00:00
-- url     : https://prove2.me/submissions/200687be-3fe3-4101-a58c-b4efdc00fba6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
(hD : IsDividendStrategy 𝓕 D) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHm : Measurable H)
(hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  exact avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
    X T x D q hq E hEm
    (avram_integration_sweep9_original_controlled_prestate_ambient_measurable
      X x D hD)
    a b hab hEregion H hHm hHcont

