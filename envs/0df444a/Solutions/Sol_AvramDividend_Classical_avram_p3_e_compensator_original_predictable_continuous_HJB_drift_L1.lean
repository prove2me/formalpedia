-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_predictable_continuous_HJB_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:51:13.434515+00:00
-- url     : https://prove2.me/submissions/f14b3235-5fef-4ee4-9233-087b9dd35e08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_discounted_HJB_drift_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
(T : ℝ≥0) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (q : ℝ) (hq : 0 ≤ q)
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hUpm : Measurable (fun p : ℝ≥0 × Ω => Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1))
(a b : ℝ) (hab : a ≤ b)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b)
(H : ℝ → ℝ) (hHm : Measurable H)
(hHcont : ContinuousOn H (Set.Icc a b)) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) * H (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) else 0) ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P) := by
  have hEmeas : MeasurableSet E :=
    avram_p3_e_compensator_original_rightCont_predictable_ambient_measurable E hEm
  have hFm := avram_p3_e_compensator_original_discounted_HJB_drift_measurable
    X T x D q E hEmeas hUpm H hHm
  obtain ⟨K, hK, hKbound⟩ :=
    avram_p3_e_compensator_original_HJB_generator_compact_bound_of_continuity
      H a b hab hHcont
  exact avram_p3_e_compensator_original_HJB_drift_L1_of_compact_bound
    X T x D q hq E a b K hK H hEregion hKbound hFm
