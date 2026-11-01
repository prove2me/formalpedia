-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:01:01.82307+00:00
-- url     : https://prove2.me/submissions/487fefc2-a2f2-417e-bc9b-71a0101ceccd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
      riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0 ∧
      riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ∈ B}).encard =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) := by
  rw [avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
    X ω s t B hB]
  apply congrArg (fun S : Set ℝ≥0 => (S.encard : ℝ≥0∞))
  ext u
  by_cases hu : 0 < u
  · simp only [Set.mem_setOf_eq]
    rw [avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
      X x D hD ω u hu]
  · simp [hu]
