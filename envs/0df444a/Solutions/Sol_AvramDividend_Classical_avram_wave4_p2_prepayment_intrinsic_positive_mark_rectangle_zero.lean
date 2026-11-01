-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_prepayment_intrinsic_positive_mark_rectangle_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:22:18.10277+00:00
-- url     : https://prove2.me/submissions/bdc1ea8f-35cc-401c-a353-f950b0ffae12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source

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
    (ω : Ω) (s t : ℝ≥0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u)))
      (Ioc s t ×ˢ Ioi (0 : ℝ)) = 0 := by
  have hEmpty :
      {u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0 ∧
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ∈
            Ioi (0 : ℝ)} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_Ioi,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨hu, _hs, _ht, _hn, hpos⟩
    rw [avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark
      X x D hD ω u hu] at hpos
    exact (not_lt_of_ge
      (avram_wave4_04a_actual_levy_jumpmark_nonpositive X ω u hu)) hpos
  calc
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ riskProcess X x D u ω -
        Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u)))
        (Ioc s t ×ˢ Ioi (0 : ℝ)) =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Ioi (0 : ℝ)) := by
          exact congrArg
            (fun μ : Measure (ℝ≥0 × ℝ) =>
              μ (Ioc s t ×ˢ Ioi (0 : ℝ)))
            (avram_wave4_p2_prepayment_intrinsic_marked_jump_measure_eq_source
              X x D hD ω)
    _ = ({u : ℝ≥0 | 0 < u ∧ s < u ∧ u ≤ t ∧
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ≠ 0 ∧
        riskProcess X x D u ω -
          Function.leftLim (fun v : ℝ≥0 => riskProcess X x D v ω) u ∈
            Ioi (0 : ℝ)}).encard :=
        (avram_wave4_p2_prepayment_intrinsic_source_rectangle_count_exact
          X x D hD ω s t (Ioi (0 : ℝ)) measurableSet_Ioi).symm
    _ = 0 := by rw [hEmpty]; simp
