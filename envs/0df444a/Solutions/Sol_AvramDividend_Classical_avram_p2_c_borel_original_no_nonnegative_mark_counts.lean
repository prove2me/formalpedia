-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_no_nonnegative_mark_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:41:01.724789+00:00
-- url     : https://prove2.me/submissions/c7bca124-adc8-4fb0-be3c-d501f3870b72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_nonzero_jump_strictly_negative
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_count_restrict_map_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Genuine original intrinsic jump-count measures give zero mass to all
Borel nonnegative mark sets, using source pathwise spectral negativity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hBpos : B ⊆ Ici (0 : ℝ))
    (hmarkMeas : Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) = 0 := by
  let J : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}
  let mark : ℝ≥0 → ℝ≥0 × ℝ := fun u =>
    (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
  have hEmpty : {u : ℝ≥0 |
      u ∈ J ∧ mark u ∈ Ioc s t ×ˢ B} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hJ, hProd⟩
    have hpos : 0 < u := hJ.1
    have hnonzero : X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 :=
      hJ.2
    have hneg :=
      avram_p2_c_borel_original_nonzero_jump_strictly_negative
        X ω u hpos hnonzero
    exact (not_lt_of_ge (hBpos hProd.2)) hneg
  change ((Measure.count.restrict J).map mark) (Ioc s t ×ˢ B) = 0
  calc
    ((Measure.count.restrict J).map mark) (Ioc s t ×ˢ B) =
        Measure.count {u : ℝ≥0 |
          u ∈ J ∧ mark u ∈ Ioc s t ×ˢ B} :=
      avram_p2_c_borel_count_restrict_map_rectangle
        mark hmarkMeas J (Ioc s t) B measurableSet_Ioc hB
    _ = 0 := by rw [hEmpty]; simp
