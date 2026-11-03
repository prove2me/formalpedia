-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_random_stopped_nonnegative_marked_cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:47:07.416755+00:00
-- url     : https://prove2.me/submissions/d6e06ecf-a828-4a0c-a77e-7e05fae3ad73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source intrinsic marked count vanishes on random stopped nonnegative cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0∞)
    (B : Ω → Set ℝ)
    (hB : ∀ ω, B ω ⊆ Ici (0 : ℝ))
    (ω : Ω) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      ({t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ ω} ×ˢ B ω) = 0 := by
  classical
  let N : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let S : Set (ℝ≥0 × ℝ) :=
    {t : ℝ≥0 | (t : ℝ≥0∞) ≤ τ ω} ×ˢ B ω
  have hRestrict :
      N S = N (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) :=
    avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support
      X ω S
  have hEmpty : S ∩ (Set.univ ×ˢ Iio (0 : ℝ)) = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hS, hNeg⟩
    rcases p with ⟨t, z⟩
    have hzB : z ∈ B ω := hS.2
    have hzNonneg : (0 : ℝ) ≤ z := hB ω hzB
    exact (not_lt_of_ge hzNonneg) hNeg.2
  change N S = 0
  rw [hRestrict, hEmpty, measure_empty]
