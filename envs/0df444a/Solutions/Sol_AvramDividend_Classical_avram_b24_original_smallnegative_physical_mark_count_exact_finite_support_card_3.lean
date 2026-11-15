-- Prove2me | solution 3 for AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:26:33.43722+00:00
-- url     : https://prove2.me/submissions/bdd4f375-878c-4d20-8d73-4bbc44c12ba6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (S : Finset ℝ≥0)
    (hS : ∀ u : ℝ≥0, u ∈ S ↔
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈
        Ioo (-1 : ℝ) 0) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0) =
      (S.card : ℝ≥0∞) := by
  let E : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈
        Ioo (-1 : ℝ) 0}
  have hE : E = (S : Set ℝ≥0) := by
    ext u
    constructor
    · intro hu
      exact (hS u).2 ⟨hu.1, hu.2.1, hu.2.2.2⟩
    · intro hu
      obtain ⟨hpos, hle, hjump⟩ := (hS u).1 hu
      exact ⟨hpos, hle, ne_of_lt hjump.2, hjump⟩
  have hFinite : E.Finite := by
    rw [hE]
    exact S.finite_toSet
  have hBase :=
    avram_a20_original_borel_window_finite_marked_times_card
      X ω T (Ioo (-1 : ℝ) 0) measurableSet_Ioo 0 T
      (by positivity : 0 ≤ T) le_rfl hFinite
  have hFin : hFinite.toFinset = S := by
    ext u
    simp only [Set.Finite.mem_toFinset, hE, Finset.mem_coe]
  rw [hFin] at hBase
  have hFilter : S.filter (fun u => 0 < u ∧ u ≤ T) = S := by
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact ⟨((hS u).1 hu).1, ((hS u).1 hu).2.1⟩
  rw [hFilter] at hBase
  simpa only [Nat.cast_id] using hBase
