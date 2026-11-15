-- Prove2me | solution 2 for AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:26:10.356032+00:00
-- url     : https://prove2.me/submissions/ba59f77e-994f-4934-b495-870c3f28ac1a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal
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
      (S.card : ℝ≥0∞)  := by
  let A : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ Ioo (-1 : ℝ) 0}
  have hA : A = (S : Set ℝ≥0) := by
    ext u
    simp only [A, Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · intro hu
      exact (hS u).2 ⟨hu.1, hu.2.1, hu.2.2.2⟩
    · intro hu
      obtain ⟨hpos, hT, hmark⟩ := (hS u).1 hu
      exact ⟨hpos, hT, ne_of_lt hmark.2, hmark⟩
  have hFin : A.Finite := by
    rw [hA]
    exact S.finite_toSet
  have hF : hFin.toFinset = S := by
    apply Finset.ext
    intro u
    simpa only [Set.Finite.mem_toFinset, hA, Finset.mem_coe]
  have hFilter : S.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ T) = S := by
    apply Finset.ext
    intro u
    simp only [Finset.mem_filter]
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, ((hS u).1 hu).1, ((hS u).1 hu).2.1⟩
  have hExact := avram_a20_original_borel_window_finite_marked_times_card
    X ω T (Ioo (-1 : ℝ) 0) measurableSet_Ioo 0 T (by positivity) le_rfl hFin
  simpa only [A, hF, hFilter] using hExact
