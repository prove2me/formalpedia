-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:25:46.962024+00:00
-- url     : https://prove2.me/submissions/d670a6c0-3702-4b42-b183-d081bcecf53c

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
  classical
  let z : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let G : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ z u ≠ 0 ∧
    z u ∈ Ioo (-1 : ℝ) 0}
  have hG : G = (↑S : Set ℝ≥0) := by
    ext u
    simp only [G, Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · intro h
      exact (hS u).2 ⟨h.1, h.2.1, h.2.2.2⟩
    · intro h
      have hdata := (hS u).1 h
      have hneq : z u ≠ 0 := ne_of_lt (Set.mem_Ioo.mp hdata.2.2).2
      exact ⟨hdata.1, hdata.2.1, hneq, hdata.2.2⟩
  have hF : G.Finite := by
    rw [hG]
    exact S.finite_toSet
  have hFilter : (hF.toFinset.filter (fun u : ℝ≥0 => 0 < u ∧ u ≤ T)) = S := by
    ext u
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · intro h
      have hmem : u ∈ G := h.1
      rw [hG] at hmem
      exact hmem
    · intro hu
      have hdata := (hS u).1 hu
      refine ⟨?_, ⟨hdata.1, hdata.2.1⟩⟩
      rw [hG]
      exact hu
  have hCount :=
    AvramDividend.Classical.avram_a20_original_borel_window_finite_marked_times_card
      X ω T (Ioo (-1 : ℝ) 0) measurableSet_Ioo
      0 T zero_le le_rfl hF
  rw [hFilter] at hCount
  exact hCount
