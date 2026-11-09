-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_jump_tsum_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T19:16:42.199249+00:00
-- url     : https://prove2.me/submissions/0b3b400a-164f-4af0-831d-5d35f72e82cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ∧
      (∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
        else 0) =
        ∑ u ∈ F, (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  classical
  have hAll :=
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite
  filter_upwards [hAll] with ω hω
  intro t
  let j : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let J : Set ℝ≥0 := {u | 0 < u ∧ u ≤ t ∧ j u ≠ 0}
  have hJ : J.Finite := hω t
  refine ⟨hJ.toFinset, ?_, ?_⟩
  · intro u
    simpa only [hJ.mem_toFinset, J, Set.mem_setOf_eq, j]
  · change (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then j u else 0) =
      ∑ u ∈ hJ.toFinset, j u
    rw [tsum_eq_sum (s := hJ.toFinset)]
    · apply Finset.sum_congr rfl
      intro u hu
      have huJ : u ∈ J := (hJ.mem_toFinset).mp hu
      simp [huJ.1, huJ.2.1]
    · intro u hu
      have hNot : u ∉ J := by
        intro hmem
        exact hu ((hJ.mem_toFinset).mpr hmem)
      by_cases ht : 0 < u ∧ u ≤ t
      · have hj : j u = 0 := by
          by_contra hne
          exact hNot ⟨ht.1, ht.2, hne⟩
        simp [ht, hj]
      · simp [ht]
