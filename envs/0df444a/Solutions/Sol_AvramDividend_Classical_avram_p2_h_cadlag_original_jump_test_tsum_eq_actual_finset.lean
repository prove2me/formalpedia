-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_original_jump_test_tsum_eq_actual_finset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:16:48.748972+00:00
-- url     : https://prove2.me/submissions/5ce8ea95-9429-4cf5-91d8-7389d5cca708

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- The original cadlag jump-test series is a literal finite sum over precisely
the genuine jump times where the separated test does not vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0)
    (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hzero : ∀ y : ℝ, |y| < δ → f y = 0) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then
        f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
        else 0) =
      ∑ u ∈ F, f (X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by
  classical
  let mark : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let S : Set ℝ≥0 := {u | 0 < u ∧ u ≤ T ∧ f (mark u) ≠ 0}
  have hlarge :
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧ δ ≤ dist (mark u) 0}.Finite :=
    avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
      X ω T δ hδ
  have hS : S.Finite := by
    apply hlarge.subset
    intro u hu
    rcases hu with ⟨hu0, huT, hf⟩
    have hnot : ¬ |mark u| < δ := by
      intro hsmall
      exact hf (hzero (mark u) hsmall)
    exact ⟨hu0, huT, by
      simpa only [Real.dist_eq, sub_zero] using (le_of_not_gt hnot)⟩
  refine ⟨hS.toFinset, ?_, ?_⟩
  · intro u
    exact hS.mem_toFinset
  · change (∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then f (mark u) else 0) =
        ∑ u ∈ hS.toFinset, f (mark u)
    calc
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ T then f (mark u) else 0) =
          ∑ u ∈ hS.toFinset, (if 0 < u ∧ u ≤ T then f (mark u) else 0) := by
        apply tsum_eq_sum (s := hS.toFinset)
        intro u hu
        by_cases ht : 0 < u ∧ u ≤ T
        · have hfzero : f (mark u) = 0 := by
            by_contra hne
            have hm : u ∈ hS.toFinset := hS.mem_toFinset.mpr ⟨ht.1, ht.2, hne⟩
            exact hu hm
          simp [ht, hfzero]
        · simp [ht]
      _ = ∑ u ∈ hS.toFinset, f (mark u) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hm : u ∈ S := hS.mem_toFinset.mp hu
        simp only [S, Set.mem_setOf_eq] at hm
        simp [hm.1, hm.2.1]
