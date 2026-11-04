-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_exact_mesh_sum_tends_finite_nonzero_test_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:41:54.736125+00:00
-- url     : https://prove2.me/submissions/2fadafcb-75ca-4d74-85b9-00a01c01fd39

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- Genuine deterministic càdlàg mesh-to-jump equality. The finite set
contains exactly the nonzero test jumps in the right-closed horizon. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hneg : tsupport f ⊆ Set.Iio (0 : ℝ))
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ F : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
        f (Y u - Function.leftLim Y u) ≠ 0) ∧
      Tendsto (fun n : ℕ =>
        ∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
              (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (∑ u ∈ F, f (Y u - Function.leftLim Y u))) := by
  classical
  obtain ⟨ρ, hρ, hzero⟩ :=
    avram_p2_h_cadlag_strict_negative_tsupport_gives_zero_near_origin f hneg
  obtain ⟨S, hS, hlimit⟩ :=
    avram_p2_h_cadlag_uniform_test_sum_tends_to_all_large_actual_jumps
      Y T hT f hf ρ hρ hzero hL hR
  let F := S.filter (fun u => f (Y u - Function.leftLim Y u) ≠ 0)
  have hF (u : ℝ≥0) : u ∈ F ↔ 0 < u ∧ u ≤ T ∧
      f (Y u - Function.leftLim Y u) ≠ 0 := by
    change (u ∈ S.filter (fun v => f (Y v - Function.leftLim Y v) ≠ 0)) ↔
      0 < u ∧ u ≤ T ∧ f (Y u - Function.leftLim Y u) ≠ 0
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨huS, hnon⟩
      exact ⟨((hS u).mp huS).1, ((hS u).mp huS).2.1, hnon⟩
    · rintro ⟨hu0, huT, hnon⟩
      have hlarge : ρ ≤ |Y u - Function.leftLim Y u| := by
        apply le_of_not_gt
        intro hsmall
        exact hnon (hzero _ hsmall)
      exact ⟨(hS u).mpr ⟨hu0, huT, hlarge⟩, hnon⟩
  have hsum : (∑ u ∈ S, f (Y u - Function.leftLim Y u)) =
      ∑ u ∈ F, f (Y u - Function.leftLim Y u) := by
    have hsub : F ⊆ S := Finset.filter_subset _ _
    have hOutside : ∀ u ∈ S, u ∉ F →
        f (Y u - Function.leftLim Y u) = 0 := by
      intro u huS huF
      by_contra hnon
      exact huF (Finset.mem_filter.mpr ⟨huS, hnon⟩)
    exact (Finset.sum_subset hsub hOutside).symm
  refine ⟨F, hF, ?_⟩
  simpa only [hsum] using hlimit
