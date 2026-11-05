-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_uniform_grid_intrinsic_test_difference_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:07:05.468116+00:00
-- url     : https://prove2.me/submissions/8a43dc95-4083-4059-9446-4d30ed2ca58a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_uniform_all_negative_test_sum_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators Classical

/-- A single eventual uniform-mesh bound controls the discrepancy between
the original grid test sum and its intrinsic finite jump test sum. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hL : ∀ t : ℝ≥0,
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t : ℝ≥0, ContinuousWithinAt Y (Ici t) t) :
    ∃ S : Finset ℝ≥0,
      (∀ u : ℝ≥0, u ∈ S ↔ 0 < u ∧ u ≤ T ∧
        ρ ≤ |Y u - Function.leftLim Y u|) ∧
      ∀ᶠ n : ℕ in atTop, ∀ f : ℝ → ℝ,
        (∀ z : ℝ, -ρ < z → f z = 0) →
        ∀ M : ℝ, 0 ≤ M → (∀ z : ℝ, |f z| ≤ M) →
        |(∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) -
          (∑ u ∈ S, f (Y u - Function.leftLim Y u))| ≤
          2 * (S.card : ℝ) * M := by
  classical
  obtain ⟨S, hS, hGrid⟩ :=
    avram_p2_l_mesh_uniform_all_negative_test_sum_envelope Y T hT ρ hρ hL hR
  refine ⟨S, hS, ?_⟩
  filter_upwards [hGrid] with n hn
  intro f hfzero M hM hfM
  have hTrue :
      |∑ u ∈ S, f (Y u - Function.leftLim Y u)| ≤
        (S.card : ℝ) * M := by
    have hfin (s : Finset ℝ≥0) :
        |∑ u ∈ s, f (Y u - Function.leftLim Y u)| ≤
          (s.card : ℝ) * M := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        calc
          |∑ u ∈ insert a s, f (Y u - Function.leftLim Y u)| =
              |f (Y a - Function.leftLim Y a) +
                ∑ u ∈ s, f (Y u - Function.leftLim Y u)| := by
                  rw [Finset.sum_insert ha]
          _ ≤ |f (Y a - Function.leftLim Y a)| +
              |∑ u ∈ s, f (Y u - Function.leftLim Y u)| := abs_add_le _ _
          _ ≤ M + (s.card : ℝ) * M := add_le_add (hfM _) ih
          _ = ((insert a s).card : ℝ) * M := by
            simp [ha]
            ring
    exact hfin S
  have hG := hn f hfzero M hM hfM
  calc
    _ ≤ |∑ i ∈ Finset.range (n + 1),
          f (Y (((i + 1 : ℕ) : ℝ≥0) *
                (T / ((n : ℝ≥0) + 1))) -
            Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))| +
          |∑ u ∈ S, f (Y u - Function.leftLim Y u)| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (∑ i ∈ Finset.range (n + 1),
                  f (Y (((i + 1 : ℕ) : ℝ≥0) *
                        (T / ((n : ℝ≥0) + 1))) -
                    Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
                (-(∑ u ∈ S, f (Y u - Function.leftLim Y u))))
    _ ≤ (S.card : ℝ) * M + (S.card : ℝ) * M := add_le_add hG hTrue
    _ = 2 * (S.card : ℝ) * M := by ring
