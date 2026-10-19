-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.exists_paletteStage_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/46312168-03da-4b1f-8a8d-b310b4fa9a5c

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteColourCount_mono
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_two_mul_stage_le_paletteColourCount

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (k : ℕ)
    (hk : paletteColourCount 2 ≤ k) :
    ∃ H : ℕ, 2 ≤ H ∧
      paletteColourCount H ≤ k ∧ k < paletteColourCount (H + 1) := by
  have hexists : ∃ H : ℕ, k < paletteColourCount H := by
    refine ⟨k + 1, ?_⟩
    have hcount := two_mul_stage_le_paletteColourCount (k + 1)
    omega
  let M : ℕ := Nat.find hexists
  have hM : k < paletteColourCount M := Nat.find_spec hexists
  have hMpos : 1 ≤ M := by
    by_contra hnot
    have hzero : M = 0 := by omega
    simp [hzero, paletteColourCount] at hM
  have hMlarge : 2 < M := by
    by_contra hnot
    have hMtwo : M ≤ 2 := by omega
    have hmono := paletteColourCount_mono hMpos hMtwo
    omega
  refine ⟨M - 1, by omega, ?_, ?_⟩
  · have hminimal :=
      Nat.find_min hexists (show M - 1 < M by omega)
    change ¬ k < paletteColourCount (M - 1) at hminimal
    omega
  · have hsucc : M - 1 + 1 = M := by omega
    simpa [hsucc] using hM
end ErdosProblems.MulticolourTriangleRamsey
