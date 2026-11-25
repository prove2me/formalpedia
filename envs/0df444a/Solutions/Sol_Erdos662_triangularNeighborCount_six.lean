-- Prove2me | solution 1 for Erdos662.triangularNeighborCount_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:13:50.207704+00:00
-- url     : https://prove2.me/submissions/cb66cba0-e847-4fbc-84a8-9d79f0a541b5

module
public import Definitions.Def_Statement
public import Definitions.Def_Research_GlobalShellSix
public import Definitions.Def_Erdos662Proof_Solution
public import Theorems.Thm_Research_mem_triCoordsWithinThirtySix_iff
public import Theorems.Thm_Research_triCoordsWithinThirtySix_card


set_option autoImplicit true
@[expose] public section
public section
open Erdos662
namespace Erdos662
theorem _root_.solution : triangularNeighborCount 6 = 126 := by
  rw [triangularNeighborCount, ← Research.triCoordsWithinThirtySix_card]
  apply Nat.subtype_card
  intro d
  rw [Research.mem_triCoordsWithinThirtySix_iff]
  constructor
  · rintro ⟨hne, hnorm⟩
    refine ⟨hne, ?_⟩
    have hcast : (Research.triNormSq d : ℝ) ≤ 36 := by exact_mod_cast hnorm
    norm_num [Research.triNormSq] at hcast ⊢
    exact hcast
  · rintro ⟨hne, hnorm⟩
    refine ⟨hne, ?_⟩
    have hcast : (Research.triNormSq d : ℝ) ≤ 36 := by
      norm_num [Research.triNormSq] at hnorm ⊢
      exact hnorm
    exact_mod_cast hcast
end Erdos662
