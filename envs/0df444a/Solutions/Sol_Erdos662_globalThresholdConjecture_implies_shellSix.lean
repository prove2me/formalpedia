-- Prove2me | solution 1 for Erdos662.globalThresholdConjecture_implies_shellSix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:20:13.826406+00:00
-- url     : https://prove2.me/submissions/b2a4c5ce-547e-4786-b1e5-8ee3e03e5b96

module
public import Definitions.Def_Statement
public import Definitions.Def_Research_GlobalShellSix
public import Definitions.Def_Erdos662Proof_Solution
public import Theorems.Thm_Erdos662_triangularNeighborCount_six

set_option autoImplicit true
@[expose] public section
public section
open Erdos662
namespace Erdos662
theorem _root_.solution
    (h : GlobalThresholdConjecture) : Research.EventualShellSixDirectedAverageBound := by
  obtain ⟨N, hN⟩ := h 6 (by norm_num)
  refine ⟨N, ?_⟩
  intro α _ _ hcard p hp
  have hbound := hN α hcard p hp
  have hpairs : closeDirectedPairs 6 p = Research.radiusSixOrdinaryDirectedPairs p := by
    unfold closeDirectedPairs Research.radiusSixOrdinaryDirectedPairs
    congr 1
  rw [hpairs, triangularNeighborCount_six] at hbound
  exact hbound
end Erdos662
