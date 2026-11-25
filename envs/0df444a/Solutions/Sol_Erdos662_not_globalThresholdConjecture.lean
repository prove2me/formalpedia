-- Prove2me | solution 1 for Erdos662.not_globalThresholdConjecture
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:32:03.099688+00:00
-- url     : https://prove2.me/submissions/7d3b0276-8ced-4a33-b1f0-bc3ebd035e3a

module
public import Definitions.Def_Statement
public import Definitions.Def_Research_GlobalShellSix
public import Definitions.Def_Erdos662Proof_Solution
public import Theorems.Thm_Erdos662_globalThresholdConjecture_implies_shellSix
public import Theorems.Thm_Research_not_eventualShellSixDirectedAverageBound


set_option autoImplicit true
@[expose] public section
public section
open Erdos662
namespace Erdos662
theorem _root_.solution : ¬ GlobalThresholdConjecture := by
  intro h
  exact Research.not_eventualShellSixDirectedAverageBound
    (globalThresholdConjecture_implies_shellSix h)
end Erdos662
