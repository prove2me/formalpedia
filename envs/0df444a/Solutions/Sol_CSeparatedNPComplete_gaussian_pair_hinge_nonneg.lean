-- Prove2me | solution 1 for CSeparatedNPComplete.gaussian_pair_hinge_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:06.163187+00:00
-- url     : https://prove2.me/submissions/df64663b-5905-4121-923b-1d6c75519464

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (c : ℝ) (a : Vec n)
    (g h : Gaussian n) : 0 ≤ gaussian_pair_hinge c a g h := le_max_left _ _
end CSeparatedNPComplete
