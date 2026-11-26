-- Prove2me | solution 1 for Falmagne.randomUtility_necessary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:26:28.64518+00:00
-- url     : https://prove2.me/submissions/e599f4eb-87b8-4a32-b2eb-d9d3e80c7a13

module
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
public import Definitions.Def_EconomicsNextProof_Conservation
public import Definitions.Def_EconomicsNextProof_PathChoice
public import Definitions.Def_EconomicsNextProof_Flow
public import Definitions.Def_EconomicsNextProof_Falmagne
public import Theorems.Thm_Falmagne_blockMarschak_necessary


set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
namespace Falmagne
theorem _root_.solution {p : Finset X → X → ℝ}
    (h : RandomUtilityRepresentable p) : BlockMarschakNonnegative p := by
  obtain ⟨w, hw, hp⟩ := h
  exact blockMarschak_necessary hw hp
end Falmagne
