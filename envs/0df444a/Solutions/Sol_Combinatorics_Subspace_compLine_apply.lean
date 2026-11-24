-- Prove2me | solution 1 for Combinatorics.Subspace.compLine_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:50:29.237829+00:00
-- url     : https://prove2.me/submissions/92ec8d82-e282-4bba-879d-e61b6cadc05d

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_ShelahHalesJewett_Line

set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
variable {η α ι ι' κ : Type*}
open Combinatorics.Subspace
namespace Combinatorics.Subspace
theorem _root_.solution (V : Subspace η α ι) (l : Line α η) (x : α) : V.compLine l x = V (l x) := by
  funext i
  cases h : V.idxFun i <;> simp [compLine, coe_apply, h]
end Combinatorics.Subspace
