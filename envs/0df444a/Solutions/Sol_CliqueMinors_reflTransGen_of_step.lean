-- Prove2me | solution 1 for CliqueMinors.reflTransGen_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:38:47.005312+00:00
-- url     : https://prove2.me/submissions/2b60181c-04c7-4ce4-b4ce-fda465e3438d

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation
namespace CliqueMinors
theorem _root_.solution {α : Type*} {r p : α → α → Prop}
    (h : ∀ a b, r a b → ReflTransGen p a b) {a b : α} (hab : ReflTransGen r a b) :
    ReflTransGen p a b := by
  induction hab with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (h _ _ hbc)
end CliqueMinors
