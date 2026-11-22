-- Prove2me | solution 1 for DeciSigma1.Constraints.PathBounds.embed_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:32.139126+00:00
-- url     : https://prove2.me/submissions/8ee9df44-98a8-4a06-93e8-07655726c890

module
public import Mathlib.Data.Fintype.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
open DeciSigma1.Constraints.PathBounds
namespace DeciSigma1.Constraints.PathBounds
theorem _root_.solution (filler t : Semantics.Tree n) (i : Fin n) (π : List (Fin n)) :
    embed filler (i :: π) t =
      Semantics.Tree.node (fun j => if j = i then embed filler π t else filler) := rfl
end DeciSigma1.Constraints.PathBounds
