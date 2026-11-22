-- Prove2me | solution 1 for DeciSigma1.Constraints.exists_eq_signedVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:39:16.304556+00:00
-- url     : https://prove2.me/submissions/8798ad69-9d0c-40ff-b868-d86bded82b3a

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Constraints
theorem _root_.solution (z : V × Bool) : ∃ u p, z = signedVar u p :=
  ⟨z.1, z.2, rfl⟩
end DeciSigma1.Constraints
