-- Prove2me | solution 1 for DeciSigma1.Constraints.signedVar_base_sign
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:55.053898+00:00
-- url     : https://prove2.me/submissions/991ed1fd-3c5c-4aa0-8dea-b79d34c40919

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
theorem _root_.solution (z : V × Bool) : signedVar (base z) (sign z) = z := rfl
end DeciSigma1.Constraints
