-- Prove2me | solution 1 for DeciSigma1.Constraints.sign_signedVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:36:52.321797+00:00
-- url     : https://prove2.me/submissions/576aa238-4aab-4887-a297-ca87a30677ee

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
theorem _root_.solution (u : V) (p : Bool) : sign (signedVar u p) = p := rfl
end DeciSigma1.Constraints
