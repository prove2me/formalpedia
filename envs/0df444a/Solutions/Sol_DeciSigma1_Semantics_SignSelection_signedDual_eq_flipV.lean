-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.signedDual_eq_flipV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:11.277304+00:00
-- url     : https://prove2.me/submissions/29cc44a1-48ef-48cb-988c-f8b61dc041c8

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution (A : (V × Bool) → Tree n) (z : (V × Bool)) :
    dual A z = Tree.dual (A (flipV z)) := rfl
end DeciSigma1.Semantics.SignSelection
