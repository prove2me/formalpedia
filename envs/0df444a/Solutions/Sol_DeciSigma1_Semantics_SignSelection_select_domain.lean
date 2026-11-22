-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.select_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:34:53.59281+00:00
-- url     : https://prove2.me/submissions/87b25484-ab05-43d5-bc93-e902e4d584cd

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_mix_domain

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) (π : List (Fin n)) :
    ((select c B h z).fn π).isSome = ((B z).fn π).isSome :=
  mix_domain _ _ _ _ _ _
end DeciSigma1.Semantics.SignSelection
