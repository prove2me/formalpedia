-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.select_depth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:36.991256+00:00
-- url     : https://prove2.me/submissions/4f24e614-c8ed-42f1-a36f-18d72ecb96f3

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_domain

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) {D : ℕ}
    (hB : ∀ z π, ((B z).fn π).isSome → π.length ≤ D) (z : (V × Bool)) (π : List (Fin n))
    (hπ : ((select c B h z).fn π).isSome) : π.length ≤ D :=
  hB z π (by rwa [select_domain] at hπ)
end DeciSigma1.Semantics.SignSelection
