-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.select_sat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:34:57.72562+00:00
-- url     : https://prove2.me/submissions/029e3a6d-f05b-4a3f-bd78-a075d54d3ddb

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_signed_signCoherent
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_select_sat_of_coherent
public import Theorems.Thm_DeciSigma1_Constraints_sat_signedDual


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution {c : Fin n → Bool} {Γ : List (LitT n V)} {B : (V × Bool) → Tree n}
    (hs : Covariant.Sat B (signed c Γ)) (h : ∀ z, SameShape (B z) (dual B z)) :
    Covariant.Sat (select c B h) (signed c Γ) :=
  select_sat_of_coherent (signed_signCoherent c Γ) hs (sat_signedDual c hs) h
end DeciSigma1.Semantics.SignSelection
