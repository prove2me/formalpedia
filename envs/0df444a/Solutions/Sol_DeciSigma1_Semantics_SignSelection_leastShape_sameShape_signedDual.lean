-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.leastShape_sameShape_signedDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:49:53.66903+00:00
-- url     : https://prove2.me/submissions/94288a28-af8a-43f8-ac3a-3fbfa8d4448a

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Selector
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_signedDual_eq_flipV
public import Theorems.Thm_DeciSigma1_Semantics_SignSelection_leastShape_flip_f
public import Theorems.Thm_DeciSigma1_Semantics_normalize_constructor


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics DeciSigma1.Semantics.SignSelection
open DeciSigma1.Constraints DeciSigma1.Constraints.Covariant DeciSigma1.Constraints.Signed
open DeciSigma1.Satisfiability
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Semantics.SignSelection
theorem _root_.solution {ψ : List (LitT n (V × Bool))} (hc : FlipClosed ψ)
    (z : (V × Bool)) : SameShape (leastShape ψ z) (dual (leastShape ψ) z) := by
  intro π
  rw [signedDual_eq_flipV]
  exact (leastShape_flip_f hc z π).trans
    (normalize_constructor (fun _ => false) true (leastShape ψ (flipV z)) π).symm
end DeciSigma1.Semantics.SignSelection
