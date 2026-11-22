-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.select_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:29:26.271802+00:00
-- url     : https://prove2.me/submissions/5929eb53-df9b-4cbc-ba29-8cc4d857b398

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
theorem _root_.solution (c : Fin n → Bool) (B : (V × Bool) → Tree n)
    (h : ∀ z, SameShape (B z) (dual B z)) (z : (V × Bool)) (π : List (Fin n)) :
    (select c B h z).fn π =
      if Bool.xor (sign z) (polarity c π) then (dual B z).fn π else (B z).fn π := rfl
end DeciSigma1.Semantics.SignSelection
