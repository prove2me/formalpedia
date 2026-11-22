-- Prove2me | solution 1 for DeciSigma1.Semantics.SignSelection.mix_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:27:10.750382+00:00
-- url     : https://prove2.me/submissions/207d4abe-1d05-407b-9173-5b75110ee9aa

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
theorem _root_.solution (c : Fin n → Bool) (p : Bool) (a b : Tree n) (h : SameShape a b)
    (π : List (Fin n)) :
    (mix c p a b h).fn π = if Bool.xor p (polarity c π) then b.fn π else a.fn π := rfl
end DeciSigma1.Semantics.SignSelection
