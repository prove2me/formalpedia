-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_true_of_hasCountermodelIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:28.925133+00:00
-- url     : https://prove2.me/submissions/09ae3c08-d1ca-4aad-b42d-9cd74f41a93d

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution {C : Semantics.Tree n → Prop}
    (h : HasCountermodelIn C c Γ q) :
    HasCountermodelIn (fun _ => True) c Γ q := by
  obtain ⟨ρ, _, hs, hf⟩ := h
  exact ⟨ρ, fun _ => trivial, hs, hf⟩
end DeciSigma1.Full.Reduction
