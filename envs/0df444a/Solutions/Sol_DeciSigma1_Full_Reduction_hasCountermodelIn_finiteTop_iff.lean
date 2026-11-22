-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_finiteTop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:39:23.893854+00:00
-- url     : https://prove2.me/submissions/dfcb271c-aa50-4db5-b7c7-0c02d896bbea

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_of_boundRealization
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_boundRealization_finiteTop


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}
namespace DeciSigma1.Full.Reduction
theorem _root_.solution :
    HasCountermodelIn FiniteTop c Γ q ↔
      Models.SatFin c Γ ∧ HasCountermodelIn (fun _ => True) c Γ q := by
  constructor
  · intro h
    obtain ⟨ρ, hc, hs, hf⟩ := h
    exact ⟨⟨ρ, hc, hs⟩, ρ, fun _ => trivial, hs, hf⟩
  · rintro ⟨hf, hc⟩
    exact hasCountermodelIn_of_boundRealization (Signed.boundRealization_finiteTop c Γ hf) hc
end DeciSigma1.Full.Reduction
