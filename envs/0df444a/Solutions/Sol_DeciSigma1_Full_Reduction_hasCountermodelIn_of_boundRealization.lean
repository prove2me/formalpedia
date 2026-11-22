-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_of_boundRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:36:45.406149+00:00
-- url     : https://prove2.me/submissions/e7913cd3-99b9-40ba-82ce-e21a27a4e295

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Theorems.Thm_DeciSigma1_Full_Reduction_realize_observations
public import Theorems.Thm_DeciSigma1_Full_Reduction_countermodelObservations_holds
public import Theorems.Thm_DeciSigma1_Full_Models_PrefixPair_realize_observations
public import Theorems.Thm_DeciSigma1_Full_failures_iff_exists_leaf_witnesses


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
    (h : Signed.BoundRealization C c Γ) (hc : HasCountermodelIn (fun _ => True) c Γ q) :
    HasCountermodelIn C c Γ q := by
  obtain ⟨ρ, _, hs, hf⟩ := hc
  obtain ⟨m, W, hm⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hf
  obtain ⟨τ, ht, hsτ, ho⟩ := realize_observations h (countermodelObservations q m W)
    ⟨ρ, hs, (countermodelObservations_holds ρ m W).mpr hm⟩
  exact ⟨τ, ht, hsτ, (failures_iff_exists_leaf_witnesses c τ q).mpr
    ⟨m, W, (countermodelObservations_holds τ m W).mp ho⟩⟩
end DeciSigma1.Full.Reduction
