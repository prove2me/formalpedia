-- Prove2me | solution 1 for DeciSigma1.Full.Reduction.hasCountermodelIn_regularTop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:11.801616+00:00
-- url     : https://prove2.me/submissions/36e1e663-f997-4bbd-87fa-7913789e2a97

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
public import Theorems.Thm_DeciSigma1_Full_Reduction_hasCountermodelIn_true_of_hasCountermodelIn
public import Theorems.Thm_DeciSigma1_Full_Reduction_Realizes_seedConsistency
public import Theorems.Thm_DeciSigma1_Full_Reduction_SeedConsistency_regular_realizes
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
theorem _root_.solution [Finite V] :
    HasCountermodelIn RegularTop c Γ q ↔ HasCountermodelIn (fun _ => True) c Γ q := by
  classical
  let := Fintype.ofFinite V
  classical
  refine ⟨hasCountermodelIn_true_of_hasCountermodelIn, ?_⟩
  rintro ⟨ρ, _, hρ, hf⟩
  obtain ⟨m, W, hm⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hf
  obtain ⟨τ, hr, ht, hw⟩ :=
    (Realizes.seedConsistency ⟨ρ, hρ, hm⟩).regular_realizes ⟨ρ, hρ⟩
  exact ⟨τ, hr, ht, (failures_iff_exists_leaf_witnesses c τ q).mpr ⟨m, W, hw⟩⟩
end DeciSigma1.Full.Reduction
