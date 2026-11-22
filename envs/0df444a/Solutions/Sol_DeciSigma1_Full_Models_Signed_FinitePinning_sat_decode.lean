-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.FinitePinning.sat_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:23:03.469259+00:00
-- url     : https://prove2.me/submissions/3eec3eac-087c-43ab-8af0-71cefbe05c66

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Full_Models_Signed_FinitePinning_sat_normalize_iff
public import Theorems.Thm_DeciSigma1_Constraints_normalized_decoded


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Full.Models.Signed.FinitePinning
theorem _root_.solution (c : Fin n → Bool) {A : V × Bool → Semantics.Tree n}
    {Γ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c Γ))
    (hf : Constraints.Signed.dual A = A) : SatT c (decoded c A) Γ := by
  apply (sat_normalize_iff c _ Γ).mp
  rwa [normalized_decoded c hf]
end DeciSigma1.Full.Models.Signed.FinitePinning
