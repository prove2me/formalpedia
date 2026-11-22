-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.FinitePinning.sat_signDual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:22:59.634463+00:00
-- url     : https://prove2.me/submissions/5b507d63-6c94-4743-8b52-c1ef0a43d0c6

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_signedDual
attribute [local simp] DeciSigma1.Constraints.sat_false



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Full.Models.Signed.FinitePinning
theorem _root_.solution {c : Fin n → Bool} {A : V × Bool → Semantics.Tree n}
    {Γ : List (LitT n V)} (h : SatT (fun _ => false) A (signed c Γ)) :
    SatT (fun _ => false) (Constraints.Signed.dual A) (signed c Γ) :=
  (sat_false ..).mpr (sat_signedDual c ((sat_false ..).mp h))
end DeciSigma1.Full.Models.Signed.FinitePinning
