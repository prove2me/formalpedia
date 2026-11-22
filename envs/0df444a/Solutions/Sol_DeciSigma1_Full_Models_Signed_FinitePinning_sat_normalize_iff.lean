-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.FinitePinning.sat_normalize_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:18:10.258005+00:00
-- url     : https://prove2.me/submissions/3e6edb11-524a-47aa-8ea1-a0b8ffb57993

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Constraints_sat_false
public import Theorems.Thm_DeciSigma1_Constraints_sat_iff_signed
attribute [local simp] DeciSigma1.Constraints.sat_false



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed DeciSigma1.Full.Models.Signed.FinitePinning
open DeciSigma1.Semantics
open DeciSigma1.Constraints
variable {n : ℕ} {V : Type*}
namespace DeciSigma1.Full.Models.Signed.FinitePinning
theorem _root_.solution (c : Fin n → Bool) (ρ : V → Semantics.Tree n)
    (Γ : List (LitT n V)) :
    SatT (fun _ => false) (normalized c ρ) (signed c Γ) ↔ SatT c ρ Γ :=
  (sat_false ..).trans (sat_iff_signed c ρ Γ).symm
end DeciSigma1.Full.Models.Signed.FinitePinning
