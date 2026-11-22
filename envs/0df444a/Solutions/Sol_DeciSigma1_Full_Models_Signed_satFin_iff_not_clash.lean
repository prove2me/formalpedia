-- Prove2me | solution 1 for DeciSigma1.Full.Models.Signed.satFin_iff_not_clash
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:08:02.727848+00:00
-- url     : https://prove2.me/submissions/1227d424-66e1-4205-82a0-4a9ab04fde51

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Automata
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_FiniteMedian
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
public import Theorems.Thm_DeciSigma1_Constraints_Ranked_Extension_satFin_iff
public import Theorems.Thm_DeciSigma1_Full_Models_satFin_iff_finite_assignment
public import Theorems.Thm_DeciSigma1_Satisfiability_satFin_iff
public import Theorems.Thm_DeciSigma1_Satisfiability_satFinite_iff_signed


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Models DeciSigma1.Full.Models.Signed
open DeciSigma1.Satisfiability DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n : ℕ}
namespace DeciSigma1.Full.Models.Signed
theorem _root_.solution {V : Type*} [Finite V]
    (c : Fin n → Bool) (Γ : List (LitT n V)) :
    SatFin c Γ ↔ ¬ LabelClash (signed c Γ) ∧ ¬ CycleClash (signed c Γ) :=
  (satFin_iff_finite_assignment c Γ).trans ((satFinite_iff_signed c Γ).trans satFin_iff)
end DeciSigma1.Full.Models.Signed
