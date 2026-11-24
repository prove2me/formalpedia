-- Prove2me | solution 1 for DimdPolyLEAN.skappa_ext_of_toFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:36.320707+00:00
-- url     : https://prove2.me/submissions/300eaf35-46d9-4ee4-8121-2a62b29a0974

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_coeff_recovery
public import Theorems.Thm_DimdPolyLEAN_toL2_eq_of_toFun_eq
public import Theorems.Thm_DimdPolyLEAN_skappa_ext_of_coeff_eq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) {kappa : MultiIndex d} {U V : Skappa d kappa}
    (h : ∀ z, toFun kappa U z = toFun kappa V z) :
    U = V := by
  apply skappa_ext_of_coeff_eq
  intro beta
  calc
    coeffSkappa U beta = inner ℂ (PhiL2 kappa beta) (toL2 kappa U) := coeff_recovery hd kappa U beta
    _ = inner ℂ (PhiL2 kappa beta) (toL2 kappa V) := by rw [toL2_eq_of_toFun_eq hd h]
    _ = coeffSkappa V beta := (coeff_recovery hd kappa V beta).symm
end DimdPolyLEAN
