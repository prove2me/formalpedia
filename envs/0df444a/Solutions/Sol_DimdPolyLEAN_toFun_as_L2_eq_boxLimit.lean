-- Prove2me | solution 1 for DimdPolyLEAN.toFun_as_L2_eq_boxLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:39:41.062835+00:00
-- url     : https://prove2.me/submissions/b66be7a7-3bfb-4e68-9288-50bb24b0cf90

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_toFun_eq_boxLimit
public import Theorems.Thm_DimdPolyLEAN_toL2_eq_boxLimit

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    IsTensorL2Rep (toL2 kappa U) (toFun kappa U) := by
  let _ := hd
  let _ := toFun_eq_boxLimit hd kappa U
  exact (toL2_eq_boxLimit hd kappa U).2
end DimdPolyLEAN
