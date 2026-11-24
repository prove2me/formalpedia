-- Prove2me | solution 1 for DimdPolyLEAN.continuous_toFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:17.470458+00:00
-- url     : https://prove2.me/submissions/3171a620-1527-44cd-9baf-0bd598a06a1c

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_toFun_eq_boxLimit
public import Theorems.Thm_DimdPolyLEAN_continuous_limit_of_locallyUniform_boxPartialSums

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Continuous (toFun kappa U) :=
  continuous_limit_of_locallyUniform_boxPartialSums hd kappa U (toFun_eq_boxLimit hd kappa U)
end DimdPolyLEAN
