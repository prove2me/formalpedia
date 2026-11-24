-- Prove2me | solution 1 for DimdPolyLEAN.continuous_limit_of_locallyUniform_boxPartialSums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:11.242969+00:00
-- url     : https://prove2.me/submissions/2addb7d4-fcf0-4d58-83d3-a14e80aa3bf4

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_partialSum_continuous

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    {f : Cd d -> ℂ}
    (hlim : BoxPartialSumsLocallyUniformTo kappa U f) :
    Continuous f := by
  let _ := hd
  exact hlim.continuous <| Filter.Frequently.of_forall fun J =>
    partialSum_continuous hd kappa U J
end DimdPolyLEAN
