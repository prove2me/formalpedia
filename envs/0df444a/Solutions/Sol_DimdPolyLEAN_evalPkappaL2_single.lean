-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:50.983552+00:00
-- url     : https://prove2.me/submissions/87ce2bc3-4160-43f1-83f9-f0c76637a2f8

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_smul
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (alpha : Idx d) (c : ℂ) :
    evalPkappaL2 kappa (Finsupp.single alpha c : Pkappa d kappa) = c • PhiL2 kappa alpha := by
  have hsingle :
      (Finsupp.single alpha c : Pkappa d kappa) =
        c • (Finsupp.single alpha 1 : Pkappa d kappa) := by
    simp_all
  rw [hsingle, evalPkappaL2_smul hd kappa c]
  rfl
end DimdPolyLEAN
