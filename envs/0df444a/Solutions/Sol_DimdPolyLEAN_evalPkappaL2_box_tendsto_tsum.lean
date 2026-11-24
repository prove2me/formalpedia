-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_box_tendsto_tsum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:54.2211+00:00
-- url     : https://prove2.me/submissions/dedd1d46-6b12-4bdf-81fa-85b56a23c7e2

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_tendsto_box_atTop
public import Theorems.Thm_DimdPolyLEAN_summable_PhiL2_coeff_smul
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_truncateFinset
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Filter.Tendsto (fun J : MultiIndex d =>
        evalPkappaL2 kappa (truncateFinset (box J) U))
      Filter.atTop
      (nhds (∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha)) := by
  have hsummable := summable_PhiL2_coeff_smul hd kappa U
  simpa [HasSum, SummationFilter.unconditional, evalPkappaL2_truncateFinset hd kappa U,
    Function.comp_def] using
    hsummable.hasSum.comp (tendsto_box_atTop (d := d))
end DimdPolyLEAN
