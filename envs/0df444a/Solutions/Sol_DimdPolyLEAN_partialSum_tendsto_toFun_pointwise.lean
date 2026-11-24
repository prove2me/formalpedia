-- Prove2me | solution 1 for DimdPolyLEAN.partialSum_tendsto_toFun_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:35:46.254494+00:00
-- url     : https://prove2.me/submissions/1ed4bf07-ea8a-469a-8930-4edc9cd0e4fb

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_summable_skappa_eval_mul
public import Theorems.Thm_DimdPolyLEAN_tendsto_box_atTop
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
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Filter.Tendsto (fun J : MultiIndex d => partialSum kappa U J z)
      Filter.atTop (nhds (toFun kappa U z)) := by
  simpa [partialSum, toFun, HasSum, SummationFilter.unconditional, Function.comp_def] using
    ((summable_skappa_eval_mul kappa U z).hasSum.comp (tendsto_box_atTop (d := d)))
end DimdPolyLEAN
