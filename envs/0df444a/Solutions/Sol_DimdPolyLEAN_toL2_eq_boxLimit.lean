-- Prove2me | solution 1 for DimdPolyLEAN.toL2_eq_boxLimit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:38:24.557412+00:00
-- url     : https://prove2.me/submissions/212d70df-3737-4a39-85d0-6c73d455e30b

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_box_tendsto_tsum
public import Theorems.Thm_DimdPolyLEAN_l2_tsum_represents_toFun
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
    L2BoxPartialSumsTendTo kappa U (toL2 kappa U) := by
  classical
  let S : L2Tensor d := ∑' alpha : Idx d, coeffSkappa U alpha • PhiL2 kappa alpha
  have hL2 :
      Filter.Tendsto (fun J : MultiIndex d =>
          evalPkappaL2 kappa (truncateFinset (box J) U))
        Filter.atTop (nhds S) := by exact evalPkappaL2_box_tendsto_tsum hd kappa U
  have hrepS : IsTensorL2Rep S (toFun kappa U) := by
    exact l2_tsum_represents_toFun hd kappa U
  rcases hrepS with ⟨hmem, htoLp⟩
  have htoL2 : toL2 kappa U = S := by
    unfold toL2
    simp [hmem, htoLp]
  constructor
  · simpa [htoL2] using hL2
  · exact ⟨hmem, by simpa [htoL2] using htoLp⟩
end DimdPolyLEAN
