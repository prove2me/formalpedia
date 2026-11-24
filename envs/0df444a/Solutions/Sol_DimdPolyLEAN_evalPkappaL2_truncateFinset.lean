-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_truncateFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:12.650855+00:00
-- url     : https://prove2.me/submissions/9be81c4f-d59c-4b79-800e-0fb478d90c61

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_zero
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_single
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa)
    (E : Finset (Idx d)) :
    evalPkappaL2 kappa (truncateFinset E U) =
      ∑ alpha ∈ E, coeffSkappa U alpha • PhiL2 kappa alpha := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      simp [truncateFinset, evalPkappaL2_zero hd kappa]
  | insert alpha E hnot hE =>
      have hE' :
          evalPkappaL2 kappa (∑ beta ∈ E, Finsupp.single beta (coeffSkappa U beta)) =
            ∑ beta ∈ E, coeffSkappa U beta • PhiL2 kappa beta := by exact hE
      simp [truncateFinset, Finset.sum_insert hnot, evalPkappaL2_add hd kappa,
        evalPkappaL2_single hd kappa, hE']
end DimdPolyLEAN
