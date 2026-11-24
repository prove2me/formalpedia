-- Prove2me | solution 1 for DimdPolyLEAN.finite_coeff_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:01.379004+00:00
-- url     : https://prove2.me/submissions/d11f7cd8-6468-4ad0-b88b-b6ab5df22186

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
public import Theorems.Thm_DimdPolyLEAN_PhiL2_orthonormal
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa)
    (beta : Idx d) :
    coeffPkappa F beta = inner ℂ (PhiL2 kappa beta) (evalPkappaL2 kappa F) := by
  classical
  induction F using Finsupp.induction with
  | zero =>
      rw [coeffPkappa, evalPkappaL2_zero hd kappa]
      simp
  | single_add alpha c F halpha hc hF =>
      rw [evalPkappaL2_add hd kappa (Finsupp.single alpha c : Pkappa d kappa) F,
        evalPkappaL2_single hd kappa alpha c, inner_add_right, ← hF]
      by_cases hβα : beta = alpha
      · subst hβα
        rw [inner_smul_right, PhiL2_orthonormal hd kappa beta beta]
        simp [coeffPkappa]
      · simp [coeffPkappa, hβα, Finsupp.single_eq_of_ne hβα, inner_smul_right,
          PhiL2_orthonormal hd kappa]
end DimdPolyLEAN
