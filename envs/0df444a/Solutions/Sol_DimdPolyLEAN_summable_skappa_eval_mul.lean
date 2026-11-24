-- Prove2me | solution 1 for DimdPolyLEAN.summable_skappa_eval_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:39.280807+00:00
-- url     : https://prove2.me/submissions/c9c29724-e4bf-48d1-ab63-6adfe4d8a0ce

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_summable_sq_Phi_eval
public import Theorems.Thm_DimdPolyLEAN_summable_skappa_eval_mul_of_phi_sq

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) :=
  summable_skappa_eval_mul_of_phi_sq kappa U z (summable_sq_Phi_eval kappa z)
end DimdPolyLEAN
