-- Prove2me | solution 1 for DimdPolyLEAN.summable_PhiL2_coeff_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:34:57.444892+00:00
-- url     : https://prove2.me/submissions/f0257960-9765-4b99-b4e5-e28ebcb5faf8

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Theorems.Thm_DimdPolyLEAN_PhiL2_orthonormal_family

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (U : Skappa d kappa) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha • PhiL2 kappa alpha) := by
  classical
  let hOrthonormal := PhiL2_orthonormal_family hd kappa
  have hOrthogonalFamily := hOrthonormal.orthogonalFamily
  have hcoeff : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    exact U.summable_norm_sq
  exact
    (hOrthogonalFamily.summable_iff_norm_sq_summable
      (fun alpha : Idx d => coeffSkappa U alpha)).2 hcoeff
end DimdPolyLEAN
