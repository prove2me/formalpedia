-- Prove2me | solution 1 for DimdPolyLEAN.summable_skappa_eval_mul_of_phi_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:42.720742+00:00
-- url     : https://prove2.me/submissions/2b49c491-3537-484f-830a-f0ec01c2c212

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite1Dimd_ProductBasisAndAnnuli
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermitek_TrueLevelBasis
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (kappa : MultiIndex d) (U : Skappa d kappa) (z : Cd d)
    (hPhi : Summable (fun alpha : Idx d => ‖Phi kappa alpha z‖ ^ 2)) :
    Summable (fun alpha : Idx d => coeffSkappa U alpha * Phi kappa alpha z) := by
  have hU : Summable (fun alpha : Idx d => ‖coeffSkappa U alpha‖ ^ 2) := by
    exact U.summable_norm_sq
  refine Summable.of_norm_bounded
    (g := fun alpha : Idx d =>
      (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2)
    ((hU.add hPhi).div_const 2) ?_
  intro alpha
  have hmul :
      ‖coeffSkappa U alpha * Phi kappa alpha z‖ <=
        ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ :=
    norm_mul_le _ _
  have hsq :
      ‖coeffSkappa U alpha‖ * ‖Phi kappa alpha z‖ <=
        (‖coeffSkappa U alpha‖ ^ 2 + ‖Phi kappa alpha z‖ ^ 2) / 2 := by
    nlinarith only [sq_nonneg (‖coeffSkappa U alpha‖ - ‖Phi kappa alpha z‖)]
  exact le_trans hmul hsq
end DimdPolyLEAN
