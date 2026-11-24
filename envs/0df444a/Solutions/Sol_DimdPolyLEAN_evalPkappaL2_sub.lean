-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:01.920022+00:00
-- url     : https://prove2.me/submissions/e17a6426-2807-46ba-b0ed-8be0d56d68f7

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_smul
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F G : Pkappa d kappa) :
    evalPkappaL2 kappa (F - G) = evalPkappaL2 kappa F - evalPkappaL2 kappa G := by
  rw [sub_eq_add_neg, evalPkappaL2_add hd kappa F (-G)]
  have hneg : evalPkappaL2 kappa (-G) = -evalPkappaL2 kappa G := by
    simpa using evalPkappaL2_smul hd kappa (-1 : ℂ) G
  rw [hneg]
  simp [sub_eq_add_neg]
end DimdPolyLEAN
