-- Prove2me | solution 1 for DimdPolyLEAN.modulusDefect_phase_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:27.560789+00:00
-- url     : https://prove2.me/submissions/6e91a181-31ba-4b71-b6cd-49c625fa3310

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_defect_sub_eq_modulusDefect
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_smul
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace DimdPolyLEAN
private theorem defect_phase_sub_eq_modulusDefect
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d)
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    defect F (phase • Q - F) = modulusDefect kappa F Q := by
  unfold defect modulusDefect
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  have heval : evalPkappa kappa (F + (phase • Q - F)) z = phase * evalPkappa kappa Q z := by
    have h1 := congrFun (evalPkappa_smul hd kappa phase Q) z
    simp_all
  rw [heval, norm_mul, hphase, one_mul]
end DimdPolyLEAN
end
end
end

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
    (F Q : Pkappa d kappa) {phase : ℂ} (hphase : ‖phase‖ = 1) :
    modulusDefect kappa F (phase • Q) = modulusDefect kappa F Q := by
  rw [← defect_sub_eq_modulusDefect hd kappa F (phase • Q),
    defect_phase_sub_eq_modulusDefect hd kappa F Q hphase]
end DimdPolyLEAN
