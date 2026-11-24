-- Prove2me | solution 1 for DimdPolyLEAN.exists_phase_positivePhaseGauge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:44.380038+00:00
-- url     : https://prove2.me/submissions/9346c3be-b41d-47b5-ab6c-59e28e46a389

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_pkappaInner_smul_left
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
    {d : Nat} {kappa : MultiIndex d} (F Q : Pkappa d kappa) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧ positivePhaseGauge F (phase • Q) := by
  let β : ℂ := pkappaInner Q F
  rcases Complex.exists_norm_eq_mul_self β with ⟨phase, hphase, hphaseβ⟩
  refine ⟨phase, hphase, ?_⟩
  have hinner : pkappaInner (phase • Q) F = ((‖β‖ : ℝ) : ℂ) := by
    rw [pkappaInner_smul_left, hphaseβ]
  constructor
  · rw [hinner]
    simp
  · rw [hinner]
    simp
end DimdPolyLEAN
