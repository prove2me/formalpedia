-- Prove2me | solution 1 for DimdPolyLEAN.phaseStability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:29.442441+00:00
-- url     : https://prove2.me/submissions/9e7e0330-10dd-41cd-a397-77eece6bd6cc

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_exists_phase_positivePhaseGauge
public import Theorems.Thm_DimdPolyLEAN_modulusDefect_phase_smul
public import Theorems.Thm_DimdPolyLEAN_positiveGaugeStability
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
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Pkappa d kappa,
        ∃ phase : ℂ, ‖phase‖ = 1 ∧
          phasedCoeffDistance F Q phase ≤ C_F * modulusDefect kappa F Q := by
  obtain ⟨C_F, hC_F_pos, hstable⟩ := positiveGaugeStability hd kappa F hF_norm
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q
  obtain ⟨phase, hphase, hpos⟩ := exists_phase_positivePhaseGauge F Q
  refine ⟨phase, hphase, ?_⟩
  have hbound := hstable (phase • Q) hpos
  simpa [phasedCoeffDistance, modulusDefect_phase_smul hd kappa F Q hphase] using hbound
end DimdPolyLEAN
