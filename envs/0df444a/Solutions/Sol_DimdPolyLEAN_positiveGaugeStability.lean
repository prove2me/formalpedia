-- Prove2me | solution 1 for DimdPolyLEAN.positiveGaugeStability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:31.088425+00:00
-- url     : https://prove2.me/submissions/a9dead83-f11c-4892-b1c2-ac40b55c66a6

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_defect_sub_eq_modulusDefect
public import Theorems.Thm_DimdPolyLEAN_positiveGauge_coercivity
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
private theorem pkappa_ne_zero_of_norm_eq_one
    {d : Nat} {kappa : MultiIndex d} {F : Pkappa d kappa} (hF_norm : ‖F‖ = 1) :
    F ≠ 0 := by
  intro hF_zero
  subst F
  have hzero : ‖(0 : Pkappa d kappa)‖ = 0 := by
    change
      Real.sqrt
          (Finset.sum (0 : Pkappa d kappa).support
            (fun alpha => ‖(0 : Pkappa d kappa) alpha‖ ^ 2)) = 0
    simp
  simp_all
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
    (F : Pkappa d kappa) (hF_norm : ‖F‖ = 1) :
    ∃ C_F : ℝ, 0 < C_F ∧
      ∀ Q : Pkappa d kappa,
        positivePhaseGauge F Q ->
          ‖Q - F‖ ≤ C_F * modulusDefect kappa F Q := by
  have hF_ne : F ≠ 0 := pkappa_ne_zero_of_norm_eq_one hF_norm
  obtain ⟨C_F, hC_F_pos, hstable⟩ :=
    positiveGauge_coercivity hd kappa F hF_ne hF_norm
  refine ⟨C_F, hC_F_pos, ?_⟩
  intro Q hposQ
  let G : Pkappa d kappa := Q - F
  have hposG : positivePhaseGauge F (F + G) := by
    simpa [G, add_comm, add_left_comm, add_assoc] using hposQ
  have hbound := hstable G hposG
  simpa [G, defect_sub_eq_modulusDefect hd kappa F Q] using hbound
end DimdPolyLEAN
