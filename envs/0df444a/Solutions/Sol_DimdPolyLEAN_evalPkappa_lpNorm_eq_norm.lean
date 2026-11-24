-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappa_lpNorm_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:37.496426+00:00
-- url     : https://prove2.me/submissions/24cb4336-9e18-44ee-99e3-011a5484a156

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
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
private theorem gaussianL2Norm_eq_lpNorm
    {d : Nat} {α : Type*} [NormedAddCommGroup α]
     (F : Cd d → α)
    (hF : AEStronglyMeasurable F (gammaD d)) :
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F 2 (gammaD d) := by
  have htwo : (2 : NNReal) ≠ 0 := by norm_num
  have hlp := MeasureTheory.lpNorm_nnreal_eq_integral_norm_rpow
    (μ := gammaD d) (p := (2 : NNReal)) (f := F) htwo hF
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      lpNorm F (↑(2 : NNReal)) (gammaD d)
  rw [hlp]
  change
    Real.sqrt (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) =
      (∫ z : Cd d, ‖F z‖ ^ (2 : ℝ) ∂ gammaD d) ^ ((2 : ℝ)⁻¹)
  rw [Real.sqrt_eq_rpow]
  norm_num
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
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) (F : Pkappa d kappa) :
    lpNorm (evalPkappa kappa F) 2 (gammaD d) = ‖F‖ := by
  calc
    lpNorm (evalPkappa kappa F) 2 (gammaD d)
        = Real.sqrt (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) :=
          (gaussianL2Norm_eq_lpNorm (evalPkappa kappa F)
            (memLp_two_evalPkappa hd kappa F).aestronglyMeasurable).symm
    _ = ‖F‖ := by
          have hpow :
              (∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ (2 : ℝ) ∂ gammaD d) =
                ∫ z : Cd d, ‖evalPkappa kappa F z‖ ^ 2 ∂ gammaD d := by
            simp_all
          rw [hpow, evalPkappa_total_mass hd kappa F, Real.sqrt_sq_eq_abs]
          exact abs_of_nonneg (Real.sqrt_nonneg _)
end DimdPolyLEAN
