-- Prove2me | solution 1 for DimdPolyLEAN.evalPkappaL2_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:44:46.11153+00:00
-- url     : https://prove2.me/submissions/2e6b718c-6313-4f41-957c-cd2763242e87

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappa_lpNorm_eq_norm
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_eq_toLp


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
    ‖evalPkappaL2 kappa F‖ = ‖F‖ := by
  rw [evalPkappaL2_eq_toLp hd kappa F,
    MeasureTheory.Lp.norm_toLp,
    MeasureTheory.toReal_eLpNorm (memLp_two_evalPkappa hd kappa F).aestronglyMeasurable]
  exact evalPkappa_lpNorm_eq_norm hd kappa F
end DimdPolyLEAN
