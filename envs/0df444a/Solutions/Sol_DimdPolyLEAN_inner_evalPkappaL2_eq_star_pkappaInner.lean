-- Prove2me | solution 1 for DimdPolyLEAN.inner_evalPkappaL2_eq_star_pkappaInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:25:41.909108+00:00
-- url     : https://prove2.me/submissions/46831f63-f8b6-42b3-9675-eea57cc21c18

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_CoefficientLimitRigidity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalCoercivity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_OrthogonalReduction_OrthogonalReduction
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_add
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_single
public import Theorems.Thm_DimdPolyLEAN_evalPkappaL2_zero
public import Theorems.Thm_DimdPolyLEAN_finite_coeff_recovery
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
    (G F : Pkappa d kappa) :
    inner ℂ (evalPkappaL2 kappa G) (evalPkappaL2 kappa F) = star (pkappaInner G F) := by
  classical
  induction G using Finsupp.induction with
  | zero =>
      simp [evalPkappaL2_zero hd kappa, pkappaInner]
  | single_add alpha c G halpha hc hG =>
      rw [evalPkappaL2_add hd kappa (Finsupp.single alpha c : Pkappa d kappa) G,
        evalPkappaL2_single hd kappa alpha c, inner_add_left, inner_smul_left, hG]
      have hcoeff := finite_coeff_recovery hd kappa F alpha
      rw [← hcoeff]
      unfold pkappaInner
      rw [Finsupp.sum_add_index]
      · rw [Finsupp.sum_single_index]
        · simp [coeffPkappa]
        · simp
      · simp_all
      · intro a ha b1 b2
        ring
end DimdPolyLEAN
