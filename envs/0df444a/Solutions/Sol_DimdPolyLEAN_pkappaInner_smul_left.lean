-- Prove2me | solution 1 for DimdPolyLEAN.pkappaInner_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:43:37.040899+00:00
-- url     : https://prove2.me/submissions/af524edd-32d1-4608-95a0-93625ee5ac73

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



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} {kappa : MultiIndex d} (c : ℂ)
    (Q F : Pkappa d kappa) :
    pkappaInner (c • Q) F = c * pkappaInner Q F := by
  by_cases hc : c = 0
  · subst c
    simp [pkappaInner]
  · unfold pkappaInner
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_smul_eq hc, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro alpha halpha
    simp [Finsupp.smul_apply, mul_assoc]
end DimdPolyLEAN
