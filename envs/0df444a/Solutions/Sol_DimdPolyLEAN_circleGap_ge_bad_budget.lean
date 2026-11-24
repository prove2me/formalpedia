-- Prove2me | solution 1 for DimdPolyLEAN.circleGap_ge_bad_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:23.843782+00:00
-- url     : https://prove2.me/submissions/403b7365-07f7-4885-ac9e-52cace3a2311

module
public import Definitions.Def_LeanPool_PhaseRetrieval_FourierParseval
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_HighFreqBandEstimate
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_SafeSquare
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_MissingMathlib_Poincare
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Order.Interval.Set.Union
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_FiniteBaseCircleEstimate

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution (D : Nat) :
    2 * circleBadConst D * circleGoodBudget D <= circleGap D := by
  unfold circleGap
  exact le_max_right 37 (2 * circleBadConst D * circleGoodBudget D)
end DimdPolyLEAN
