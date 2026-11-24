-- Prove2me | solution 1 for DimdPolyLEAN.thirty_two_le_circleConst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:36.594692+00:00
-- url     : https://prove2.me/submissions/e0c267ec-bae6-49e2-9070-753b8979e04f

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
public import Theorems.Thm_DimdPolyLEAN_circleGap_pos

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution (D : Nat) : (32 : ℝ) <= circleConst D := by
  dsimp [circleConst]
  have hgap : (1 : ℝ) <= ((circleGap D : Nat) : ℝ) := by exact_mod_cast circleGap_pos D
  linarith only [hgap, sq_nonneg (((circleGap D : Nat) : ℝ) - 1)]
end DimdPolyLEAN
