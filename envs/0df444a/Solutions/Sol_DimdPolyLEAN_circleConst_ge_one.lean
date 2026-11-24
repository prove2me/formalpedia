-- Prove2me | solution 1 for DimdPolyLEAN.circleConst_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:33.324372+00:00
-- url     : https://prove2.me/submissions/a5bdd5ce-026a-4305-9af8-150ed1bd3df8

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
theorem _root_.solution (D : Nat) : 1 <= circleConst D := by
  dsimp [circleConst]
  have hgap : (1 : ℝ) <= ((circleGap D : Nat) : ℝ) := by exact_mod_cast circleGap_pos D
  linarith only [hgap, sq_nonneg (((circleGap D : Nat) : ℝ) - 1)]
end DimdPolyLEAN
