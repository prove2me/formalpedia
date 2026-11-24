-- Prove2me | solution 1 for DimdPolyLEAN.circleBadConst_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:19.483451+00:00
-- url     : https://prove2.me/submissions/73c0e375-3e25-434f-9296-bbc1cca76fe4

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
theorem _root_.solution (D : Nat) : 1 <= circleBadConst D := by
  unfold circleBadConst
  exact le_max_left 1 (max (82 * D) (2 ^ D - 1))
end DimdPolyLEAN
