-- Prove2me | solution 1 for DimdPolyLEAN.finite_base_circle_estimate_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:24.67227+00:00
-- url     : https://prove2.me/submissions/66353af1-1c5a-4663-8030-ab8bc5a7b1a8

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
public import Theorems.Thm_DimdPolyLEAN_circleConst_pos
public import Theorems.Thm_DimdPolyLEAN_finite_base_circle_estimate

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution (D : Nat) :
    ∃ A : Nat, 1 <= A ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ {L N : Nat}, 1 <= L ->
          A * L <= N ->
          ∀ (q : Fin (D + 1) -> ℂ) (p : Fin L -> ℂ),
            circleL2Sq (bandPoly N p) <=
              C * defectSq (lowPoly q) (bandPoly N p) := by
  refine ⟨circleGap D, circleGap_pos D, circleConst D, circleConst_pos D, ?_⟩
  intro L N hL hsep q p
  exact finite_base_circle_estimate D hL hsep q p
end DimdPolyLEAN
