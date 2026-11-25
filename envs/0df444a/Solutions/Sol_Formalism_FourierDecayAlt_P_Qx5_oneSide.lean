-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.oneSide
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:27:26.385967+00:00
-- url     : https://prove2.me/submissions/262124b0-011c-495b-a710-1883f1fda035

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_oneSide_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_skip_one_eq_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [AddCommGroup X] [Module ℂ X]
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution : ∀ (n : ℕ) (α β : Fin n → ℂ) (H : (Fin (n - 2) → Fin n) → X),
    ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (skip1 i p)) •
        H (skip1 i ∘ skip1 p) =
      ∑ i : Fin n, ∑ i' : Fin n,
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0
  | 0, _, _, _ => by simp
  | 1, _, _, _ => by
    have : ∀ i i' : Fin 1, ¬ i < i' := fun i i' => by rw [Subsingleton.elim i i']; exact lt_irrefl _
    simp [this]
  | M + 2, α, β, H => by
    have h := oneSide_succ M α β H
    have e1 : ∀ i : Fin (M + 2), (skip1 i : Fin (M + 1) → Fin (M + 2)) = i.succAbove := Qx6.skip_one_eq_succAbove
    have e2 : ∀ p : Fin (M + 1), (skip1 p : Fin M → Fin (M + 1)) = p.succAbove := Qx6.skip_one_eq_succAbove
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    show ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β ((skip1 i : Fin (M + 1) → Fin (M + 2)) p)) •
      H ((skip1 i : Fin (M + 1) → Fin (M + 2)) ∘ (skip1 p : Fin M → Fin (M + 1))) = _
    rw [e1, e2]
end Formalism.FourierDecayAlt.P.Qx5
