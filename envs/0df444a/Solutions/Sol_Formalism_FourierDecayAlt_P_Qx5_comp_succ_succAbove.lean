-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.comp_succ_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:00.579523+00:00
-- url     : https://prove2.me/submissions/6a8fff7e-1645-4546-aa46-e53cf0e2bf80

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp


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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {α : Type*} {t : ℕ} (b : Fin (t + 2) → α) (q : Fin (t + 1)) :
    (b ∘ q.succ.succAbove) ∘ Fin.succ = (b ∘ Fin.succ) ∘ q.succAbove := by
  funext k
  simp only [Function.comp, Fin.succ_succAbove_succ]
end Formalism.FourierDecayAlt.P.Qx5
