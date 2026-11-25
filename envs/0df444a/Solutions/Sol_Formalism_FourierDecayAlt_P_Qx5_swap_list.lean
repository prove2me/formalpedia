-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.swap_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:32.457403+00:00
-- url     : https://prove2.me/submissions/1c355d91-a3c0-4ff2-818a-1c5499daf3bf

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
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
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution {α : Type*} {t : ℕ} (a : Fin (t + 2) → α) (p : Fin (t + 2)) (l : Fin (t + 1)) :
    (a ∘ (p.succAbove l).succAbove) ∘ (l.predAbove p).succAbove = (a ∘ p.succAbove) ∘ l.succAbove := by
  funext k
  simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]
end Formalism.FourierDecayAlt.P.Qx5
