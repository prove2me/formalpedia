-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:59:57.597389+00:00
-- url     : https://prove2.me/submissions/42de980b-0f06-43d3-adfa-54f1f4189939

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution {f f₂ : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w)
    (h : ∀ g ∈ GV k r, f g = f₂ g) : ∀ g ∈ GV k r, W w f g = W w f₂ g := by
  induction w with
  | nil => exact h
  | cons x w ih =>
    intro g hg
    rw [W_cons, W_cons]
    exact op_congr x.1 (hw x (by simp)) (ih (fun y hy => hw y (by simp [hy]))) g hg
end Formalism.FourierDecayAlt.P.B4
