-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_dl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:58.015709+00:00
-- url     : https://prove2.me/submissions/3611bf58-a685-4f6e-ba45-855e9e756417

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_dl

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
theorem _root_.solution (t : ℝ × ℝ) (h1 : t.1 ≠ 0) (h2 : t.2 ≠ 0) (w : List (Bool × Mat k r)) (f : Mat k r → E) :
    W w (dl t f) = dl t (W (w.map (adj t)) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    rw [W_cons, ih, op_dl t h1 h2, List.map_cons, W_cons]
    try rfl
end Formalism.FourierDecayAlt.P.B4
