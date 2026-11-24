-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.dLR_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:19:22.859489+00:00
-- url     : https://prove2.me/submissions/65f1d7ff-ebfb-4f6a-928b-370f495cd5f6

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_true
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_false
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_append

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
theorem _root_.solution (u v : List (Mat k r)) (f : Mat k r → E) : dLR u v f = W (lr u v) f := by
  have hv : ∀ v : List (Mat k r), Rw v f = W (v.map fun X => (false, X)) f := by
    intro v
    induction v with
    | nil => rfl
    | cons X v ih =>
      rw [List.map_cons, W_cons, ← ih, op_false]
      rfl
  have hu : ∀ (u : List (Mat k r)) (F : Mat k r → E), u.foldr LdV F = W (u.map fun X => (true, X)) F := by
    intro u F
    induction u with
    | nil => rfl
    | cons X u ih =>
      rw [List.map_cons, W_cons, ← ih, op_true]
      rfl
  unfold lr
  rw [W_append, ← hv, ← hu]
  rfl
end Formalism.FourierDecayAlt.P.B4
