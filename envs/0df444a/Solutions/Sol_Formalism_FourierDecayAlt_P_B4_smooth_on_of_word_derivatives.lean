-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:41:01.474456+00:00
-- url     : https://prove2.me/submissions/79b863be-d43b-4e01-a678-9e28285df634

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_op
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_nil
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
theorem _root_.solution {f : Mat k r → E} (w : List (Bool × Mat k r)) (hw : AllLie w) :
    ∀ m : ℕ, CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((m : ℕ) : ℕ∞) (GV k r) (W w f) := by
  induction w with
  | nil =>
    intro m hm
    rw [W_nil]
    first
      | exact hm
      | simpa using hm
  | cons x w ih =>
    intro m hm
    rw [W_cons]
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hm' : CkOn ((m + 1 + w.length : ℕ) : ℕ∞) (GV k r) f := by
      rw [show m + 1 + w.length = m + (x :: w).length by simp only [List.length_cons]; omega]
      exact hm
    exact ckOn_op m x.1 (ih hw' (m + 1) hm') hx
end Formalism.FourierDecayAlt.P.B4
