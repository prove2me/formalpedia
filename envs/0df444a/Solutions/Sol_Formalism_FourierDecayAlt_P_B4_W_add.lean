-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:00:43.376254+00:00
-- url     : https://prove2.me/submissions/2f3f964a-910d-4b05-8c9f-e0ec47b3cbd5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_cons
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_smooth_on_of_word_derivatives

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
    (hf : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f) (hf₂ : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂) :
    ∀ g ∈ GV k r, W w (f + f₂) g = W w f g + W w f₂ g := by
  induction w with
  | nil => intro g _; rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x (by simp)
    have hw' : AllLie w := fun y hy => hw y (by simp [hy])
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf
    have hf₂' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf₂
    have g1 : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf
    have g2 : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f₂ :=
      ckOn_mono (by simp only [List.length_cons]; omega) hf₂
    rw [W_cons, W_cons, W_cons]
    rw [op_congr (f₂ := W w f + W w f₂) x.1 hx (ih hw' hf' hf₂') g hg]
    exact op_add x.1 hx (smooth_on_of_word_derivatives w hw' 1 g1) (smooth_on_of_word_derivatives w hw' 1 g2) hg
end Formalism.FourierDecayAlt.P.B4
