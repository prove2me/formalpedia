-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.W_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:52.719504+00:00
-- url     : https://prove2.me/submissions/8fd08d14-7255-4ab0-a4fa-7898c6e86a18

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_smul

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
    ∀ g ∈ GV k r, W w (f - f₂) g = W w f g - W w f₂ g := by
  intro g hg
  have e : f - f₂ = f + ((-1 : ℂ) • f₂) := by
    funext x
    simp [sub_eq_add_neg]
  rw [e, W_add w hw hf (ckOn_smul (-1) hf₂) g hg, W_smul]
  simp [sub_eq_add_neg]
end Formalism.FourierDecayAlt.P.B4
