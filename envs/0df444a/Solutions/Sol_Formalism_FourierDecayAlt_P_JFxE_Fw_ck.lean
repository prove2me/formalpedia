-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.Fw_ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:53:55.614974+00:00
-- url     : https://prove2.me/submissions/380fb3ad-307e-443b-8a36-9cb998b05041

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RepIntCastMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (hC : HC Eop) : ∀ (w : List (Ix k r)) (m : ℕ) (f : Mat k r → E),
    CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Fw Eop w f) := by
  intro w
  induction w with
  | nil => intro m f hf; simpa [Fw] using hf
  | cons x w ih =>
    intro m f hf
    have h1 : CkOn (((m + 1) + w.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : (m + 1) + w.length = m + (x :: w).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact hC x.1 x.2 m _ (ih (m + 1) f h1)
end Formalism.FourierDecayAlt.P.JFxE
