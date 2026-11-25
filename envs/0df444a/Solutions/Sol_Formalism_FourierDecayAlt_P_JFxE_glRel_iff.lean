-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.glRel_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:54.789841+00:00
-- url     : https://prove2.me/submissions/12b16fd6-d8b7-46c2-b8dd-9384f18903da

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (E : Fin n → Fin n → A) : GlRel E ↔ ∀ a b c d, rel E a b c d = 0 := by
  unfold GlRel rel
  constructor
  · intro h a b c d; rw [h a b c d, sub_self]
  · intro h a b c d; exact sub_eq_zero.mp (h a b c d)
end Formalism.FourierDecayAlt.P.JFxE
