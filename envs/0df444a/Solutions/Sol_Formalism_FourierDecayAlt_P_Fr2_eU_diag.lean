-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr2.eU_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:25.177637+00:00
-- url     : https://prove2.me/submissions/358f5eea-9f47-4b28-befe-918879109bd0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Interlace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleRecOfAdmissibleWord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Finset Formalism.FourierDecayAlt.I Formalism.FourierDecayAlt.P.Interlace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr2
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr2
theorem _root_.solution (a : S) (i : Fin 2) :
    (eU a i i : SlopeTestRemainingChoices S A) = Matrix.diagonal (fun e => if e a = i then 1 else 0) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy; simp [eU]
  · have : ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro ⟨h1, h2, h3⟩
      apply hxy; funext b
      by_cases hb : b = a
      · subst hb; rw [h1, h2]
      · exact h3 b hb
    simp [eU, Matrix.diagonal_apply_ne _ hxy, this]
end Formalism.FourierDecayAlt.P.Fr2
