-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr11.eU_same
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:53.909288+00:00
-- url     : https://prove2.me/submissions/967339a2-37b5-4249-83bf-d2aa02f4999a

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ResidueForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr11
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
noncomputable section
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr11
theorem _root_.solution (a : S) (i : Fin 2) : (eU a i i : SlopeTestRemainingChoices S A) = dg (fun e => if e a = i then 1 else 0) := by
  apply Matrix.ext
  intro x y
  simp only [eU, dg, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hx : x a = i <;> simp [hx]
  · have hn : ¬ (x a = i ∧ y a = i ∧ ∀ b, b ≠ a → x b = y b) := by
      rintro ⟨h1, h2, h3⟩
      apply hxy
      funext b
      by_cases hb : b = a
      · subst hb
        rw [h1, h2]
      · exact h3 b hb
    rw [if_neg hn, if_neg hxy]
end Formalism.FourierDecayAlt.P.Fr11
