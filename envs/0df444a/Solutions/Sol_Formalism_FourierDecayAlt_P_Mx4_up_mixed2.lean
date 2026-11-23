-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.up_mixed2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:14.990863+00:00
-- url     : https://prove2.me/submissions/46a4dfa1-9204-4cec-8945-6f5bf2c5fad8

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (l j : ℕ) (hjl : j ≠ l) (π π2 π3 : Ty P) (h1 : Up P l π3 π) (h2 : Up P j π3 π2) :
    ∃ π1, Up P j π π1 ∧ Up P l π2 π1 := by
  refine ⟨fun i => if (i : ℕ) + 1 = j then π2 i else π i, fun i => ?_, fun i => ?_⟩
  all_goals
    have a := h1 i
    have b := h2 i
    by_cases hj : (i : ℕ) + 1 = j
    · have hl : (i : ℕ) + 1 ≠ l := fun h => hjl (hj.symm.trans h)
      simp only [if_pos hj, if_neg hl] at a b ⊢; omega
    · by_cases hl : (i : ℕ) + 1 = l
      · simp only [if_neg hj, if_pos hl] at a b ⊢; omega
      · simp only [if_neg hj, if_neg hl] at a b ⊢; omega
end Formalism.FourierDecayAlt.P.Mx4
