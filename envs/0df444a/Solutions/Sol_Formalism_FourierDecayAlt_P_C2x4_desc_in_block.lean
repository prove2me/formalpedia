-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.desc_in_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:55.468188+00:00
-- url     : https://prove2.me/submissions/ed968f79-4f83-4be3-a3aa-a53aee2a70e4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_cut_of_ascent
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_no_cut_between

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a b : Fin m)
    (hab : blk w a = blk w b) (j : Fin m) (hj1 : a ≤ j) (hj2 : j.val + 1 ≤ b.val) :
    ∃ h : j.val + 1 < m, w ⟨j.val + 1, h⟩ < w j := by
  have h : j.val + 1 < m := lt_of_le_of_lt hj2 b.isLt
  refine ⟨h, ?_⟩
  have hne : w ⟨j.val + 1, h⟩ ≠ w j := fun e => by
    have := congrArg Fin.val (w.injective e); simp at this
  rcases lt_or_gt_of_ne hne with h1 | h1
  · exact h1
  · exfalso
    exact no_cut_between w a b j hab hj1 (by rw [Fin.lt_def]; omega) (cut_of_ascent w d hC j h h1)
end Formalism.FourierDecayAlt.P.C2x4
