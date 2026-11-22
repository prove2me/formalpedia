-- Prove2me | solution 1 for Formalism.G0.ChoiceOfTopsP.term_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:39:58.329385+00:00
-- url     : https://prove2.me/submissions/e7c45417-6cca-4aa4-bc07-1b9123f8b7a9

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ChoiceOfTops

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.G0
open Formalism.G0.ChoiceOfTopsP
namespace Formalism.G0.ChoiceOfTopsP
theorem _root_.solution (p a b c d : Prop) {_ : Decidable p} {_ : Decidable a} {_ : Decidable b}
    {_ : Decidable c} {_ : Decidable d} (w : ℝ) (hw : 0 ≤ w) (h : p → a ∨ b ∨ c ∨ d) :
    (if p then w else 0) ≤
      (if a then w else 0) + (if b then w else 0) + (if c then w else 0) + (if d then w else 0) := by
  by_cases hp : p
  · rcases h hp with h' | h' | h' | h' <;>
      split_ifs <;> linarith
  · split_ifs <;> linarith
end Formalism.G0.ChoiceOfTopsP
