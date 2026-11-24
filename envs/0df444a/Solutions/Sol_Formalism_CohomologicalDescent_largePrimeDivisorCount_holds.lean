-- Prove2me | solution 1 for Formalism.CohomologicalDescent.largePrimeDivisorCount_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:41:34.041901+00:00
-- url     : https://prove2.me/submissions/59f556ef-858c-42c0-a620-2cda2d32b0fb

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Theorems.Thm_Formalism_CohomologicalDescent_eq_of_dvd_of_abs_lt_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution : PrimeCount := by
  intro L T P hL hT hP
  choose! f hfT hfd using fun l (hl : l ∈ P) => (hP l hl).2.2
  apply Finset.card_le_card_of_injOn f
  · intro l hl
    exact hfT l hl
  · intro l hl l' hl' heq
    have h1 := hT (f l) (hfT l hl)
    refine eq_of_dvd_of_abs_lt_sq hL h1.1 h1.2 (hP l hl).1 (hP l' hl').1 (hP l hl).2.1
      (hP l' hl').2.1 (hfd l hl) ?_
    rw [heq]
    exact hfd l' hl'
end Formalism.CohomologicalDescent
