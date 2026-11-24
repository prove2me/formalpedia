-- Prove2me | solution 1 for Formalism.G0.det_divides
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:40.724283+00:00
-- url     : https://prove2.me/submissions/866e993a-47b8-4575-97a7-ef74a6c95c02

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
import Theorems.Thm_Formalism_G0_DetDividesP_red_of_valGE
import Theorems.Thm_Formalism_G0_DetDividesP_dvd_pow_of_red

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
namespace Formalism.G0
theorem _root_.solution : DetDivides := by
  intro K ι _ _ _ r vec S A d G th hA hAS hG hV hB
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h1 : detLetters (K := K) A = 1 := by
      unfold detLetters; exact Matrix.det_isEmpty
    rw [h1, one_pow]; exact one_dvd _
  · exact DetDividesP.dvd_pow_of_red hr A hA _ G
      (DetDividesP.red_of_valGE hr vec S A d G th hAS hG hV hB)
end Formalism.G0
