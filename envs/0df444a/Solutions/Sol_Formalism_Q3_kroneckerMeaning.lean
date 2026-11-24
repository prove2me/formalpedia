-- Prove2me | solution 1 for Formalism.Q3.kroneckerMeaning
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:34:11.832456+00:00
-- url     : https://prove2.me/submissions/95dd664c-4788-4f55-b4ad-ea0300b8746f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning
import Theorems.Thm_Formalism_Q3_kron_odd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.Q3
open ZMod
namespace Formalism.Q3
theorem _root_.solution : KroneckerMeaning := by
  intro q hq hq4
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  refine ⟨fun p hp hp2 _ => kron_odd q p hq4 hp hp2, ?_, ?_⟩
  · unfold chiQ
    rw [jacobiSym.at_two hqo, χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega)]
    by_cases h8 : q % 8 = 7
    · rw [if_pos (Or.inr h8)]; simp [h8]
    · rw [if_neg (by omega)]; simp [h8]
  · unfold chiQ
    rw [jacobiSym.at_neg_one hqo, χ₄_nat_three_mod_four hq4]
end Formalism.Q3
