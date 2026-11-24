-- Prove2me | solution 1 for Formalism.Q3.kron_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:36.561846+00:00
-- url     : https://prove2.me/submissions/ee9b9f72-dcbd-41ec-884c-b35283169886

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementGroup
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_KroneckerMeaning

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
theorem _root_.solution (q p : ℕ) (hq4 : q % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo : q % 2 = 1 := by omega
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hpo)]
  have h := jacobiSym.quadratic_reciprocity_if hpo hqo
  rcases Nat.odd_mod_four_iff.mp hpo with h1 | h3
  · rw [χ₄_nat_one_mod_four h1, one_mul, ← h]
    simp [h1]
  · rw [χ₄_nat_three_mod_four h3, ← h]
    simp [h3, hq4]
end Formalism.Q3
