-- Prove2me | solution 1 for FreyPackage.not_p_dvd_padicValInt_two_freyCurveInt_discr
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/014ed213-f86f-5985-b684-198a9c979037

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_FLTPrelim_FreyPackage
import Theorems.Thm_FreyPackage_padicValInt_two_freyCurveInt_discr
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr

theorem solution (P : FreyPackage) : ¬ P.p ∣ padicValInt 2 P.freyCurveInt.Δ := by
  intro h
  have h8 : P.p ∣ 8 := by
    have h2 : P.p ∣ padicValInt 2 P.freyCurveInt.Δ + 8 :=
      ⟨2 * padicValInt 2 (P.a * P.b * P.c), by rw [P.padicValInt_two_freyCurveInt_discr]; ring⟩
    exact (Nat.dvd_add_right h).mp h2
  have h2 : P.p ∣ 2 := P.pp.dvd_of_dvd_pow (show P.p ∣ 2 ^ 3 by norm_num; exact h8)
  have := (Nat.prime_dvd_prime_iff_eq P.pp Nat.prime_two).mp h2
  have := P.hp5
  omega

end S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr
end P2MW
export P2MW.S_FreyPackage_not_p_dvd_padicValInt_two_freyCurveInt_discr (solution)
