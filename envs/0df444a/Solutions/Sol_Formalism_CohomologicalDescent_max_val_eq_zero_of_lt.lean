-- Prove2me | solution 1 for Formalism.CohomologicalDescent.max_val_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:58.424872+00:00
-- url     : https://prove2.me/submissions/1cb4a137-c3c2-4397-ab0b-fb13b618d9b3

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ParamsWindow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution (l n : ℕ) (h : n < l) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n = 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hp : l.Prime
  · apply le_of_eq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hdf : l ∣ n.factorial := hd.trans ⟨i.factorial * (n - i).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hi']; ring⟩
    have := (Nat.Prime.dvd_factorial hp).mp hdf
    omega
  · exact (Nat.factorization_eq_zero_of_not_prime _ hp).le
end Formalism.CohomologicalDescent
