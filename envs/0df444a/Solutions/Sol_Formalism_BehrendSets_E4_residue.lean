-- Prove2me | solution 1 for Formalism.BehrendSets.E4.residue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:22:20.70316+00:00
-- url     : https://prove2.me/submissions/a3e2be19-be7b-4360-bc0f-6dd7a2ff79ca

import Mathlib
import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_ProbEqSumIte
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_Select
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_MemWindowIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.BehrendSets Formalism.BehrendSets.E4
open Formalism.BehrendSets Formalism.BehrendSets.Rand
variable {α : Type} [DecidableEq α]
namespace Formalism.BehrendSets.E4
theorem _root_.solution (o j i : ℕ) (hj : j < o) (hd : o ∣ j + i) : (o - i % o) % o = j := by
  have ho : 0 < o := by omega
  have hr : i % o < o := Nat.mod_lt _ ho
  have h0 : (j + i % o) % o = 0 := by
    rw [Nat.add_mod_mod]
    exact Nat.mod_eq_zero_of_dvd hd
  by_cases hlt : j + i % o < o
  · rw [Nat.mod_eq_of_lt hlt] at h0
    have hi0 : i % o = 0 := by omega
    rw [hi0, Nat.sub_zero, Nat.mod_self]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
end Formalism.BehrendSets.E4
