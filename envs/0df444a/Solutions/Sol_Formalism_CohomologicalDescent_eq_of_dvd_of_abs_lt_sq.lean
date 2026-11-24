-- Prove2me | solution 1 for Formalism.CohomologicalDescent.eq_of_dvd_of_abs_lt_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:32:56.458889+00:00
-- url     : https://prove2.me/submissions/671e77c7-a4b7-422e-bd7b-8ea84eedd55d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence

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
theorem _root_.solution {L : ℝ} (hL : 0 ≤ L) {n : ℤ} (hn : n ≠ 0) (hnL : ((|n| : ℤ) : ℝ) < L ^ 2)
    {l l' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ)) (hLl' : L < (l' : ℝ))
    (hd : (l : ℤ) ∣ n) (hd' : (l' : ℤ) ∣ n) : l = l' := by
  by_contra hne
  have hcop : IsCoprime (l : ℤ) (l' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes hl hl').mpr hne
  have hmul : (l : ℤ) * l' ∣ |n| := by
    rw [dvd_abs]
    exact hcop.mul_dvd hd hd'
  have hle : (l : ℤ) * l' ≤ |n| := Int.le_of_dvd (abs_pos.mpr hn) hmul
  have hle' : (l : ℝ) * l' ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hle
  have hsq : L ^ 2 < (l : ℝ) * l' := by
    rw [sq]
    exact mul_lt_mul'' hLl hLl' hL hL
  linarith
end Formalism.CohomologicalDescent
