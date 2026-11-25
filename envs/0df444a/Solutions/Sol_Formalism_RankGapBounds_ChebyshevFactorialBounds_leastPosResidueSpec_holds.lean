-- Prove2me | solution 1 for Formalism.RankGapBounds.ChebyshevFactorialBounds.leastPosResidueSpec_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:19:38.795635+00:00
-- url     : https://prove2.me/submissions/bc9731b5-a20f-49aa-93e4-55f28a502941

import Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Finset
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.ChebyshevFactorialBounds
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
theorem _root_.solution : LeastResFacts := by
  intro a l hl
  unfold leastRes
  set S := {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ a - (d : ℤ)} with hS
  have hl' : (0 : ℤ) < l := by exact_mod_cast hl
  have h0 : 0 ≤ (a - 1) % (l : ℤ) := Int.emod_nonneg _ hl'.ne'
  have hlt0 : (a - 1) % (l : ℤ) < l := Int.emod_lt_of_pos _ hl'
  set r := ((a - 1) % (l : ℤ)).toNat with hr
  have hr' : (r : ℤ) = (a - 1) % (l : ℤ) := Int.toNat_of_nonneg h0
  have hmemd : r + 1 ∈ S := by
    refine ⟨by omega, ?_⟩
    have he : a - ((r + 1 : ℕ) : ℤ) = (l : ℤ) * ((a - 1) / l) := by
      have := Int.emod_def (a - 1) (l : ℤ)
      push_cast
      linarith
    rw [he]
    exact dvd_mul_right _ _
  have hmem := Nat.sInf_mem ⟨_, hmemd⟩
  have hle : sInf S ≤ r + 1 := Nat.sInf_le hmemd
  have hrl : r < l := by omega
  refine ⟨hmem.1, by omega, hmem.2, fun ha1 hal => ?_⟩
  set m := a.toNat with hm
  have hm' : (m : ℤ) = a := Int.toNat_of_nonneg (by omega)
  have hamem : m ∈ S := ⟨by omega, by rw [hm', sub_self]; exact dvd_zero _⟩
  have h1 : sInf S ≤ m := Nat.sInf_le hamem
  have h2 : m ≤ sInf S := by
    by_contra hlt'
    rw [not_le] at hlt'
    obtain ⟨k, hk⟩ := hmem.2
    have hpos : 0 < a - ((sInf S : ℕ) : ℤ) := by omega
    have hsmall : a - ((sInf S : ℕ) : ℤ) < l := by have := hmem.1; omega
    rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
    · nlinarith
    · rw [hk0, mul_zero] at hk
      omega
    · nlinarith
  omega
end Formalism.RankGapBounds.ChebyshevFactorialBounds
