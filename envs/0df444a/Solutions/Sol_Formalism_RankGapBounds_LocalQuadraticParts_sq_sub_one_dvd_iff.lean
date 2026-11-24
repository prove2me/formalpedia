-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.sq_sub_one_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:59.762933+00:00
-- url     : https://prove2.me/submissions/a351bc04-1596-40d5-86ff-4c87cdd20c05

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (x : ℤ) (hx : Odd x) (m : ℕ) (hm : 1 ≤ m) :
    (2 : ℤ) ^ (m + 1) ∣ x ^ 2 - 1 ↔ ((2 : ℤ) ^ m ∣ x - 1 ∨ (2 : ℤ) ^ m ∣ x + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ := hx
  have e1 : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by ring
  have e2 : 2 * k + 1 - 1 = 2 * k := by ring
  have e3 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  have p1 : (2 : ℤ) ^ (n + 1 + 1) = 4 * 2 ^ n := by ring
  have p2 : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [e1, e2, e3, p1, p2, mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0),
    mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0), mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)]
  constructor
  · intro h
    rcases Int.even_or_odd k with ⟨b, hb⟩ | ⟨b, hb⟩
    · left
      have hc : IsCoprime ((2 : ℤ) ^ n) (k + 1) := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_right h
    · right
      have hc : IsCoprime ((2 : ℤ) ^ n) k := by
        apply IsCoprime.pow_left
        refine ⟨-b, 1, ?_⟩
        rw [hb]
        ring
      exact hc.dvd_of_dvd_mul_left h
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h _
    · exact dvd_mul_of_dvd_right h _
end Formalism.RankGapBounds.LocalQuadraticParts
