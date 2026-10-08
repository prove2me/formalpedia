-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_iUnion_nat_horizons
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T07:01:15.368002+00:00
-- url     : https://prove2.me/submissions/dcb5c3d9-b15f-4014-b24a-da640110b4d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical Set

theorem solution (σ : ENNReal) :
    paymentTimes σ = iUnion (fun n : ℕ => paymentTimes (min σ n)) := by
  ext t
  simp only [paymentTimes, mem_setOf_eq, mem_iUnion]
  constructor
  · rintro ⟨ht, h⟩
    rcases h with rfl | hlt
    · exact ⟨0, ht, Or.inl rfl⟩
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt ENNReal.ofReal_ne_top
      exact ⟨n, ht, Or.inr (lt_min hlt hn)⟩
  · rintro ⟨n, ht, h⟩
    refine ⟨ht, ?_⟩
    rcases h with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr (lt_of_lt_of_le hlt (min_le_left _ _))
