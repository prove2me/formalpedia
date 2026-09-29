-- Prove2me | solution 1 for DeligneSerre.charZero_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/2f5f56d5-3802-5fee-bf16-673e30d16357

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.CharZero.Defs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_charZero_quotient

theorem solution {T : Type*} [CommRing T] (𝔭 : Ideal T)
    (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) : CharZero (T ⧸ 𝔭) := by
  refine ⟨fun m n hmn => ?_⟩
  have h : algebraMap ℤ T ((m : ℤ) - (n : ℤ)) ∈ 𝔭 := by
    rw [map_sub]
    have hcast : ∀ k : ℕ, (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (k : ℤ)) = (k : T ⧸ 𝔭) := by
      intro k; push_cast; simp
    have hm : (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (m : ℤ)) =
        (Ideal.Quotient.mk 𝔭) (algebraMap ℤ T (n : ℤ)) := by
      rw [hcast m, hcast n, hmn]
    rwa [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem] at hm
  have := h𝔭 _ h
  omega

end S_DeligneSerre_charZero_quotient
end P2MW
export P2MW.S_DeligneSerre_charZero_quotient (solution)
