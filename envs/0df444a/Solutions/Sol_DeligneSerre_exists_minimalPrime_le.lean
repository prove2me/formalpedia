-- Prove2me | solution 1 for DeligneSerre.exists_minimalPrime_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/559d4e09-e77d-5528-995d-12a3602ff4f6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_minimalPrime_le

theorem solution {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
    (𝔪 : Ideal T) (h𝔪 : 𝔪.IsPrime) :
    ∃ 𝔭 ∈ minimalPrimes T, 𝔭 ≤ 𝔪 ∧ ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0 := by
  haveI := h𝔪
  haveI : 𝔪.LiesOver (𝔪.under ℤ) := ⟨rfl⟩
  haveI : (𝔪.under ℤ).IsPrime := Ideal.IsPrime.under ℤ 𝔪
  obtain ⟨P, hP𝔪, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal ℤ)) (q := 𝔪.under ℤ) 𝔪 bot_le
  haveI := hPprime
  obtain ⟨𝔭, h𝔭min, h𝔭P⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal T)) (J := P) bot_le
  refine ⟨𝔭, h𝔭min, h𝔭P.trans hP𝔪, fun n hn => ?_⟩
  have hnP : algebraMap ℤ T n ∈ P := h𝔭P hn
  have : n ∈ P.under ℤ := hnP
  rw [← hPover.over] at this
  simpa using this

end S_DeligneSerre_exists_minimalPrime_le
end P2MW
export P2MW.S_DeligneSerre_exists_minimalPrime_le (solution)
