-- Prove2me | solution 2 for Devaney.hasPrimePeriod_of_iterate_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:43:21.36609+00:00
-- url     : https://prove2.me/submissions/2ffeefcc-b3eb-41eb-9d79-4de745846df6

import Mathlib
import Definitions.Def_Devaney_sarkovskii

open Devaney

namespace Aux

theorem hpp_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (h : HasPrimePeriod f x n) :
    Function.minimalPeriod f x = n := by
  obtain ⟨hn, hfix, hmin⟩ := h
  have hper : Function.IsPeriodicPt f n x := hfix
  have hmem : x ∈ Function.periodicPts f := ⟨n, hn, hper⟩
  have hpos : 0 < Function.minimalPeriod f x :=
    Function.minimalPeriod_pos_of_mem_periodicPts hmem
  have hle : Function.minimalPeriod f x ≤ n := hper.minimalPeriod_le hn
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact absurd (Function.isPeriodicPt_minimalPeriod f x) (hmin _ hpos hlt)
  · exact heq

theorem hpp_of_minimalPeriod {f : ℝ → ℝ} {x : ℝ} {n : ℕ} (hn : 0 < n)
    (h : Function.minimalPeriod f x = n) : HasPrimePeriod f x n := by
  refine ⟨hn, ?_, ?_⟩
  · have := Function.isPeriodicPt_minimalPeriod f x
    rw [h] at this; exact this
  · intro k hk hkn hfx
    have hp : Function.IsPeriodicPt f k x := hfx
    have := hp.minimalPeriod_le hk
    rw [h] at this; omega

end Aux

theorem solution (f : ℝ → ℝ) (y : ℝ) (M j : ℕ) (hj : 2 ∣ j)
    (h : HasPrimePeriod (f^[2 ^ M]) y j) : HasPrimePeriod f y (2 ^ M * j) := by
  have hj0 : 0 < j := h.1
  have hK : (2:ℕ) ^ M ≠ 0 := by positivity
  have hper : Function.IsPeriodicPt f (2 ^ M * j) y := by
    have h1 : Function.IsPeriodicPt (f^[2 ^ M]) j y := h.2.1
    have h2 : (f^[2 ^ M])^[j] y = y := h1
    rw [← Function.iterate_mul] at h2
    exact h2
  have hdiv : j = Function.minimalPeriod f y / Nat.gcd (Function.minimalPeriod f y) (2 ^ M) :=
    (Aux.hpp_minimalPeriod h).symm.trans (Function.minimalPeriod_iterate_eq_div_gcd hK)
  have hgN : Nat.gcd (Function.minimalPeriod f y) (2 ^ M) ∣ Function.minimalPeriod f y :=
    Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (Function.minimalPeriod f y) (2 ^ M) ∣ 2 ^ M := Nat.gcd_dvd_right _ _
  obtain ⟨e, hle, hge⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg2
  have hNgj : Function.minimalPeriod f y = Nat.gcd (Function.minimalPeriod f y) (2 ^ M) * j := by
    rw [hdiv]; exact (Nat.mul_div_cancel' hgN).symm
  have heM : e = M := by
    by_contra hne
    obtain ⟨t, ht⟩ := hj
    have h1 : (2:ℕ) ^ (e + 1) ∣ Function.minimalPeriod f y := by
      refine ⟨t, ?_⟩
      rw [hNgj, hge, ht, pow_succ]; ring
    have h2 : (2:ℕ) ^ (e + 1) ∣ 2 ^ M := pow_dvd_pow 2 (by omega)
    have h3 := Nat.dvd_gcd h1 h2
    rw [hge] at h3
    have h4 := Nat.le_of_dvd (by positivity) h3
    have h5 : (2:ℕ) ^ e < 2 ^ (e + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  refine Aux.hpp_of_minimalPeriod (by positivity) ?_
  rw [hNgj, hge, heM]
