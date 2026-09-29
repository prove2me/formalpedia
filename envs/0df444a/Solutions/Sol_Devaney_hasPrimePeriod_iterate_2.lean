-- Prove2me | solution 2 for Devaney.hasPrimePeriod_iterate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-17T14:43:20.631098+00:00
-- url     : https://prove2.me/submissions/98446223-0e9e-48b5-ae0f-55e272dd6bd2

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

theorem solution (f : ℝ → ℝ) (x : ℝ) (m n : ℕ) (hn : 0 < n)
    (h : HasPrimePeriod f x m) : HasPrimePeriod (f^[n]) x (m / Nat.gcd m n) := by
  have hm0 : 0 < m := h.1
  have hm : Function.minimalPeriod f x = m := Aux.hpp_minimalPeriod h
  have hd := Function.minimalPeriod_iterate_eq_div_gcd (f := f) (x := x) (n := n) (by omega)
  rw [hm] at hd
  have hg : 0 < Nat.gcd m n := by
    rcases Nat.eq_zero_or_pos (Nat.gcd m n) with hz | hp
    · rw [Nat.gcd_eq_zero_iff] at hz; omega
    · exact hp
  exact Aux.hpp_of_minimalPeriod
    (Nat.div_pos (Nat.le_of_dvd hm0 (Nat.gcd_dvd_left m n)) hg) hd
