-- Prove2me | solution 1 for Erdos195.degs_three_ap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T21:22:21.503477+00:00
-- url     : https://prove2.me/submissions/e12131fd-136e-45e2-bd20-6655e11ed157

import Mathlib
import Definitions.Def_Erdos195_defs


namespace Erdos195


/-- DEGS-type lower bound, proved directly over ℤ: every bijection `ℕ ≃ ℤ` has an increasing
monotone 3-AP `f 0, f m, 2 f m - f 0` where `m` is the first index with `f m > f 0`. -/
theorem degs_three_ap (f : ℕ ≃ ℤ) : HasMonotoneAP f 3 := by
  classical
  have hex : ∃ n, f 0 < f n := ⟨f.symm (f 0 + 1), by simp⟩
  set m := Nat.find hex with hm
  have hfm : f 0 < f m := Nat.find_spec hex
  have hbelow : ∀ i, 0 < i → i < m → f i < f 0 := by
    intro i hi him
    have h1 : ¬ f 0 < f i := Nat.find_min hex him
    have h2 : f i ≠ f 0 := by
      intro h; have := f.injective h; omega
    omega
  set j := f.symm (2 * f m - f 0) with hj
  have hfj : f j = 2 * f m - f 0 := by simp [hj]
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hfm; exact absurd hfm (lt_irrefl _)
    · exact h
  have hmj : m < j := by
    by_contra hcon
    push Not at hcon
    rcases Nat.lt_or_ge j m with h | h
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0] at hfj; omega
      · have := hbelow j h0 h; omega
    · have : j = m := le_antisymm hcon h
      rw [this] at hfj; omega
  refine ⟨[0, m, j], ⟨f 0, f m - f 0, Or.inl ?_⟩, ?_⟩
  · simp [List.range_succ, hfj]
    ring
  · simp [List.pairwise_cons]
    omega

end Erdos195



open Erdos195 in
theorem solution (f : ℕ ≃ ℤ) : HasMonotoneAP f 3 :=
  Erdos195.degs_three_ap f
