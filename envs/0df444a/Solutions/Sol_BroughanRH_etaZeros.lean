-- Prove2me | solution 1 for BroughanRH.etaZeros
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T18:38:24.019931+00:00
-- url     : https://prove2.me/submissions/bb677e41-2a4d-465f-a515-91fdc47aaa19
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_riemann_hypothesis

theorem solution :
    let eta (s : ℂ) := (1 - (2 : ℂ)^(1-s)) * riemannZeta s
    ∀ s : ℂ, 0 < s.re → s.re < 1 → eta s = 0 → s.re = 1/2 := by
  intro eta s h0 h1 hs
  have hfac : (1 - (2 : ℂ)^(1-s)) ≠ 0 := by
    intro h
    have h2 : (2 : ℂ)^(1-s) = 1 := by linear_combination -h
    have hn := congrArg norm h2
    rw [show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.norm_natCast_cpow_of_pos (by norm_num)] at hn
    simp only [Complex.sub_re, Complex.one_re, norm_one, Nat.cast_ofNat] at hn
    have : (1:ℝ) < (2:ℝ)^(1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  have hz : riemannZeta s = 0 := by
    rcases mul_eq_zero.mp hs with h | h
    · exact absurd h hfac
    · exact h
  apply riemann_hypothesis s hz
  · rintro ⟨n, rfl⟩
    simp at h0
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  · rintro rfl
    simp at h1
