-- Prove2me | solution 1 for BroughanRH.nicolasUpper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-11-23T19:17:09.757382+00:00
-- url     : https://prove2.me/submissions/6fed2126-149b-4679-b67c-38b303dd610d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BroughanRH_nicolasExplicit
import Mathlib

theorem solution :
    let c (n : ℕ) : ℝ := ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) * Real.sqrt (Real.log n)
    let β : ℝ := 2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2
    ∀ n : ℕ, primorial 1591883 ≤ n → c n < Real.exp Real.eulerMascheroniConstant * (2 + β) := by
  intro c β n hn
  have h := BroughanRH.nicolasExplicit n hn

  have hn2 : 2 ≤ n := by
    have h1 : (1591883 : ℕ) ≤ primorial 1591883 := le_primorial_self
    omega
  have hn2' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.2 hlog
  have hss : Real.sqrt (Real.log n) * Real.sqrt (Real.log n) = Real.log n :=
    Real.mul_self_sqrt hlog.le
  show ((n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) *
      Real.sqrt (Real.log n) < Real.exp Real.eulerMascheroniConstant * (2 + β)
  have h' : (n : ℝ) / (n.totient : ℝ) - Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) <
      Real.exp Real.eulerMascheroniConstant * (2 + β) / Real.sqrt (Real.log n) := by
    have := h; linarith
  rw [lt_div_iff₀ hs] at h'
  exact h'
