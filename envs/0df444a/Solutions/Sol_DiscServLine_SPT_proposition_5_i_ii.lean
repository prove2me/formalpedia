-- Prove2me | solution 1 for DiscServLine.SPT.proposition_5_i_ii
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T06:45:07.165718+00:00
-- url     : https://prove2.me/submissions/5ca5e6d4-d005-45d7-8b3c-ae1e8405bbfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DiscServLine_SPT_Model
import Theorems.Thm_DiscServLine_SPT_lemma_A7

open DiscServLine.SPT

theorem solution (P : Params) (hP : P.Standing) :
    (∃ d, IsOptimal P d) ∧ ∀ d, IsOptimal P d → d.lo < d.hi ∧ d.Λk 0 = P.Λ := by
  obtain ⟨hex, hall⟩ := lemma_A7 P hP
  refine ⟨hex, fun d hd => ?_⟩
  obtain ⟨ω, ⟨hω0, hω1⟩, -, h0, -, -, hlo, hhi⟩ := hall d hd
  refine ⟨?_, h0⟩
  obtain ⟨hc, -, hb, hΛ⟩ := hP
  have hκ : 0 < κ P := by unfold κ; positivity
  rw [hlo, hhi]
  unfold tLoA7 tHiA7
  set s := Real.sqrt (1 + κ P) with hs
  set r := Real.sqrt (1 + ω * κ P) with hr
  have hr1 : 0 < 1 + ω * κ P := by positivity
  have hs2 : s ^ 2 = 1 + κ P := Real.sq_sqrt (by positivity)
  have hr2 : r ^ 2 = 1 + ω * κ P := Real.sq_sqrt hr1.le
  have hrpos : 0 < r := Real.sqrt_pos.mpr hr1
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hq : Real.sqrt (ω / (1 + ω * κ P)) = Real.sqrt ω / r := by
    rw [Real.sqrt_div' _ hr1.le]
  rw [hq]
  have hwpos : 0 < Real.sqrt ω := Real.sqrt_pos.mpr hω0
  have hw2 : Real.sqrt ω ^ 2 = ω := Real.sq_sqrt hω0.le
  have hsr : r < s := by
    rw [hs, hr]; apply Real.sqrt_lt_sqrt hr1.le; nlinarith
  have hkey : s * Real.sqrt ω < r := by
    have : (s * Real.sqrt ω) ^ 2 < r ^ 2 := by
      rw [mul_pow, hs2, hw2, hr2]; nlinarith
    nlinarith [mul_pos hspos hwpos]
  have hcb : 0 < P.c / (2 * P.b) := by positivity
  have hpos : 0 < P.c / (2 * P.b) * (s - r) := mul_pos hcb (by linarith)
  rw [div_div_eq_mul_div, lt_div_iff₀ hwpos]
  nlinarith [mul_lt_mul_of_pos_left hkey hpos]
