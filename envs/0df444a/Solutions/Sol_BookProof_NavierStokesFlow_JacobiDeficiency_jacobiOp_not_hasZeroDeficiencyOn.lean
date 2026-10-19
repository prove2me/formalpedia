-- Prove2me | solution 1 for BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_not_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:10:42.798988+00:00
-- url     : https://prove2.me/submissions/d7ad566b-5609-4b43-9932-7a5ec5d3c69e

import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesDeficiency.lean — theorem BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_not_hasZeroDeficiencyOn
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.JacobiDeficiency


open scoped ENNReal
theorem h43_jw_ge (n : ℕ) : (2 : ℝ) * 4 ^ n ≤ jacobiWeight n := by
  induction n with
  | zero => simp [jacobiWeight]
  | succ m ih => rw [jacobiWeight, pow_succ]; linarith

theorem h43_jw_pos (n : ℕ) : 0 < jacobiWeight n :=
  lt_of_lt_of_le (by positivity) (h43_jw_ge n)

theorem h43_jdef (n : ℕ) : jacobiFun defFun n = Complex.I * defFun n := by
  cases n with
  | zero => simp [jacobiFun, defFun, jacobiWeight]; ring
  | succ m =>
    simp only [jacobiFun, defFun, jacobiWeight]
    push_cast
    linear_combination ((Complex.I / 2) ^ m * (jacobiWeight m : ℂ)) * Complex.I_sq

theorem h43_defState_ne : defState ≠ 0 := by
  intro h
  have := congrArg (fun f : LpNat.L2N => (f : ℕ → ℂ) 0) h
  simp [defState, defFun] at this

theorem h43_not_zd : ¬ HasZeroDeficiencyOn (lpFiniteModes ℕ) jacobiOp := by
  intro h
  apply h43_defState_ne
  apply h.1
  intro v
  obtain ⟨N, hN⟩ := LpNat.exists_tail_zero v.2
  have hl := LpNat.inner_eq_sum_range (f := ((jacobiOp v : lpFiniteModes ℕ) : LpNat.L2N))
    (g := defState) (N := N + 1) (by simpa using jacobiFun_tail_zero hN)
  have hr := LpNat.inner_eq_sum_range (f := ((v : lpFiniteModes ℕ) : LpNat.L2N))
    (g := Complex.I • defState) (N := N + 1) (fun n hn => hN n (by omega))
  rw [hl, hr, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have e : ∀ n, ((Complex.I • defState : LpNat.L2N) : ℕ → ℂ) n = jacobiFun defFun n := by
    intro n; rw [h43_jdef]; rfl
  simp only [jacobiOp_coe, e]
  have := jacobi_wronskian ((v : LpNat.L2N) : ℕ → ℂ) defFun N
  rw [hN N le_rfl, hN (N + 1) (by omega)] at this
  simpa [defState] using this

theorem solution :
    ¬ HasZeroDeficiencyOn (lpFiniteModes ℕ) jacobiOp := by
  exact h43_not_zd

