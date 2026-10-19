-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:57:58.21799+00:00
-- url     : https://prove2.me/submissions/6c80fffc-86a9-4c92-8d7c-651b9763774d

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterSinusoidalPosition.lean — theorem BookProof.ChapterSinusoidalPosition.scoreSoftmax_sinusoidal_ge
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSinusoidalPosition


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}


theorem solution {m : ℕ} {beta : ℝ} (hb : 0 ≤ beta) (w : Fin n → ℝ)
    (p : ℝ) (k : Fin m → ℝ) (j : Fin m) :
    Real.exp (-(beta * (2 * n))) / (m : ℝ)
      ≤ scoreSoftmax beta (fun l => peInner w p (k l)) j := by
  have hs : ∀ l, |peInner w p (k l)| ≤ n := by
    intro l
    unfold peInner sinusoidalEncode
    calc |∑ a, (Real.sin (w a * p) * Real.sin (w a * k l) + Real.cos (w a * p) * Real.cos (w a * k l))|
        ≤ ∑ a, |Real.sin (w a * p) * Real.sin (w a * k l) + Real.cos (w a * p) * Real.cos (w a * k l)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have e : Real.sin (w a * p) * Real.sin (w a * k l) + Real.cos (w a * p) * Real.cos (w a * k l)
              = Real.cos (w a * p - w a * k l) := by rw [Real.cos_sub]; ring
          rw [e]; exact Real.abs_cos_le_one _
      _ = n := by simp
  have hm : (0 : ℝ) < m := by exact_mod_cast Fin.pos j
  set S := fun l => peInner w p (k l)
  have hnum : Real.exp (-(beta * n)) ≤ Real.exp (beta * S j) := by
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hs j)).1
    nlinarith
  have hden : ∑ l, Real.exp (beta * S l) ≤ m * Real.exp (beta * n) := by
    calc ∑ l, Real.exp (beta * S l) ≤ ∑ _l : Fin m, Real.exp (beta * n) :=
          Finset.sum_le_sum fun l _ => Real.exp_le_exp.mpr (by
            have := (abs_le.mp (hs l)).2; nlinarith)
      _ = m * Real.exp (beta * n) := by simp
  have hdpos : 0 < ∑ l, Real.exp (beta * S l) :=
    Finset.sum_pos (fun l _ => Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
  unfold scoreSoftmax
  rw [div_le_div_iff₀ hm hdpos]
  have e2 : Real.exp (-(beta * (2 * n))) * (m * Real.exp (beta * n)) = m * Real.exp (-(beta * n)) := by
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  calc Real.exp (-(beta * (2 * n))) * ∑ l, Real.exp (beta * S l)
      ≤ Real.exp (-(beta * (2 * n))) * (m * Real.exp (beta * n)) :=
        mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
    _ = m * Real.exp (-(beta * n)) := e2
    _ ≤ m * Real.exp (beta * S j) := mul_le_mul_of_nonneg_left hnum hm.le
    _ = Real.exp (beta * S j) * m := by ring

