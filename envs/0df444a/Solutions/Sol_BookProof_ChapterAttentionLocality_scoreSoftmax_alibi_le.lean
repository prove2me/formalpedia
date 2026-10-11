-- Prove2me | solution 1 for BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T22:45:07.231574+00:00
-- url     : https://prove2.me/submissions/c80f13d9-3a8b-4884-9ce5-e1291d5c4915

-- Generated from ChapterAttentionLocality.lean — solution of BookProof.ChapterAttentionLocality.scoreSoftmax_alibi_le
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_denom_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterAttentionLocality



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta gamma Delta : ℝ} (hb : 0 ≤ beta) (s : Fin m → ℝ)
    (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0) (hDelta : ∀ l, s l ≤ s j₀ + Delta)
    (l : Fin m) :
    scoreSoftmax beta (alibiScore s gamma d) l
      ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l))) := by

  set t := alibiScore s gamma d with ht
  have hZ : 0 < ∑ x, Real.exp (beta * t x) := scoreSoftmax_denom_pos beta t l
  have hden : Real.exp (beta * t j₀) ≤ ∑ x, Real.exp (beta * t x) :=
    Finset.single_le_sum (f := fun x => Real.exp (beta * t x))
      (fun x _ => (Real.exp_pos _).le) (Finset.mem_univ j₀)
  have hnum : Real.exp (beta * t l)
      ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l)))
        * Real.exp (beta * t j₀) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hj : t j₀ = s j₀ := by simp [ht, alibiScore, hd0]
    have hl : t l = s l - gamma * d l := rfl
    have := hDelta l
    rw [hj, hl]
    nlinarith [hb, this]
  calc scoreSoftmax beta t l = Real.exp (beta * t l) / ∑ x, Real.exp (beta * t x) := rfl
    _ ≤ (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l)))
          * Real.exp (beta * t j₀)) / ∑ x, Real.exp (beta * t x) :=
        div_le_div_of_nonneg_right hnum hZ.le
    _ ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l))) := by
        rw [div_le_iff₀ hZ]
        have hpos : 0 ≤ Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * d l))) :=
          (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
        exact mul_le_mul_of_nonneg_left hden hpos
