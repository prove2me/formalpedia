-- Prove2me | solution 1 for BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:15.575712+00:00
-- url     : https://prove2.me/submissions/bae5716a-58f9-4876-a168-790cd47c361a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionLocality.lean — solution of BookProof.ChapterAttentionLocality.norm_headOutput_window_sub_le
import Mathlib
import Definitions.Def_ChapterAttentionLocality
import Theorems.Thm_BookProof_ChapterAttentionLocality_mem_window
import Theorems.Thm_BookProof_ChapterAttentionLocality_farMass_le
import Theorems.Thm_BookProof_ChapterAttentionSparse_norm_headOutput_masked_sub_le
import Theorems.Thm_BookProof_ChapterAttentionSparse_one_sub_attendedMass_eq
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterAttentionMasking
import Definitions.Def_ChapterAttentionOutput
import Definitions.Def_ChapterAttentionSparse
open BookProof.ChapterAttentionSparse
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionMasking
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionLocality



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {beta gamma Delta R : ℝ} (hb : 0 ≤ beta)
    (hg : 0 ≤ gamma) (s : Fin m → ℝ) (d : Fin m → ℝ) {j₀ : Fin m} (hd0 : d j₀ = 0)
    (hR : 0 < R) (hDelta : ∀ l, s l ≤ s j₀ + Delta) {v : Fin m → E} {C : ℝ}
    (hv : ∀ j, ‖v j‖ ≤ C) (hC : 0 ≤ C) :
    ‖observableExpectation
        (maskedSoftmax beta (alibiScore s gamma d) (window d R)) v
      - headOutput beta (alibiScore s gamma d) v‖
      ≤ 2 * ((m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))))) * C := by

  have hj₀ : j₀ ∈ window d R := by rw [mem_window, hd0]; exact hR
  have hS : (window d R).Nonempty := ⟨j₀, hj₀⟩
  have hfar := farMass_le hb hg s d hd0 hDelta (R := R)
  have hmass : 1 - attendedMass beta (alibiScore s gamma d) (window d R)
      ≤ (m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R)))) := by
    rw [one_sub_attendedMass_eq beta (alibiScore s gamma d) (window d R) j₀]
    exact hfar
  refine le_trans
    (norm_headOutput_masked_sub_le beta (alibiScore s gamma d) hS j₀ hv) ?_
  have h2 : 2 * (1 - attendedMass beta (alibiScore s gamma d) (window d R))
      ≤ 2 * ((m : ℝ) * (Real.exp (beta * Delta) * Real.exp (-(beta * (gamma * R))))) := by
    linarith
  exact mul_le_mul_of_nonneg_right h2 hC
