-- Prove2me | solution 1 for BookProof.ChapterAttentionMarkov.push_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:43:55.613738+00:00
-- url     : https://prove2.me/submissions/abdb4ece-fe85-4974-b191-5e8256f8f185

-- Generated from ChapterAttentionMarkov.lean — solution of BookProof.ChapterAttentionMarkov.push_nonneg
import Mathlib
import Definitions.Def_ChapterAttentionMarkov
open BookProof.ChapterAttentionMarkov



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {P : Fin m → Fin m → ℝ} {p : Fin m → ℝ} (hP : IsStochastic P)
    (hp : ∀ j, 0 ≤ p j) (j : Fin m) : 0 ≤ push P p j := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hP.1 i j)
