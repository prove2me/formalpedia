-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.observableExpectation_mixture
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:39.458555+00:00
-- url     : https://prove2.me/submissions/b68de75f-452a-4572-ac8e-2e2f465873e3

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.observableExpectation_mixture
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Definitions.Def_ChapterObservableExpectation
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin H → ℝ) (p : Fin H → Fin m → ℝ)
    (v : Fin m → E) :
    observableExpectation (mixture w p) v = ∑ h, w h • observableExpectation (p h) v := by

  rw [observableExpectation]
  have hterm : ∀ j : Fin m, mixture w p j • v j = ∑ h, w h • (p h j • v j) := by
    intro j
    rw [mixture, Finset.sum_smul]
    exact Finset.sum_congr rfl fun h _ => by rw [mul_smul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [observableExpectation, Finset.smul_sum]
