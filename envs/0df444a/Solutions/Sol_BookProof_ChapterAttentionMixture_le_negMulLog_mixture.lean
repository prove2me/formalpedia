-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.le_negMulLog_mixture
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:28:42.407148+00:00
-- url     : https://prove2.me/submissions/af522fcf-5588-4b58-b625-f5747ae02c2d

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.le_negMulLog_mixture
import Mathlib
import Definitions.Def_ChapterAttentionMixture
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {w : Fin H → ℝ} {p : Fin H → Fin m → ℝ} (hw0 : ∀ h, 0 ≤ w h)
    (hw : ∑ h, w h = 1) (hp0 : ∀ h j, 0 ≤ p h j) (j : Fin m) :
    ∑ h, w h * Real.negMulLog (p h j) ≤ Real.negMulLog (mixture w p j) := by

  have h := Real.concaveOn_negMulLog.le_map_sum (t := (Finset.univ : Finset (Fin H)))
    (w := w) (p := fun h => p h j) (fun h _ => hw0 h) hw (fun h _ => hp0 h j)
  simpa [mixture, smul_eq_mul] using h
