-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:15.175873+00:00
-- url     : https://prove2.me/submissions/8cf42603-ba2d-40d7-85f4-1b0cd423c6e8

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_eq_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_smul_query
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_max
import Theorems.Thm_BookProof_ChapterSoftmaxBorn_coherentBorn_eq_softmax
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) :
    Tendsto (fun c : ℝ => bornWeight (c • q) k j) atTop (𝓝 1) := by

  have hrewrite : ∀ c : ℝ, bornWeight (c • q) k j
      = scoreSoftmax (2 * c) (fun l => inner ℝ q (k l)) j := by
    intro c
    rw [coherentBorn_eq_softmax (c • q) k r hk j, softmax_smul_query,
      softmax_eq_scoreSoftmax]
  have hscale : Tendsto (fun c : ℝ => 2 * c) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hlim := (tendsto_scoreSoftmax_max (fun l => inner ℝ q (k l)) j hmax).comp hscale
  simpa [hrewrite, Function.comp] using! hlim
