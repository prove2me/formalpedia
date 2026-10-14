-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:37:16.483881+00:00
-- url     : https://prove2.me/submissions/f784f71e-0ae3-42a0-b239-e8b75b302770

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.tendsto_coherentBorn_smul_query_ne
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_eq_scoreSoftmax
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_softmax_smul_query
import Theorems.Thm_BookProof_ChapterSoftmaxSharpness_tendsto_scoreSoftmax_ne
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
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (r : ℝ) (hk : ∀ l, ‖k l‖ = r) (j i : Fin m)
    (hmax : ∀ l, l ≠ j → (inner ℝ q (k l) : ℝ) < inner ℝ q (k j)) (hi : i ≠ j) :
    Tendsto (fun c : ℝ => bornWeight (c • q) k i) atTop (𝓝 0) := by

  have hrewrite : ∀ c : ℝ, bornWeight (c • q) k i
      = scoreSoftmax (2 * c) (fun l => inner ℝ q (k l)) i := by
    intro c
    rw [coherentBorn_eq_softmax (c • q) k r hk i, softmax_smul_query,
      softmax_eq_scoreSoftmax]
  have hscale : Tendsto (fun c : ℝ => 2 * c) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop (by norm_num)
  have hlim := (tendsto_scoreSoftmax_ne (fun l => inner ℝ q (k l)) j i hmax hi).comp hscale
  simpa [hrewrite, Function.comp] using! hlim
