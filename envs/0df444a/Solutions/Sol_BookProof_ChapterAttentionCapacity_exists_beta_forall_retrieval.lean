-- Prove2me | solution 1 for BookProof.ChapterAttentionCapacity.exists_beta_forall_retrieval
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:38:31.435815+00:00
-- url     : https://prove2.me/submissions/7647b357-f042-4fd0-a8f7-7801f1bb12e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterAttentionCapacity.lean — solution of BookProof.ChapterAttentionCapacity.exists_beta_forall_retrieval
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
import Theorems.Thm_BookProof_ChapterAttentionCapacity_norm_headOutput_distScore_sub_le_of_separated
import Theorems.Thm_BookProof_ChapterAttentionCapacity_tendsto_capacityError
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionCapacity



open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution {k : Fin m → EuclideanSpace ℝ (Fin n)}
    {v : Fin m → E} {r C eps : ℝ} (hr : 0 < r) (hsep : keysSeparated k r)
    (hv : ∀ l, ‖v l‖ ≤ C) (heps : 0 < eps) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ b, B ≤ b → ∀ i : Fin m,
      ‖headOutput b (distScore (k i) k) v - v i‖ ≤ eps := by

  have htend := tendsto_capacityError (C := C) hr ((m : ℝ) - 1)
  have hev : ∀ᶠ b : ℝ in atTop, 2 * C * (((m : ℝ) - 1) * Real.exp (-(b * r ^ 2))) ≤ eps :=
    htend.eventually (eventually_le_nhds heps)
  obtain ⟨B₀, hB₀⟩ := eventually_atTop.1 hev
  refine ⟨max 0 B₀, le_max_left _ _, fun b hb i => ?_⟩
  have hb0 : 0 ≤ b := le_trans (le_max_left _ _) hb
  have hbB : B₀ ≤ b := le_trans (le_max_right _ _) hb
  exact le_trans
    (norm_headOutput_distScore_sub_le_of_separated hb0 hr.le hsep hv i) (hB₀ b hbB)
