-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff_retained
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:35:57.920231+00:00
-- url     : https://prove2.me/submissions/512341ae-0383-4560-a384-768a01375e74

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff_retained
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_defect_le_sqrt_cutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_retainedEmbedding_isometry
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_mem_range_retainedEmbedding
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (heig : IsGramEigen w u lam) {tol : ℝ}
    {d : ℕ} {e : Fin d → Fin m} (he : Function.Injective e)
    (hpos : ∀ j : Fin d, 0 < lam (e j))
    (hcut : ∀ k ∉ (Finset.univ.image e), lam k ≤ tol) (i : Fin m) :
    ‖w i - retainedEmbedding w u lam e
        (adjoint (retainedEmbedding w u lam e) (w i))‖ ≤ Real.sqrt tol := by

  refine defect_le_sqrt_cutoff heig (Finset.univ.image e) hcut _
    (retainedEmbedding_isometry heig he hpos) ?_ i
  intro k hk
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
  exact mem_range_retainedEmbedding hpos j
