-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T09:42:48.783149+00:00
-- url     : https://prove2.me/submissions/79e0253e-9b3c-413f-b002-fec77ef65204

-- Generated from ChapterFreeFieldBornSurj.lean — solution of BookProof.ChapterFreeFieldBornSurj.bornMap_bornSection
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSurj
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply
open BookProof.ChapterFreeFieldBornSurj



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    bornMap (bornSection p) = p := by

  funext k
  change (bornSection p k) ^ 2 = p k
  rw [bornSection_apply, Real.sq_sqrt (hp.1 k)]
