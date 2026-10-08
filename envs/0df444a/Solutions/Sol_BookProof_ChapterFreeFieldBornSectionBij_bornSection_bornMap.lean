-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:53:37.169489+00:00
-- url     : https://prove2.me/submissions/45947bb6-a782-42f5-a36c-32f318b6bef9

-- Generated from ChapterFreeFieldBornSectionBij.lean — solution of BookProof.ChapterFreeFieldBornSectionBij.bornSection_bornMap
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSectionBij
import Theorems.Thm_BookProof_ChapterFreeFieldBornSurj_bornSection_apply
open BookProof.ChapterFreeFieldBornSectionBij



open MeasureTheory
open BookProof.ChapterFreeFieldGaussian BookProof.ChapterFreeFieldSphere
open BookProof.ChapterFreeFieldSphereSupport BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSurj


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ nonnegOrthant n) :
    bornSection (bornMap x) = x := by

  ext k
  rw [bornSection_apply]
  change Real.sqrt ((x k) ^ 2) = x k
  rw [Real.sqrt_sq (hx k)]
