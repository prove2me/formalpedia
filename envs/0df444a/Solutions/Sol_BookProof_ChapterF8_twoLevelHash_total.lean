-- Prove2me | solution 1 for BookProof.ChapterF8.twoLevelHash_total
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:42.879128+00:00
-- url     : https://prove2.me/submissions/da2d8691-c27d-4c1a-8374-36d8b23a590e

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.twoLevelHash_total
import Mathlib
import Definitions.Def_ChapterF8
import Theorems.Thm_BookProof_ChapterF8_fockEmbed_mem_singleExcitation
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K)
    (x : Fin d → ℝ) : twoLevelHash h g x ∈ singleExcitation K := fockEmbed_mem_singleExcitation g (featureHash h x)
