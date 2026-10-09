-- Prove2me | solution 1 for BookProof.ChapterF8.twoLevelHash_decodes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:56.832089+00:00
-- url     : https://prove2.me/submissions/0ba338e7-2301-4a95-8cc6-d2b08f7ed46e

-- Generated from ChapterF8.lean — solution of BookProof.ChapterF8.twoLevelHash_decodes
import Mathlib
import Definitions.Def_ChapterF8
import Theorems.Thm_BookProof_ChapterF8_featureHash_decodes
open BookProof.ChapterF8



noncomputable section

open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution {d k K : ℕ} (h : Fin d → Fin k) (g : Fin k → Fin K)
    (hg : Function.Injective g) (x : Fin d → ℝ) (j : Fin k) :
    twoLevelHash h g x (Finsupp.single (g j) 1) = ((featureHash h x j : ℝ) : ℂ) := featureHash_decodes g hg (featureHash h x) j
