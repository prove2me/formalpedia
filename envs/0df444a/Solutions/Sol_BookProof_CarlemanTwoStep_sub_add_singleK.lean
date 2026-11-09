-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sub_add_singleK
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:21.787867+00:00
-- url     : https://prove2.me/submissions/11cbcb87-cdb6-43cb-9da9-0921cdde7233

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sub_add_singleK
import Mathlib
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
open BookProof.CarlemanTwoStep




open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} (h : k ≤ a i) :
    (a - Finsupp.single i k) + Finsupp.single i k = a := by
  ext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]
