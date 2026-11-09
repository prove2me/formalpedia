-- Prove2me | solution 1 for BookProof.CarlemanTwoStep.sub_singleK_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T06:50:25.939082+00:00
-- url     : https://prove2.me/submissions/beeddc67-9e67-49a2-bd58-45b99eb5ecbc

-- Generated from ChapterCarlemanTwoStep.lean — solution of BookProof.CarlemanTwoStep.sub_singleK_apply
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

theorem solution {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    (a - Finsupp.single i k : Fin d →₀ ℕ) i = a i - k := by
  simp [Finsupp.tsub_apply]
