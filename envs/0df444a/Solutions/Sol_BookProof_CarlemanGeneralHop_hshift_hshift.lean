-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.hshift_hshift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T22:57:13.143739+00:00
-- url     : https://prove2.me/submissions/9624d10e-5cae-42d0-b42f-5906868fce7b

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.hshift_hshift
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Theorems.Thm_BookProof_CarlemanGeneralHop_hshift_apply
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p m a : Fin d →₀ ℕ} (h : ∀ k, m k ≤ a k) :
    hshift m p (hshift p m a) = a := by

  ext k
  rw [hshift_apply, hshift_apply]
  have := h k
  omega
