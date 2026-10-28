-- Prove2me | solution 1 for BruhatGlue.no_glue
-- status  : ACCEPTED   (prove)
-- author  : @darkhipo
-- created : 2026-10-28T19:11:53.949762+00:00
-- url     : https://prove2.me/submissions/8f2f53ad-d230-4c06-96bd-d1176cf35cea

import Definitions.Def_BruhatGlue_Model

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open BruhatGlue

theorem solution {K : Type*} [Field K] {m : ℕ} {w} (h : Glue K m (blkSwap K m) w) :
    m ≤ w := by
  have h1 := glue_rank h
  rw [B_blkSwap, Matrix.rank_one] at h1
  simpa using h1
