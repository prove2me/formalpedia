-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.iSup_min_nat_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T10:58:57.134214+00:00
-- url     : https://prove2.me/submissions/c7f7af7f-5f80-4e2c-87d0-1b5151c0506f

import Mathlib

open ENNReal

theorem solution {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ :=
  ne_of_lt ((iSup_le fun x => min_le_right (f x) (n : ENNReal)).trans_lt (natCast_lt_top n))
