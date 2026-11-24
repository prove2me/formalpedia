-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.iSup_nonzero_of_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T10:58:49.590458+00:00
-- url     : https://prove2.me/submissions/ee427f7d-3ac5-4b99-bbdd-0be95f488164

import Mathlib

open ENNReal

theorem solution {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hf_nonzero
  exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hx) (le_iSup f x))
