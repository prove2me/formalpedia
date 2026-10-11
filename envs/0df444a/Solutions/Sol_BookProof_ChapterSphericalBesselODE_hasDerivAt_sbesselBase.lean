-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:31.350603+00:00
-- url     : https://prove2.me/submissions/a5f410dd-823b-428c-9add-3d46b0eecb9b

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.hasDerivAt_sbesselBase
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt sbesselBase (Real.cos x / x - Real.sin x / x ^ 2) x := by

  have h := (Real.hasDerivAt_sin x).div (hasDerivAt_id x) hx
  simp only [id_eq] at h
  have he : (Real.cos x * x - Real.sin x * 1) / x ^ 2
      = Real.cos x / x - Real.sin x / x ^ 2 := by field_simp
  rwa [he] at h
