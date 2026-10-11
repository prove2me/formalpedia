-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:11.312723+00:00
-- url     : https://prove2.me/submissions/eaf92ed8-ffbd-4fe0-bae7-c6bf0807527c

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.spherical_plancherel_bump
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_spherical_plancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddSchwartz_apply
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddSchwartz_odd
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution :
    ∫ p in Ioi (0 : ℝ), ‖sphericalTransform (fun r : ℝ => oddBump r / (r : ℂ)) p‖ ^ 2 * p ^ 2
      = ∫ r in Ioi (0 : ℝ), ‖oddBump r / (r : ℂ)‖ ^ 2 * r ^ 2 :=
  spherical_plancherel oddSchwartz oddSchwartz_odd _ fun r hr => by
      have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hr).ne'
      rw [oddSchwartz_apply]
      field_simp
