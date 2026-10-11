-- Prove2me | solution 1 for BookProof.ChapterSphericalBessel.sbessel_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-11T08:56:55.42727+00:00
-- url     : https://prove2.me/submissions/bb002368-9539-47b8-836d-92ca63eb64ee

-- Generated from ChapterSphericalBessel.lean — theorem BookProof.ChapterSphericalBessel.sbessel_one_eq
import Mathlib
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBessel



open scoped Topology
open BookProof.ChapterSphericalBessel

theorem solution{r : ℝ} (hr : r ≠ 0) : sbessel 1 r = sj1 r := by
  have hd : deriv sbesselBase r = (Real.cos r * r - Real.sin r * 1) / r ^ 2 := by
    show deriv (fun r => Real.sin r / r) r = _
    exact ((Real.hasDerivAt_sin r).div (hasDerivAt_id r) hr).deriv
  simp only [sbessel, pow_one, Function.iterate_one, rayleighOp, sj1]
  rw [hd]
  field_simp
  ring
