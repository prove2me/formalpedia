-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_starobinskyV_mul_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:36.319658+00:00
-- url     : https://prove2.me/submissions/a550542d-c91a-48ac-b836-f8cce1ec8cc2

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_starobinskyV_mul_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_gaussPoly_of_expBounded
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (p : Polynomial ℝ) :
    MemLp (fun x : ℝ => ((starobinskyV M alpha x * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) :=
  memLp_mul_gaussPoly_of_expBounded
      (continuous_starobinskyV M alpha)
      (expBounded_starobinskyV M alpha hM) p
