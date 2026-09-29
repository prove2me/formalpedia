-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:35.520504+00:00
-- url     : https://prove2.me/submissions/36f60493-15ce-4606-9134-eb1fdaf31ecf

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_scalaronFull1D_mul_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_add
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_poly
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_gaussPoly_of_expBounded
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ)
    (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        (((V3.eval x + starobinskyV M alpha x) * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) :=
  memLp_mul_gaussPoly_of_expBounded
      (V3.continuous_aeval.add (continuous_starobinskyV M alpha))
      ((expBounded_poly V3).add (expBounded_starobinskyV M alpha hM)) p
