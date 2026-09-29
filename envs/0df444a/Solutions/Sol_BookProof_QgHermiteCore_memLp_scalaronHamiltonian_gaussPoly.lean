-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:34:36.962014+00:00
-- url     : https://prove2.me/submissions/0b1fa56d-6dc7-4503-b508-c7f14b97a266

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_scalaronHamiltonian_gaussPoly
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_continuous_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_memLp_hamiltonian_gaussPoly
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (p : Polynomial ℝ) :
    MemLp (fun x : ℝ =>
        ((-deriv (deriv (gaussPoly p)) x + starobinskyV M alpha x * gaussPoly p x : ℝ) : ℂ)) 2
      (volume : Measure ℝ) :=
  memLp_hamiltonian_gaussPoly
      (continuous_starobinskyV M alpha)
      (expBounded_starobinskyV M alpha hM) p
