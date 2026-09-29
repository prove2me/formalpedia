-- Prove2me | solution 1 for BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:11.22798+00:00
-- url     : https://prove2.me/submissions/b1f0001b-3756-43ca-b0a6-331a4502f29f

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.memLp_scalaronSectorPotential_mul_pgFun
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_memLp_mul_pgFun_of_expBounded
import Theorems.Thm_BookProof_QgHermiteCore_continuous_scalaronSectorPotential
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_scalaronSectorPotential
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ)
    (p : MvPolynomial (Fin 2) ℂ) :
    MemLp (fun x : Vd 2 => ((scalaronSectorPotential M alpha V3 x : ℝ) : ℂ) * pgFun p x) 2
      (volume : Measure (Vd 2)) :=
  memLp_mul_pgFun_of_expBounded (continuous_scalaronSectorPotential M alpha V3)
      (expBounded_scalaronSectorPotential M alpha hM V3) p
