-- Prove2me | solution 1 for BookProof.QgHermiteCore.expBounded_scalaronSectorPotential
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:34.812402+00:00
-- url     : https://prove2.me/submissions/7da6b527-e424-4b07-a672-5426d6644e28

-- Generated from ChapterQgHermiteCore.lean — solution of BookProof.QgHermiteCore.expBounded_scalaronSectorPotential
import Mathlib
import Definitions.Def_ChapterQgHermiteCore
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_add
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_poly
import Theorems.Thm_BookProof_QgHermiteCore_expBounded_starobinskyV
import Theorems.Thm_BookProof_QgHermiteCore_ExpBounded_comp_coord
open BookProof.QgHermiteCore














open MeasureTheory Polynomial Filter Topology
open BookProof.HermiteCore BookProof.Starobinsky







variable {E : Type*} [NormedAddCommGroup E]





































open BookProof.HermiteProductCore

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (hM : 0 < M) (V3 : Polynomial ℝ) :
    ExpBounded (scalaronSectorPotential M alpha V3) := ((expBounded_poly V3).comp_coord 0).add ((expBounded_starobinskyV M alpha hM).comp_coord 1)
