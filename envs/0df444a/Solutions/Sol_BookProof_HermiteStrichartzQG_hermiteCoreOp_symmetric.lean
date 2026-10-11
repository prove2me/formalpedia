-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:01.250997+00:00
-- url     : https://prove2.me/submissions/50da72c5-362f-41f8-ab61-e76e006bdfbe

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteCoreOp_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteDiagOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    SymmetricOn hermiteCore (hermiteCoreOp lam) := by

  intro x y
  exact hermiteDiagOp_symmetric lam
    (Submodule.inclusion (hermiteCore_le_hermiteDiagDomain lam) x)
    (Submodule.inclusion (hermiteCore_le_hermiteDiagDomain lam) y)
