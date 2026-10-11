-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.qg3D_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:05.386373+00:00
-- url     : https://prove2.me/submissions/1f662631-16bb-4312-8a5a-a0af79d5314c

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.qg3D_symmetric
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (xi : ℕ → Fin 3 → ℝ) (xiY V : ℕ → ℝ) :
    SymmetricOn hermiteCore (qg3DHermiteHamiltonian xi xiY V) := hermiteCoreOp_symmetric _
