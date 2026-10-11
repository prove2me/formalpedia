-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:02.250335+00:00
-- url     : https://prove2.me/submissions/cd85d9e3-a12d-4f62-b9de-a9f5aa8f35ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.hermiteCoreOp_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_deficiencyTrivialAt
import Theorems.Thm_BookProof_QuantumGravityDensitized_strichartz_esa_of_finiteSpeed
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp lam) := strichartz_esa_of_finiteSpeed _ fun _ hz => hermiteCoreOp_deficiencyTrivialAt lam hz
