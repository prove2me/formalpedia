-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:08.3249+00:00
-- url     : https://prove2.me/submissions/d3e43ed0-cf85-435a-ac46-4adcc8b38a82
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.qgMode_essentiallySelfAdjoint_on_hermiteCore
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityDensitized
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (a b V : ℕ → ℝ) :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp (qgModeSymbol a b V)) := hermiteCoreOp_essentiallySelfAdjoint _
