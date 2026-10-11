-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:04.455349+00:00
-- url     : https://prove2.me/submissions/b0fd5f28-a6c0-42e2-962e-b07f3b168bf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.oscillator_essentiallySelfAdjoint_on_hermiteCore
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn hermiteCore (hermiteCoreOp oscillatorSymbol) := hermiteCoreOp_essentiallySelfAdjoint _
