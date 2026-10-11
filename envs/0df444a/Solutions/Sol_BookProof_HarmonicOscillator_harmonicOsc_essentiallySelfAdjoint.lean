-- Prove2me | solution 1 for BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:38.588386+00:00
-- url     : https://prove2.me/submissions/7f21f6a7-b7c1-47bc-b5a5-7fe346bb1a11
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.harmonicOsc_essentiallySelfAdjoint
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_essentiallySelfAdjoint
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn hermiteCore harmonicOscOp := hermiteCoreOp_essentiallySelfAdjoint harmonicSymbol
