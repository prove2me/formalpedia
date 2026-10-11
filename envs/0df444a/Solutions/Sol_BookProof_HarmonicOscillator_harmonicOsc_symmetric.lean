-- Prove2me | solution 1 for BookProof.HarmonicOscillator.harmonicOsc_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:03:37.527995+00:00
-- url     : https://prove2.me/submissions/dd99b221-1673-46dd-b51a-ccbb21e6a9bf

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.harmonicOsc_symmetric
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_symmetric
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine

set_option maxHeartbeats 1000000 in
theorem solution : SymmetricOn hermiteCore harmonicOscOp := hermiteCoreOp_symmetric harmonicSymbol
