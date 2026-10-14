-- Prove2me | solution 1 for BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:44:53.095067+00:00
-- url     : https://prove2.me/submissions/438a3015-29fa-42cc-ba63-5ebfd34ad259

-- Generated from ChapterHarmonicOscillatorEsa.lean — solution of BookProof.HarmonicOscillator.harmonicOscOp_hermiteLp
import Mathlib
import Definitions.Def_ChapterHarmonicOscillatorEsa
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteCoreOp_hermiteLp
import Theorems.Thm_BookProof_HermiteStrichartzQG_hermiteLp_mem_hermiteCore
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HarmonicOscillator




open MeasureTheory Polynomial BookProof.HermiteCore BookProof.HermiteStrichartzQG
open BookProof.FarisLavine
open BookProof.HermiteCore

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    harmonicOscOp ⟨hermiteLp n, hermiteLp_mem_hermiteCore n⟩
      = ((harmonicSymbol n : ℂ)) • hermiteLp n := hermiteCoreOp_hermiteLp harmonicSymbol n
