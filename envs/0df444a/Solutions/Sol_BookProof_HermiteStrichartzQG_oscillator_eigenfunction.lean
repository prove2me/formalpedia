-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.oscillator_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:12:03.453855+00:00
-- url     : https://prove2.me/submissions/fa52e260-1a7d-4515-8a2b-cd5ab7295f2f

-- Generated from ChapterStrichartzHermiteQG.lean — solution of BookProof.HermiteStrichartzQG.oscillator_eigenfunction
import Mathlib
import Definitions.Def_ChapterStrichartzHermiteQG
import Theorems.Thm_BookProof_HermiteCore_hermiteFun_oscillator
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteStrichartzQG




open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : ℝ) :
    -(deriv (deriv (hermiteFun n)) x) + x ^ 2 / 4 * hermiteFun n x
      = oscillatorSymbol n * hermiteFun n x := hermiteFun_oscillator n x
