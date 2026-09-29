-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.cpoly_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:59:36.790755+00:00
-- url     : https://prove2.me/submissions/4d071003-3e3f-4b3f-9cc4-919bc49c49dc

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.cpoly_sum
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    cpoly (∑ i ∈ s, f i) = ∑ i ∈ s, cpoly (f i) := map_sum (MvPolynomial.map (starRingEnd ℂ)) f s
