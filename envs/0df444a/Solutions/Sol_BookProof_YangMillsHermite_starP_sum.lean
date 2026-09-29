-- Prove2me | solution 1 for BookProof.YangMillsHermite.starP_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T02:13:01.654427+00:00
-- url     : https://prove2.me/submissions/16fa5445-3fd3-4eb2-885c-f66df7f458f9

-- Generated from ChapterYangMillsHermite.lean — solution of BookProof.YangMillsHermite.starP_sum
import Mathlib
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := map_sum _ _ _
