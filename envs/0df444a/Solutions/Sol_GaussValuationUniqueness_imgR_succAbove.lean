-- Prove2me | solution 1 for GaussValuationUniqueness.imgR_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:24.015413+00:00
-- url     : https://prove2.me/submissions/99497ff2-1d88-4a16-abe6-9894cbc7a236

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Theorems.Thm_GaussValuationUniqueness_sac_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
namespace GaussValuationUniqueness
theorem _root_.solution {R : Type*} [CommRing R] {D N : ℕ} (j0 : Fin (N + 1)) (ρ : Fin N → R)
    (i : Fin (D + 1)) (k : Fin N) :
    imgR (D := D) j0 ρ (i, j0.succAbove k) = MvPolynomial.X (Sum.inr (i, k)) := by
  unfold imgR
  exact sac_succAbove j0 _ _ k
end GaussValuationUniqueness
