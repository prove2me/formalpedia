-- Prove2me | solution 1 for GaussValuationUniqueness.imgR_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:22.344184+00:00
-- url     : https://prove2.me/submissions/12e94209-5719-4691-be71-5053f391627b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Theorems.Thm_GaussValuationUniqueness_sac_same


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
    (i : Fin (D + 1)) : imgR (D := D) j0 ρ (i, j0) = if i = 0 then MvPolynomial.X (Sum.inl ())
      else -∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (ρ k) := by
  unfold imgR
  exact sac_same j0 _ _
end GaussValuationUniqueness
