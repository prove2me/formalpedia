-- Prove2me | solution 1 for GaussValuationUniqueness.imgR_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:23.954487+00:00
-- url     : https://prove2.me/submissions/25e8f9e1-d31f-4046-8bd9-a47f2b94f771

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Theorems.Thm_GaussValuationUniqueness_imgR_same
import Theorems.Thm_GaussValuationUniqueness_imgR_succAbove

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
theorem _root_.solution {R R' : Type*} [CommRing R] [CommRing R'] {D N : ℕ} (φ : R →+* R')
    (j0 : Fin (N + 1)) (ρ : Fin N → R) (t : TVar D N) :
    MvPolynomial.map φ (imgR j0 ρ t) = imgR j0 (fun k => φ (ρ k)) t := by
  obtain ⟨i, j⟩ := t
  rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
  · rw [imgR_same, imgR_same]
    split_ifs
    · exact MvPolynomial.map_X φ _
    · simp only [map_neg, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
  · rw [imgR_succAbove, imgR_succAbove, MvPolynomial.map_X]
end GaussValuationUniqueness
