-- Prove2me | solution 1 for GaussValuationUniqueness.sImg_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:30.142802+00:00
-- url     : https://prove2.me/submissions/aaccb3dc-25cd-4d20-be70-19f65c8b441e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_SHomFactor
import Theorems.Thm_GaussValuationUniqueness_sac_same
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
theorem _root_.solution {Ω : Type} [Field Ω] {D N : ℕ} (jc : Fin (N + 1)) (b : Fin (N + 1) → Ω)
    (hb : b jc = 1) (i : Fin (D + 1)) (hi : i ≠ 0) :
    ∑ j, sImg (D := D) jc (fun k => b (jc.succAbove k)) (i, j) *
      algebraMap Ω (OmS Ω D N) (b j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc]
  simp only [sImg, GaussValuationUniqueness.sac_same, GaussValuationUniqueness.sac_succAbove, if_neg hi, hb, map_one,
    mul_one]
  simp only [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, ← map_mul, ← map_sum, ← map_add, neg_add_cancel, map_zero]
end GaussValuationUniqueness
