-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.isWt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:05.108081+00:00
-- url     : https://prove2.me/submissions/dde62129-51c5-421c-86a5-c72bb5d91073

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    (GA p L j).IsWt la x ↔ x ∈ WtSpC p L j univ la := by
  show weightedHomogeneousComponent (wv L j) la x = x ↔ _
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm c _
    have hw : IsWeightedHomogeneous (wv L j) x la := by
      rw [← h]; exact weightedHomogeneousComponent_isWeightedHomogeneous la x
    rw [← weight_wv, hw (mem_support_iff.mp (Finset.mem_coe.mp hm))]
  · intro h
    apply weightedHomogeneousComponent_eq_self
    intro m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)
end Formalism.CountingSumsFrames.TO
