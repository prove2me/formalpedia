-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.wtsp_iff_wh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:14.320661+00:00
-- url     : https://prove2.me/submissions/efac20d4-8181-4992-8ff5-f5651cc48dfd

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
theorem _root_.solution (L : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ μ ↔ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j) μ := by
  rw [WtSpC, mem_restrictSupport_iff, mem_weightedHomogeneousSubmodule]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (Finset.mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]
end Formalism.CountingSumsFrames.TO
