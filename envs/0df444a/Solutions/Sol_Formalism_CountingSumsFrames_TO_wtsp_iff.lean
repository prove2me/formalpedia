-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.wtsp_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:28.071086+00:00
-- url     : https://prove2.me/submissions/b12b60bc-644b-4dc2-8615-2b4b49126ffd

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {M : ℕ} (L : Letters M) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ la ↔ IsWeightedHomogeneous (wv L j) x la := by
  rw [WtSpC, mem_restrictSupport_iff]
  constructor
  · intro h m hm
    funext c
    rw [weight_wv]
    exact h (Finset.mem_coe.mpr (mem_support_iff.mpr hm)) c (mem_univ c)
  · intro h m hm c _
    rw [← weight_wv, h (mem_support_iff.mp (Finset.mem_coe.mp hm))]
end Formalism.CountingSumsFrames.TO
