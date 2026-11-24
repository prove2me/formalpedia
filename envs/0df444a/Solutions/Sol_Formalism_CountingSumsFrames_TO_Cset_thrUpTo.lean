-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Cset_thrUpTo
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:22.142802+00:00
-- url     : https://prove2.me/submissions/c5a518c6-aee4-4c38-93c0-986446897bdf

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_congr
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution [NeZero r] (L : Letters N) (T : TieData) (i : Fin T.t) :
    Cset p (r := r) L (T.pos i + 1 + 1) T.J (T.thrUpTo i) = Cset p L (T.pos i + 1 + 1) T.J T.thr := by
  unfold Cset
  congr 1
  refine iInf_congr fun k => ?_
  unfold Mup TieData.thrUpTo
  by_cases h : T.J k < T.pos i + 1 + 1
  · rw [if_pos h, if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg h]
end Formalism.CountingSumsFrames.TO
