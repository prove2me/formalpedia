-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.midAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:35.408808+00:00
-- url     : https://prove2.me/submissions/1f21ae80-50ea-40db-8d1b-1ea4bd801335

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    midAct p L j0 J c d x = glAct p L J c d x - glAct p L j0 c d x := by
  rw [glAct_split L hJ c d, LinearMap.add_apply]; abel
end Formalism.CountingSumsFrames.TO
