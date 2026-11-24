-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.midAct_mul_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:37.18103+00:00
-- url     : https://prove2.me/submissions/32a18836-3304-4b5e-8b7c-17e1ddbee99a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_midAct_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_midAct_eq
import Theorems.Thm_Formalism_GM_M_FB_glAct_mul


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
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {g q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsF (fsj N r j0) g) : midAct p L j0 J c d (g * q) = g * midAct p L j0 J c d q := by
  have h0 := midAct_isF L j0 J c d hg
  rw [midAct_eq L hJ] at h0 ⊢
  rw [midAct_eq L hJ c d q, Formalism.GM.M.FB.glAct_mul, Formalism.GM.M.FB.glAct_mul]
  have : q * glAct p L J c d g - q * glAct p L j0 c d g = 0 := by rw [← mul_sub, h0, mul_zero]
  linear_combination this
end Formalism.CountingSumsFrames.TO
