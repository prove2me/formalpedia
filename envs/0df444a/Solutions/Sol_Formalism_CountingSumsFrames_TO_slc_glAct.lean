-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.slc_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:38.903595+00:00
-- url     : https://prove2.me/submissions/b644a033-75dc-436c-87b7-01444f1281c6

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_sl_mul
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isL_monomial_ltr
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_monomial_frst
import Theorems.Thm_Formalism_CountingSumsFrames_TO_monomial_split
import Theorems.Thm_Formalism_CountingSumsFrames_TO_glAct_isF
import Theorems.Thm_Formalism_CountingSumsFrames_TO_killL_of_isL
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_mul_kill
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_add


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
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : J ≤ j0) (c d : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    slc (fsj N r j0) m (glAct p L J c d x) = glAct p L J c d (slc (fsj N r j0) m x) := by
  induction x using MvPolynomial.induction_on' with
  | monomial m' a =>
    rw [monomial_split (fsj N r j0) m' a,
      glAct_mul_kill L J c d _ (killL_of_isL hJ (isL_monomial_ltr _ m' 1)),
      sl_mul _ m (glAct_isF L j0 J c d (isF_monomial_frst _ m' a)) (isL_monomial_ltr _ m' 1),
      sl_mul _ m (isF_monomial_frst _ m' a) (isL_monomial_ltr _ m' 1), map_smul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
end Formalism.CountingSumsFrames.TO
