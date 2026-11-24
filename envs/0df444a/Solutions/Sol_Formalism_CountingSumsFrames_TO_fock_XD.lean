-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_XD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:36.231821+00:00
-- url     : https://prove2.me/submissions/3e00093d-6607-4ed2-9aa3-94e635075945

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_X_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_symm


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
theorem _root_.solution {σ : Type} [Fintype σ] [DecidableEq σ] (u v : σ) (x y : MvPolynomial σ ℚ_[p]) :
    fock p (X u * pderiv v x) y = fock p x (X v * pderiv u y) := by
  rw [gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm, ← gammaIntegralityLemmas.fock_X_mul, gammaIntegralityLemmas.fock_symm]
end Formalism.CountingSumsFrames.TO
