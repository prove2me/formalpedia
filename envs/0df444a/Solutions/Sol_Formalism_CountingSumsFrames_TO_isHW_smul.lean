-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.isHW_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:19.45714+00:00
-- url     : https://prove2.me/submissions/6bd69138-3dda-46ae-82bf-f7b97f16cbf7

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isHW_iff

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
theorem _root_.solution (L : Letters N) (j : ℕ) (la : Fin r → ℤ) (c : ℚ_[p]) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : (GA p L j).IsHW la x) : (GA p L j).IsHW la (c • x) := by
  rw [isHW_iff] at hx ⊢
  exact Submodule.smul_mem _ _ hx
end Formalism.CountingSumsFrames.TO
