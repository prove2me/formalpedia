-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.iso_keep_glAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:49.452342+00:00
-- url     : https://prove2.me/submissions/401f9e7a-c446-45b0-8df9-5a3564a0063a

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_iso_keep_comm
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_glStable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_midAct_comm


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
theorem _root_.solution (L : Letters N) {j j0 : ℕ} (hj : j ≤ j0) (c d : Fin r) (la : Fin r → ℤ) :
    ∀ x ∈ IsoC p L j univ la, glAct p L j0 c d x ∈ IsoC p L j univ la := by
  intro x hx
  rw [glAct_split L hj c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (isoC_glStable L j la c d x hx)
    (iso_keep_comm L j (midAct p L j j0 c d) (fun c' d' y => midAct_comm L j j0 c d c' d' y) la x hx)
end Formalism.CountingSumsFrames.TO
