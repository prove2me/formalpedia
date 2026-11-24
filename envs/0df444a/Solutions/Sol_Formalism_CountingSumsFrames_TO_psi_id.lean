-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.psi_id
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:09.692796+00:00
-- url     : https://prove2.me/submissions/e2c0df0f-76fd-4fc1-a671-564bd309cf29

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff


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
theorem _root_.solution (L : Letters N) (j0 : ℕ) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hx : x ∈ Pol p r (Lz L j0)) :
    psi p L j0 x = x := by
  rw [pol_iff] at hx
  rw [psi, weightedHomogeneousComponent_of_mem hx, if_pos rfl]
end Formalism.CountingSumsFrames.TO
