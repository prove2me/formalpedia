-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Y_fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:45.241483+00:00
-- url     : https://prove2.me/submissions/00160d08-4277-4fc3-9500-21a3e52df8de

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_fd


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
theorem _root_.solution [NeZero r] (L : Letters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    FiniteDimensional ℚ_[p] (Y p (r := r) L J M) := by
  have := pol_fd (p := p) (r := r) L
  exact Submodule.finiteDimensional_of_le (inf_le_left : Y p (r := r) L J M ≤ Pol p r L)
end Formalism.CountingSumsFrames.TO
