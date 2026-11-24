-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.killL_of_isL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:28.386937+00:00
-- url     : https://prove2.me/submissions/0fb0750c-8658-4695-be23-ea705a15c4d7

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution {j0 J : ℕ} (hJ : J ≤ j0) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hq : IsL (fsj N r j0) q) :
    ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < J → m v = 0 := by
  intro m hm v hv
  by_contra hne
  exact hq m hm v hne (show fsj N r j0 v from lt_of_lt_of_le hv hJ)
end Formalism.CountingSumsFrames.TO
