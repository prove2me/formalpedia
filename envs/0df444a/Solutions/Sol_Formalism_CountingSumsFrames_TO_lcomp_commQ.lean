-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.lcomp_commQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:50.754166+00:00
-- url     : https://prove2.me/submissions/e17d652c-9715-4369-bdcb-840eb89d1bbf

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons


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
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (Q : V →ₗ[K] V) (h : ∀ j x, P j (Q x) = Q (P j x)) : ∀ (l : List ι) (x : V), lcomp P l (Q x) = Q (lcomp P l x)
  | [], _ => rfl
  | a :: l, x => by
    rw [lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply, solution P Q h l x, h a]
end Formalism.CountingSumsFrames.TO
