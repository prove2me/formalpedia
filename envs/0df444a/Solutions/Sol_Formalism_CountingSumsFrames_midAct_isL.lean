-- Prove2me | solution 1 for Formalism.CountingSumsFrames.midAct_isL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:43.984263+00:00
-- url     : https://prove2.me/submissions/548435a0-518f-4897-a1ab-854a68e27297

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_isL_iff
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_isL
import Theorems.Thm_Formalism_CountingSumsFrames_midAct_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (c d : Fin r) {q : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hq : IsL (fsj N r j0) q) : IsL (fsj N r j0) (midAct p L j0 J c d q) := by
  rw [midAct_eq L hJ, isL_iff]
  exact Submodule.sub_mem _ ((isL_iff _ _).mp (glAct_isL L j0 J c d hq)) ((isL_iff _ _).mp (glAct_isL L j0 j0 c d hq))
end Formalism.CountingSumsFrames
