-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.pol_finW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:44.341402+00:00
-- url     : https://prove2.me/submissions/3e9e85a5-6d40-4413-8066-8bc6eef1b13a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) (j : ℕ) : (GA p LL j).FinW (Pol p r LL) := by
  classical
  refine ⟨(pol_finite (r := r) LL).toFinset.image (Finsupp.weight (wv LL j)), fun x hx μ hμ => ?_⟩
  show weightedHomogeneousComponent (wv LL j) μ x = 0
  unfold Pol at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  apply weightedHomogeneousComponent_eq_zero'
  intro d hd hw
  apply hμ
  rw [Finset.mem_image]
  refine ⟨d, ?_, hw⟩
  rw [Set.Finite.mem_toFinset]
  exact hx hd
end Formalism.GM.DimensionMonotonicity
