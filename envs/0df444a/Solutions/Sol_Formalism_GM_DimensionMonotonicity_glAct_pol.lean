-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.glAct_pol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:08.392123+00:00
-- url     : https://prove2.me/submissions/4e8c93d0-bc3f-45a6-a00d-e006036b791e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_pol_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_wL

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
theorem _root_.solution (LL L2 : Letters N) (j : ℕ) (a b : Fin r) {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ Pol p r L2) : glAct p LL j a b x ∈ Pol p r L2 := by
  rw [pol_iff] at hx ⊢
  have h := glAct_wL LL j a b (by rw [mem_weightedHomogeneousSubmodule]; exact hx)
  rw [mem_weightedHomogeneousSubmodule] at h
  exact h
end Formalism.GM.DimensionMonotonicity
