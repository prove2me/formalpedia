-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Cas_mul_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:07.267301+00:00
-- url     : https://prove2.me/submissions/734961bf-5ca1-427b-86da-97d15add602b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_apply
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_mul_kill

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
theorem _root_.solution (LL : Letters N) (j0 : ℕ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).Cas (y * q) = (GA p LL j0).Cas y * q := by
  rw [GlW.Cas_apply, GlW.Cas_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  show glAct p LL j0 a b (glAct p LL j0 b a (y * q)) = glAct p LL j0 a b (glAct p LL j0 b a y) * q
  rw [glAct_mul_kill LL j0 b a y hq, glAct_mul_kill LL j0 a b _ hq]
end Formalism.GM.DimensionMonotonicity
