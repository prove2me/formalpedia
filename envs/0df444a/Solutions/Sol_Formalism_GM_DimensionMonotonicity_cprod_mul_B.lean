-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.cprod_mul_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:45.549526+00:00
-- url     : https://prove2.me/submissions/6ac7b8c7-d1ef-4ff2-824b-4428350dd68b

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_mul_B

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
theorem _root_.solution (LL : Letters N) (j0 : ℕ) (cs : List ℤ) (y q : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hq : ∀ m ∈ q.support, ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → m v = 0) :
    (GA p LL j0).cprod cs (y * q) = (GA p LL j0).cprod cs y * q := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [GlW.cprod_cons, GlW.cprod_cons, ih, Cas_mul_B LL j0 _ q hq, sub_mul, smul_mul_assoc]
end Formalism.GM.DimensionMonotonicity
