-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.ycond_cprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:58:39.6731+00:00
-- url     : https://prove2.me/submissions/7ec55226-06ca-4fb4-811d-fdd4bffab59a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_comm_glAct
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Cas_wh

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
theorem _root_.solution [NeZero r] (LL : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (M : WithTop ℤ) (cs : List ℤ)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    (GA p LL j0).cprod cs F ∈ YCond p LL J M := by
  refine ycond_of_comm LL J M ((GA p LL j0).cprod cs) ?_ ?_ F hF
  · intro c d G
    induction cs with
    | nil => rfl
    | cons c0 cs ih =>
      rw [GlW.cprod_cons, GlW.cprod_cons, ih, Cas_comm_glAct LL hJ, map_sub, map_smul]
  · intro ν G hG
    induction cs with
    | nil => exact hG
    | cons c0 cs ih =>
      rw [GlW.cprod_cons]
      exact Submodule.sub_mem _ (Cas_wh LL hJ ih) (Submodule.smul_mem _ _ ih)
end Formalism.GM.DimensionMonotonicity
