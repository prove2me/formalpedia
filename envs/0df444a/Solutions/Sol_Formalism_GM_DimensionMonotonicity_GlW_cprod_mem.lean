-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.cprod_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:45.222918+00:00
-- url     : https://prove2.me/submissions/6fa91f21-b2b4-4c98-97d1-c157e482c6a0

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_Cas_mem
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_cprod_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open Finset
open Formalism.GM.DimensionMonotonicity.GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {U : Submodule K V} (hU : G.Stable U) (cs : List ℤ) {x : V} (hx : x ∈ U) :
    G.cprod cs x ∈ U := by
  induction cs with
  | nil => exact hx
  | cons c cs ih =>
    rw [cprod_cons]
    exact U.sub_mem (G.Cas_mem hU ih) (U.smul_mem _ ih)
end Formalism.GM.DimensionMonotonicity.GlW
