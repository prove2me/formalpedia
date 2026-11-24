-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.comp_cprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:10.553628+00:00
-- url     : https://prove2.me/submissions/214e82c5-5ddc-4837-b06c-acb67359ff4e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_comp_Cas
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
theorem _root_.solution (μ : Fin r → ℤ) (cs : List ℤ) (x : V) :
    G.comp μ (G.cprod cs x) = G.cprod cs (G.comp μ x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [cprod_cons, cprod_cons, map_sub, map_smul, G.comp_Cas, ih]
end Formalism.GM.DimensionMonotonicity.GlW
