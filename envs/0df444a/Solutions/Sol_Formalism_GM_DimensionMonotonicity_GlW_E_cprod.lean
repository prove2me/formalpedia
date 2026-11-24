-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.E_cprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:44:47.787969+00:00
-- url     : https://prove2.me/submissions/4a3962b3-abd4-4a18-b6b1-16e1321ecc76

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_E_Cas
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
theorem _root_.solution (a b : Fin r) (cs : List ℤ) (x : V) : G.E a b (G.cprod cs x) = G.cprod cs (G.E a b x) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [cprod_cons, cprod_cons, map_sub, map_smul, G.E_Cas, ih]
end Formalism.GM.DimensionMonotonicity.GlW
