-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.Lw_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:11.185346+00:00
-- url     : https://prove2.me/submissions/81a7ba9b-3850-410b-928a-51c891185e4f

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone

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
theorem _root_.solution (v : V) {a b : Fin r} (h : b < a) {x : V} (hx : x ∈ G.Lw v) : G.E a b x ∈ G.Lw v := by
  exact Submodule.mem_sInf.mpr fun U hU => hU.2 a b h x (Submodule.mem_sInf.mp hx U hU)
end Formalism.GM.DimensionMonotonicity.GlW
