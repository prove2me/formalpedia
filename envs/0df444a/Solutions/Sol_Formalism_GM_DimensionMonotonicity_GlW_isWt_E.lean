-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.isWt_E
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:06.644175+00:00
-- url     : https://prove2.me/submissions/24389051-e155-48c9-a3d8-b82768101b0a

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
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
namespace Formalism.GM.DimensionMonotonicity.GlW
theorem _root_.solution {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (a b : Fin r) :
    G.IsWt (ν + dl a b) (G.E a b x) := by
  show G.comp (ν + dl a b) (G.E a b x) = G.E a b x
  rw [G.shift, add_sub_cancel_right, show G.comp ν x = x from h]
end Formalism.GM.DimensionMonotonicity.GlW
