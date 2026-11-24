-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.isWt_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:32.366645+00:00
-- url     : https://prove2.me/submissions/34f12f2f-7090-4df7-ae66-e3cfa56e86b1

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
theorem _root_.solution (μ : Fin r → ℤ) (x : V) : G.IsWt μ (G.comp μ x) := by
  show G.comp μ (G.comp μ x) = G.comp μ x
  rw [G.idem, if_pos rfl]
end Formalism.GM.DimensionMonotonicity.GlW
