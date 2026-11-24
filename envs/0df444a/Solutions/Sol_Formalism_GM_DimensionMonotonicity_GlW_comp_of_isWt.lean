-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.comp_of_isWt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:56.303786+00:00
-- url     : https://prove2.me/submissions/dd742706-7b6a-47a7-9d12-87b9613f8dea

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
theorem _root_.solution {μ ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) :
    G.comp μ x = if μ = ν then x else 0 := by
  have h' : G.comp ν x = x := h
  calc G.comp μ x = G.comp μ (G.comp ν x) := by rw [h']
    _ = if μ = ν then x else 0 := by rw [G.idem, h']
end Formalism.GM.DimensionMonotonicity.GlW
