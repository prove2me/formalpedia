-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.Lw_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:31.564206+00:00
-- url     : https://prove2.me/submissions/64cc6f90-cc89-44fe-ba0f-bf5fa1983b61

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
theorem _root_.solution (v : V) {U : Submodule K V} (hv : v ∈ U) (hU : ∀ a b, b < a → ∀ x ∈ U, G.E a b x ∈ U) :
    G.Lw v ≤ U := by
  apply sInf_le
  exact ⟨hv, hU⟩
end Formalism.GM.DimensionMonotonicity.GlW
