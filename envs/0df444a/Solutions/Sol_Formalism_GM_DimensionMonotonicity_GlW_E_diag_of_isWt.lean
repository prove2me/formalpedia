-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.GlW.E_diag_of_isWt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:32:06.662896+00:00
-- url     : https://prove2.me/submissions/f69bf3f8-291e-4a62-a99d-16b8c7e2714f

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
theorem _root_.solution {ν : Fin r → ℤ} {x : V} (h : G.IsWt ν x) (c : Fin r) :
    G.E c c x = ((ν c : ℤ) : K) • x := by
  have h' : G.comp ν x = x := h
  have h2 := G.diag c ν x
  rwa [h'] at h2
end Formalism.GM.DimensionMonotonicity.GlW
