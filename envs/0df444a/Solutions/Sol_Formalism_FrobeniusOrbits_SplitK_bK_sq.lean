-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.bK_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:04.314817+00:00
-- url     : https://prove2.me/submissions/9532536b-01d9-4ee9-a03f-89f0a1cf6223

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hb : b ^ 2 = -(d : L)) : bK b ^ 2 = -(d : Kd b) := by
  first
  | exact Subtype.ext (by simp [bK, hb])
  | (apply Subtype.ext; simp [bK, hb])
  | (apply Subtype.ext; push_cast [bK]; exact hb)
end Formalism.FrobeniusOrbits.SplitK
