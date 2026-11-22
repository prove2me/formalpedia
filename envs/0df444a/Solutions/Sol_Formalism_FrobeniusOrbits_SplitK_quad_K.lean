-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.quad_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:35:34.374228+00:00
-- url     : https://prove2.me/submissions/678e41b6-f124-4fab-b480-dd84e42929bc

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_finrank_K

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
theorem _root_.solution (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Algebra.IsQuadraticExtension ℚ (Kd b) := by
  first
  | exact ⟨finrank_K hd hb⟩
  | exact { finrank_eq_two' := finrank_K hd hb }
  | exact { toFree := inferInstance, finrank_eq_two' := finrank_K hd hb }
  | (constructor <;> first | exact finrank_K hd hb | exact inferInstance)
end Formalism.FrobeniusOrbits.SplitK
