-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.bK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:41.601893+00:00
-- url     : https://prove2.me/submissions/275b48ab-53ef-460a-b6c8-59f2098bb3fe

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
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
private theorem bK_ne_neg_bK_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : bK b ≠ -bK b := by
  intro h
  have h2 : b = -b := by
    first
    | exact congrArg Subtype.val h
    | simpa [bK] using congrArg Subtype.val h
  have h3 : b = 0 := by
    have h4 : (2 : L) * b = 0 := by linear_combination h2
    rcases mul_eq_zero.mp h4 with h5 | h5
    · norm_num at h5
    · exact h5
  rw [h3] at hb
  have h6 : (d : L) = 0 := by linear_combination hb
  have h7 : d = 0 := by exact_mod_cast h6
  omega
end Formalism.FrobeniusOrbits.SplitK
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) : bK b ≠ 0 := by
  intro h
  apply bK_ne_neg_bK_of_sq_eq_neg hd0 hb
  rw [h, neg_zero]
end Formalism.FrobeniusOrbits.SplitK
