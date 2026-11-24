-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.apply_bK_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:50.07475+00:00
-- url     : https://prove2.me/submissions/f73b58e8-5535-4b4d-b918-06f72f3a306c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_bK_sq
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_gal_eq_one_of_fix
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
private theorem Kd_algEquiv_bK_eq_or_eq_neg (hb : b ^ 2 = -(d : L)) (σ : Kd b ≃ₐ[ℚ] Kd b) :
    σ (bK b) = bK b ∨ σ (bK b) = -bK b := by
  have h1 : σ (bK b) ^ 2 = bK b ^ 2 := by
    first
    | rw [← map_pow, bK_sq hb, map_neg, map_natCast]
    | (rw [← map_pow, bK_sq hb]; simp)
  have h2 : (σ (bK b) - bK b) * (σ (bK b) + bK b) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h | h
  · left
    linear_combination h
  · right
    linear_combination h
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
theorem _root_.solution (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (ι : Kd b ≃ₐ[ℚ] Kd b) (hι : ι ≠ 1) :
    ι (bK b) = -bK b := by
  rcases Kd_algEquiv_bK_eq_or_eq_neg hb ι with h | h
  · exact absurd (gal_eq_one_of_fix ι h) hι
  · exact h
end Formalism.FrobeniusOrbits.SplitK
