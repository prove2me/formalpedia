-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.smul_intCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:42.922895+00:00
-- url     : https://prove2.me/submissions/4cbdf193-0d0c-48e2-8f6a-e0b5738a6d93

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
theorem _root_.solution (σ : Kd b ≃ₐ[ℚ] Kd b) (n : ℤ) : σ • (n : 𝓞 (Kd b)) = n := by
  first
  | exact map_intCast (MulSemiringAction.toRingHom (Kd b ≃ₐ[ℚ] Kd b) (𝓞 (Kd b)) σ) n
  | simp
  | (rw [← MulSemiringAction.toRingHom_apply, map_intCast])
end Formalism.FrobeniusOrbits.SplitK
