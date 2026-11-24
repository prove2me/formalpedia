-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.smul_mem_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:42.950956+00:00
-- url     : https://prove2.me/submissions/21a1b6e1-307c-43ca-bfea-9c8b6d8aeb45

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
theorem _root_.solution (σ : Kd b ≃ₐ[ℚ] Kd b) (P : Ideal (𝓞 (Kd b))) (h : σ • P = P)
    (y : 𝓞 (Kd b)) (hy : y ∈ P) : σ • y ∈ P := by
  first
  | (have h1 := Ideal.smul_mem_pointwise_smul σ y P hy; rwa [h] at h1)
  | (rw [← h]; exact Ideal.smul_mem_pointwise_smul σ y P hy)
  | (rw [← h]; exact Ideal.mem_map_of_mem _ hy)
end Formalism.FrobeniusOrbits.SplitK
