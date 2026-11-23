-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.map_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:39.755804+00:00
-- url     : https://prove2.me/submissions/2ec4ac6a-6a77-40db-b102-5472cf7e61c3

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
theorem _root_.solution {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α) :
    S.map σ.toEmbedding = S ↔ ∀ x, σ x ∈ S ↔ x ∈ S := by
  rw [Finset.ext_iff]
  simp only [Finset.mem_map_equiv]
  constructor
  · intro h x
    simpa using (h (σ x)).symm
  · intro h b
    simpa using (h (σ.symm b)).symm
end Formalism.CyclotomicNorms.PermutationFixedPoints
