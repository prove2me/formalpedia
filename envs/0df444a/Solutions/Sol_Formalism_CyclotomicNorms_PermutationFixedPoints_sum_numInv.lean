-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:48.25138+00:00
-- url     : https://prove2.me/submissions/e0daba2d-d8e2-4d0a-9cac-b130e79ad279

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
theorem _root_.solution (N a : ℕ) :
    ∑ σ : Equiv.Perm (Fin N), numInv N a σ =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) => ∀ x, σ x ∈ S ↔ x ∈ S)).card := by
  simp only [numInv, Finset.card_filter]
  exact Finset.sum_comm
end Formalism.CyclotomicNorms.PermutationFixedPoints
