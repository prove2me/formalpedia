-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.inv_exchange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:39.668274+00:00
-- url     : https://prove2.me/submissions/19c7ae70-d6f3-4093-9614-0ec69f8868c1

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
theorem _root_.solution {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) (S : Finset α)
    (hS : ∀ z, σ z ∈ S ↔ z ∈ S) (x y : α) (hx : σ x = x) (hy : σ y = y) :
    ∀ z, σ z ∈ insert y (S.erase x) ↔ z ∈ insert y (S.erase x) := by
  intro z
  have e1 : σ z = y ↔ z = y :=
    ⟨fun h => σ.injective (h.trans hy.symm), fun h => h ▸ hy⟩
  have e2 : σ z = x ↔ z = x :=
    ⟨fun h => σ.injective (h.trans hx.symm), fun h => h ▸ hx⟩
  simp only [Finset.mem_insert, Finset.mem_erase, ne_eq, e1, e2, hS]
end Formalism.CyclotomicNorms.PermutationFixedPoints
