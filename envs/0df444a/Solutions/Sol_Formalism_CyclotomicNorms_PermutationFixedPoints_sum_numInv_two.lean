-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.sum_numInv_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:48.250886+00:00
-- url     : https://prove2.me/submissions/b9ccb454-1eb5-4a39-bf75-62b7a52a14b6

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
    ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0) =
      ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
        (univ.filter (fun σ : Equiv.Perm (Fin N) =>
          (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by
  calc ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0)
      = ∑ σ : Equiv.Perm (Fin N), ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
          (if ((∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ) then 1 else 0) := by
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        by_cases h : 2 ≤ numInv N a σ
        · simp only [h, if_true, and_true]
          rw [numInv, Finset.card_filter]
        · simp [h]
    _ = _ := by
        rw [Finset.sum_comm]
        simp only [Finset.card_filter]
end Formalism.CyclotomicNorms.PermutationFixedPoints
