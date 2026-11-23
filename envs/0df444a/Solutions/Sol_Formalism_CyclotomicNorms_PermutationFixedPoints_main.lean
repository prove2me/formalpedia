-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:56.533869+00:00
-- url     : https://prove2.me/submissions/1defef59-c791-4399-9012-378e84695469

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_map_eq_iff
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_sum_numInv
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_sum_numInv_two
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_stab_le
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_good_ge

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
theorem _root_.solution : PermFixedSet := by
  intro N a ha haN
  have hpt : ∀ σ : Equiv.Perm (Fin N),
      8 * (if (∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S) then 1 else 0) +
        4 * (if 2 ≤ numInv N a σ then numInv N a σ else 0) ≤ 8 * numInv N a σ := by
    intro σ
    by_cases hA : ∃ S : Finset (Fin N), S.card = a ∧ S.map σ.toEmbedding = S
    · have h1 : 1 ≤ numInv N a σ := by
        obtain ⟨S, hSc, hSm⟩ := hA
        unfold numInv
        apply Finset.card_pos.2
        refine ⟨S, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        exact ⟨⟨Finset.subset_univ _, hSc⟩, (map_eq_iff σ S).1 hSm⟩
      rw [if_pos hA]
      split_ifs <;> omega
    · rw [if_neg hA]
      split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Equiv.Perm (Fin N)))) (fun σ _ => hpt σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.card_filter] at hsum
  have hconst : ∑ S ∈ (univ : Finset (Fin N)).powersetCard a,
      a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin, ← mul_assoc, Nat.choose_mul_factorial_mul_factorial haN.le]
  have hX : ∑ σ : Equiv.Perm (Fin N), numInv N a σ ≤ N.factorial := by
    rw [sum_numInv, ← hconst]
    refine Finset.sum_le_sum (fun S hS => ?_)
    rw [Finset.mem_powersetCard] at hS
    have := card_stab_le N S
    rwa [hS.2] at this
  have hX2 : N.factorial ≤
      4 * ∑ σ : Equiv.Perm (Fin N), (if 2 ≤ numInv N a σ then numInv N a σ else 0) := by
    rw [sum_numInv_two, Finset.mul_sum, ← hconst]
    refine Finset.sum_le_sum (fun S hS => ?_)
    rw [Finset.mem_powersetCard] at hS
    exact card_good_ge N a ha haN S hS.2
  omega
end Formalism.CyclotomicNorms.PermutationFixedPoints
