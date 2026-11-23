-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unitriangularReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:19.464163+00:00
-- url     : https://prove2.me/submissions/570b4745-9ed5-48c2-b6a8-e7980e219ff2

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : UnipotentReduce := by
  intro E _ O FF N u hFF hu1 hu0
  classical
  have key : ∀ t : ℕ, ∃ n : Matrix (Fin N) (Fin N) E, (∀ i, n i i = 1) ∧
      (∀ i j, j < i → n i j = 0) ∧ (∀ i j, n i j ∈ O) ∧
      ∀ i j : Fin N, i < j → N ≤ (i:ℕ) + t → (u * n) i j ∈ FF := by
    intro t
    induction t with
    | zero =>
      refine ⟨1, by simp, fun i j h => Matrix.one_apply_ne h.ne', fun i j => ?_,
        fun i j _ h => absurd i.2 (by omega)⟩
      rw [Matrix.one_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    | succ t ih =>
      obtain ⟨n, h1, h0, hO, hF⟩ := ih
      by_cases ht : t < N
      · let s : Fin N := ⟨N - t - 1, by omega⟩
        choose a ha using fun j : Fin N =>
          hFF (∑ k ∈ Finset.univ.filter (fun k => s < k), u s k * n k j)
        let n' : Matrix (Fin N) (Fin N) E := n.updateRow s (fun j => if s < j then a j else n s j)
        have hn's : ∀ j, n' s j = if s < j then a j else n s j := fun j => by
          simp [n', Matrix.updateRow_self]
        have hn'ne : ∀ i j, i ≠ s → n' i j = n i j := fun i j hi => by
          simp [n', Matrix.updateRow_ne hi]
        have hmul : ∀ i j, (u * n') i j = (u * n) i j + u i s * (n' s j - n s j) := by
          intro i j
          simp only [Matrix.mul_apply]
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s),
            ← Finset.add_sum_erase Finset.univ (fun k => u i k * n k j) (Finset.mem_univ s)]
          have : ∑ k ∈ Finset.univ.erase s, u i k * n' k j =
              ∑ k ∈ Finset.univ.erase s, u i k * n k j :=
            Finset.sum_congr rfl fun k hk => by rw [hn'ne k j (Finset.ne_of_mem_erase hk)]
          rw [this]; ring
        refine ⟨n', ?_, ?_, ?_, ?_⟩
        · intro i
          by_cases hi : i = s
          · subst hi; rw [hn's, if_neg (lt_irrefl _), h1]
          · rw [hn'ne i i hi, h1]
        · intro i j hji
          by_cases hi : i = s
          · subst hi; rw [hn's, if_neg (not_lt.2 hji.le), h0 _ _ hji]
          · rw [hn'ne i j hi, h0 _ _ hji]
        · intro i j
          by_cases hi : i = s
          · subst hi; rw [hn's]; split_ifs
            · exact (ha j).1
            · exact hO _ _
          · rw [hn'ne i j hi]; exact hO _ _
        · intro i j hij hi
          rw [hmul]
          by_cases his : i = s
          · subst his
            rw [hu1, hn's, if_pos hij]
            have hsplit : (u * n) s j = n s j +
                ∑ k ∈ Finset.univ.filter (fun k => s < k), u s k * n k j := by
              rw [Matrix.mul_apply, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => s < k)]
              rw [add_comm]; congr 1
              rw [Finset.sum_eq_single s]
              · rw [hu1, one_mul]
              · intro k hk hki
                have : k < s := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hk).2) hki
                rw [hu0 _ _ this, zero_mul]
              · intro h; exact (h (by simp)).elim
            rw [hsplit]
            have := (ha j).2
            convert this using 1; ring
          · have hsi : s < i := by
              rw [Fin.lt_def]
              have : (i : ℕ) ≠ (s : ℕ) := fun h => his (Fin.ext h)
              have hs : (s : ℕ) = N - t - 1 := rfl
              omega
            rw [hu0 _ _ hsi, zero_mul, add_zero]
            apply hF i j hij
            have hs : (s : ℕ) = N - t - 1 := rfl
            rw [Fin.lt_def] at hsi
            omega
      · exact ⟨n, h1, h0, hO, fun i j hij _ => hF i j hij (by omega)⟩
  obtain ⟨n, h1, h0, hO, hF⟩ := key N
  exact ⟨n, h1, h0, hO, fun i j hij => hF i j hij (by omega)⟩
end Formalism.HermitianLatticeCounting.P
