-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.geom_tail
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:36.59677+00:00
-- url     : https://prove2.me/submissions/087223e3-d67f-47cf-b91f-da3c11890a34

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (q N m : ℕ) (hq : 2 ≤ q) (hN : 2 ≤ N) (hm : m ≤ N) :
    ∑ j ∈ Finset.Icc 2 m, q ^ (N - j) ≤ 2 * q ^ (N - 2) := by
  have key : ∀ m, 1 ≤ m → m ≤ N →
      (∑ j ∈ Finset.Icc 2 m, q ^ (N - j)) * (q - 1) + q ^ (N - m) = q ^ (N - 1) := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ m ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; simp
      · rw [Finset.sum_Icc_succ_top (by omega), add_mul, add_assoc]
        have e : q ^ (N - (m + 1)) * (q - 1) + q ^ (N - (m + 1)) = q ^ (N - m) := by
          have h3 : N - m = (N - (m + 1)) + 1 := by omega
          rw [h3, pow_succ, ← Nat.mul_succ]
          congr 1
          omega
        rw [e]
        exact ih hm (by omega)
  by_cases hm1 : 1 ≤ m
  · have h := key m hm1 hm
    have hN1 : q ^ (N - 1) = q ^ (N - 2) * q := by
      rw [← pow_succ]; congr 1; omega
    obtain ⟨p, hp⟩ : ∃ p, q = p + 2 := ⟨q - 2, by omega⟩
    subst hp
    have hq1 : p + 2 - 1 = p + 1 := by omega
    rw [hq1, hN1] at h
    set S := ∑ j ∈ Finset.Icc 2 m, (p + 2) ^ (N - j)
    set Q := (p + 2) ^ (N - 2)
    by_contra hc
    push_neg at hc
    have h4 := Nat.mul_le_mul_right (p + 1) (show 2 * Q + 1 ≤ S by omega)
    clear_value S Q
    ring_nf at h h4
    nlinarith [Nat.zero_le (p * Q), Nat.zero_le ((2 + p) ^ (N - m))]
  · have : m = 0 := by omega
    subst this
    simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
