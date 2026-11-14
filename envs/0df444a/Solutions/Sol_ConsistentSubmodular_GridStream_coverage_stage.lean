-- Prove2me | solution 1 for ConsistentSubmodular.GridStream.coverage_stage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:28:45.805205+00:00
-- url     : https://prove2.me/submissions/b28d3606-fb72-428b-9e1d-57c11a85ebb7

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

section

noncomputable section

open scoped BigOperators

open Finset

namespace ConsistentSubmodular.GridStream

/-- Division with remainder for `a n + b` with `b < n`. -/
theorem mul_add_div_mod {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a ∧ (a * n + b) % n = b := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le b) hb
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

end ConsistentSubmodular.GridStream

end

end

section

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem solution {k m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    (k : ℝ) * k + k * j ≤ coverageValue (gridStreamCover k m) (stageColumns k m j) := by
  classical
  unfold coverageValue
  have hjmk : j * k ≤ m * k := Nat.mul_le_mul_right k hjm
  have hsucc : (j + 1) * k = j * k + k := Nat.succ_mul j k
  have hpred : j * k = (j - 1) * k + k := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hj1]
  set T := (stageColumns k m j).biUnion (gridStreamCover k m)
  have hcore : range (k * k) ⊆ T.map Fin.valEmbedding := by
    intro y hy
    have hy' : y < k * k := mem_range.mp hy
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        simp at hy'
      · exact h
    have hyk : y % k < k := Nat.mod_lt _ hk
    refine mem_map.mpr ⟨⟨y, by omega⟩, mem_biUnion.mpr ⟨⟨j * k + y % k, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp only [stageColumns, mem_filter, mem_univ, true_and]
      omega
    · simp only [gridStreamCover, mem_filter, mem_univ, true_and]
      rw [if_neg (by omega)]
      refine Or.inl ⟨hy', ?_⟩
      rw [show j * k + y % k - k = (j - 1) * k + y % k by omega, (mul_add_div_mod hyk).2]
  have haux : ((range k ×ˢ range j).image fun p => k * k + p.1 * m + p.2) ⊆
      T.map Fin.valEmbedding := by
    intro y hy
    obtain ⟨⟨i, l⟩, hil, rfl⟩ := mem_image.mp hy
    obtain ⟨hi, hl⟩ := mem_product.mp hil
    have hi' : i < k := mem_range.mp hi
    have hl' : l < j := mem_range.mp hl
    have hlm : l < m := by omega
    have him : (i + 1) * m ≤ k * m := Nat.mul_le_mul_right m hi'
    have hisucc : (i + 1) * m = i * m + m := Nat.succ_mul i m
    refine mem_map.mpr ⟨⟨k * k + i * m + l, by omega⟩,
      mem_biUnion.mpr ⟨⟨j * k + i, by omega⟩, ?_, ?_⟩, rfl⟩
    · simp only [stageColumns, mem_filter, mem_univ, true_and]
      omega
    · simp only [gridStreamCover, mem_filter, mem_univ, true_and]
      rw [if_neg (by omega)]
      refine Or.inr ⟨by omega, ?_, ?_⟩
      · rw [show k * k + i * m + l - k * k = i * m + l by omega,
          show j * k + i - k = (j - 1) * k + i by omega, (mul_add_div_mod hlm).1,
          (mul_add_div_mod hi').2]
      · rw [show k * k + i * m + l - k * k = i * m + l by omega,
          show j * k + i - k = (j - 1) * k + i by omega, (mul_add_div_mod hlm).2,
          (mul_add_div_mod hi').1]
        omega
  have hdisj : Disjoint (range (k * k))
      ((range k ×ˢ range j).image fun p => k * k + p.1 * m + p.2) := by
    rw [disjoint_left]
    intro a ha hb
    obtain ⟨p, -, rfl⟩ := mem_image.mp hb
    have := mem_range.mp ha
    omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => k * k + p.1 * m + p.2) ↑(range k ×ˢ range j) := by
    intro p hp q hq hpq
    have hp2 : p.2 < m := by
      have := (mem_product.mp (mem_coe.mp hp)).2
      have := mem_range.mp this
      omega
    have hq2 : q.2 < m := by
      have := (mem_product.mp (mem_coe.mp hq)).2
      have := mem_range.mp this
      omega
    have hpq' : p.1 * m + p.2 = q.1 * m + q.2 := by
      simp only at hpq
      omega
    have h1 := mul_add_div_mod (a := p.1) hp2
    have h2 := mul_add_div_mod (a := q.1) hq2
    rw [hpq'] at h1
    exact Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)
  have hcard := card_le_card (union_subset hcore haux)
  rw [card_union_of_disjoint hdisj, card_range, card_image_of_injOn hinj, card_product,
    card_range, card_range, card_map] at hcard
  exact_mod_cast hcard

end
