-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger88_monotone_grid_Ioc_cash_exact_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:01:59.16908+00:00
-- url     : https://prove2.me/submissions/1731ddaf-a218-440f-b6e7-0038244a631a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in Ioc (v i) (v (i + 1)), f s ∂μ) =
    ∫⁻ s in Ioc (v 0) (v k), f s ∂μ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmid : v 0 ≤ v k := hv (Nat.zero_le k)
      have hlast : v k ≤ v (k + 1) := hv (Nat.le_succ k)
      have hset : Ioc (v 0) (v (k + 1)) =
          Ioc (v 0) (v k) ∪ Ioc (v k) (v (k + 1)) := by
        ext t
        simp only [mem_Ioc, mem_union]
        constructor
        · rintro ⟨h0, ht⟩
          by_cases htk : t ≤ v k
          · exact Or.inl ⟨h0, htk⟩
          · exact Or.inr ⟨lt_of_not_ge htk, ht⟩
        · intro h
          rcases h with h | h
          · exact ⟨h.1, h.2.trans hlast⟩
          · exact ⟨lt_of_le_of_lt hmid h.1, h.2⟩
      have hd : Disjoint (Ioc (v 0) (v k)) (Ioc (v k) (v (k + 1))) := by
        apply Set.disjoint_left.mpr
        intro t hA hB
        exact (not_lt_of_ge hA.2) hB.1
      rw [Finset.sum_range_succ, ih, hset,
        lintegral_union measurableSet_Ioc hd]
