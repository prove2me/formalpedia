-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger90_masked_monotone_grid_Ioc_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:10:53.382014+00:00
-- url     : https://prove2.me/submissions/657d8600-4251-4cc2-970e-824cddaf9c31

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (S : Set ℝ) (hS : MeasurableSet S)
    (v : ℕ → ℝ) (hv : Monotone v) (k : ℕ) :
    (∑ i ∈ Finset.range k,
      ∫⁻ s in S ∩ Ioc (v i) (v (i + 1)), f s ∂μ) =
    ∫⁻ s in S ∩ Ioc (v 0) (v k), f s ∂μ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmid : v 0 ≤ v k := hv (Nat.zero_le k)
      have hlast : v k ≤ v (k + 1) := hv (Nat.le_succ k)
      have hset : S ∩ Ioc (v 0) (v (k + 1)) =
          (S ∩ Ioc (v 0) (v k)) ∪ (S ∩ Ioc (v k) (v (k + 1))) := by
        ext t
        simp only [mem_inter_iff, mem_Ioc, mem_union]
        constructor
        · rintro ⟨hs, h0, ht⟩
          by_cases htk : t ≤ v k
          · exact Or.inl ⟨hs, h0, htk⟩
          · exact Or.inr ⟨hs, lt_of_not_ge htk, ht⟩
        · intro h
          rcases h with h | h
          · exact ⟨h.1, h.2.1, h.2.2.trans hlast⟩
          · exact ⟨h.1, lt_of_le_of_lt hmid h.2.1, h.2.2⟩
      have hd : Disjoint (S ∩ Ioc (v 0) (v k))
          (S ∩ Ioc (v k) (v (k + 1))) := by
        apply Set.disjoint_left.mpr
        intro t hA hB
        exact (not_lt_of_ge hA.2.2) hB.2.1
      rw [Finset.sum_range_succ, ih, hset,
        lintegral_union (hS.inter measurableSet_Ioc) hd]
