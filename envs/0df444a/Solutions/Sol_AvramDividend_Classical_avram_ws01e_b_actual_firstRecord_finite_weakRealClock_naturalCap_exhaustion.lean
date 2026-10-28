-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_actual_firstRecord_finite_weakRealClock_naturalCap_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T16:11:51.150343+00:00
-- url     : https://prove2.me/submissions/a130c7f1-687c-4719-bddc-7285be56e1cb

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    ({ω : Ω | twoSidedExitUpTime X b ω < ⊤} =
      ⋃ n : ℕ, {ω : Ω |
        twoSidedExitUpTime X b ω < (n : ℝ≥0∞)}) ∧
    ({z : Ω × ℝ |
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2} =
      ⋃ n : ℕ, {z : Ω × ℝ |
        twoSidedExitUpTime X b z.1 < (n : ℝ≥0∞) ∧
        ((twoSidedExitUpTime X b z.1).toNNReal : ℝ) ≤ z.2}) := by
  let T : Ω → ℝ≥0∞ := twoSidedExitUpTime X b
  have hFinite (ω : Ω) :
      T ω < ⊤ ↔ ∃ n : ℕ, T ω < (n : ℝ≥0∞) := by
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_gt ((T ω).toNNReal)
      refine ⟨n, ?_⟩
      have hEq : ((T ω).toNNReal : ℝ≥0∞) = T ω :=
        ENNReal.coe_toNNReal (ne_top_of_lt h)
      rw [← hEq]
      exact_mod_cast hn
    · rintro ⟨n, hn⟩
      exact lt_of_lt_of_le hn le_top
  constructor
  · ext ω
    simpa only [Set.mem_setOf_eq, Set.mem_iUnion] using hFinite ω
  · ext z
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨ht, hc⟩
      obtain ⟨n, hn⟩ := (hFinite z.1).mp ht
      exact ⟨n, hn, hc⟩
    · rintro ⟨n, hn, hc⟩
      exact ⟨(hFinite z.1).mpr ⟨n, hn⟩, hc⟩
