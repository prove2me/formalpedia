-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T17:17:03.849038+00:00
-- url     : https://prove2.me/submissions/56526bd5-57d3-49c4-8d30-333d49beb026

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (n : ℕ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      z.2 ((Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n)) := by
  classical
  let idx : ℝ≥0 × (ℝ≥0 → ℝ) → ℕ :=
    fun z => Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n)
  have hidx : Measurable idx := by
    exact ((measurable_coe_nnreal_real.comp measurable_fst).mul_const
      ((2 : ℝ) ^ n)).nat_ceil
  have hfixed (k : ℕ) :
      Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
        z.2 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)) :=
    (measurable_pi_apply _).comp measurable_snd
  change Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
    z.2 (((idx z : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n))
  intro s hs
  have hpre :
      (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
        z.2 (((idx z : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n)) ⁻¹' s =
      ⋃ k : ℕ,
        {z : ℝ≥0 × (ℝ≥0 → ℝ) | idx z = k} ∩
        {z : ℝ≥0 × (ℝ≥0 → ℝ) |
          z.2 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) ∈ s} := by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨idx z, rfl, hz⟩
    · rintro ⟨k, hk, hz⟩
      change z.2 (((idx z : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ∈ s
      rw [hk]
      exact hz
  rw [hpre]
  have hlevel (k : ℕ) : MeasurableSet {z : ℝ≥0 × (ℝ≥0 → ℝ) | idx z = k} :=
    hidx measurableSet_eq
  exact MeasurableSet.iUnion (fun k =>
    (hlevel k).inter ((hfixed k) hs))
