-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_index_fibre_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:37:05.553684+00:00
-- url     : https://prove2.me/submissions/3acbed9e-6dd3-4e4a-b1ef-1ad3c409ab20

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace S107Dy

lemma le_iff (t : ℝ≥0) (n m : ℕ) :
    (t : ℝ) * (2 : ℝ) ^ n ≤ m ↔ t ≤ (m : ℝ≥0) / (2 : ℝ≥0) ^ n := by
  rw [← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
    le_div_iff₀ (by positivity)]
  norm_num

lemma fibre {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by
  have hle : ∀ m : ℕ, MeasurableSet[𝓕 ((m : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ m} := by
    intro m
    have h := hstop ((m : ℝ≥0) / (2 : ℝ≥0) ^ n)
    convert h using 1
    ext ω
    simp only [Set.mem_ofPred_eq, WithTop.coe_le_coe, le_iff]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · convert hle 0 using 1
    ext ω; simp only [Set.mem_ofPred_eq, Nat.ceil_eq_zero, Nat.cast_zero]
  · have hmono : (((k - 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n) ≤ (k : ℝ≥0) / (2 : ℝ≥0) ^ n := by
      gcongr; exact_mod_cast Nat.sub_le k 1
    have h1 := 𝓕.mono hmono _ (hle (k - 1))
    have : {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} =
        {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ k} \ {ω | (τ ω : ℝ) * (2 : ℝ) ^ n ≤ ((k - 1 : ℕ) : ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_diff, Nat.ceil_eq_iff hk.ne', not_le]
      tauto
    rw [this]
    exact (hle k).diff h1

end S107Dy
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hstop : MeasureTheory.IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (n k : ℕ) :
    MeasurableSet[𝓕 ((k : ℝ≥0) / (2 : ℝ≥0) ^ n)]
      {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} :=
  S107Dy.fibre 𝓕 τ hstop n k
