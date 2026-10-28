-- Prove2me | solution 1 for AvramDividend.Classical.bounded_stopping_dyadic_grid_approximation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:37:13.399988+00:00
-- url     : https://prove2.me/submissions/db70724b-3ee2-481a-a6a2-00120f099055

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology
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
open scoped ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) := by
  let c : ℕ → Ω → ℕ := fun n ω => Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n)
  refine ⟨fun n ω => (c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n,
    fun n => (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n) + 1)).image
      (fun k : ℕ => (k : ℝ≥0) / (2 : ℝ≥0) ^ n), ?_, ?_, ?_, ?_⟩
  · intro n ω
    refine Finset.mem_image.2 ⟨c n ω, Finset.mem_range.2 (Nat.lt_succ_of_le ?_), rfl⟩
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hbound ω) (by positivity))
  · intro n s hs
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hs
    have hinj : ∀ a b : ℕ, (a : ℝ≥0) / (2 : ℝ≥0) ^ n = (b : ℝ≥0) / (2 : ℝ≥0) ^ n → a = b := by
      intro a b h
      have h2 : (2 : ℝ≥0) ^ n ≠ 0 := by positivity
      rw [div_left_inj' h2] at h; exact_mod_cast h
    have : {ω : Ω | (c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n = (k : ℝ≥0) / (2 : ℝ≥0) ^ n} =
        {ω : Ω | Nat.ceil ((τ ω : ℝ) * (2 : ℝ) ^ n) = k} := by
      ext ω; simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => hinj _ _ h, fun h => by simp only [c, h]⟩
    rw [this]; exact S107Dy.fibre 𝓕 τ hstop n k
  · intro ω n
    have := Nat.le_ceil ((τ ω : ℝ) * (2 : ℝ) ^ n)
    exact (S107Dy.le_iff (τ ω) n (c n ω)).1 this
  · intro ω
    rw [← NNReal.tendsto_coe]
    have hup : ∀ n, (((c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) ≤ τ ω + (1 / 2 : ℝ) ^ n := by
      intro n
      have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (τ ω : ℝ) * (2 : ℝ) ^ n by positivity)
      rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, div_le_iff₀ (by positivity)]
      have : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
      push_cast
      nlinarith
    have hlo : ∀ n, (τ ω : ℝ) ≤ (((c n ω : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      intro n
      exact_mod_cast (S107Dy.le_iff (τ ω) n (c n ω)).1 (Nat.le_ceil _)
    have hlim : Tendsto (fun n : ℕ => (τ ω : ℝ) + (1 / 2 : ℝ) ^ n) atTop (𝓝 (τ ω)) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_add (τ ω : ℝ)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim hlo hup
