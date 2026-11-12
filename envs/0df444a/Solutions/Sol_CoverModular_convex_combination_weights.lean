-- Prove2me | solution 1 for CoverModular.convex_combination_weights
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T22:15:18.731368+00:00
-- url     : https://prove2.me/submissions/b2cdea20-8eab-466b-8139-0d33da67ca19

import Mathlib

theorem solution (K : ℕ) (hK : 1 ≤ K) :
    let δ : ℝ := 2 / (1 - (1 - 2 / (K : ℝ)) ^ K)
    let π : ℕ → ℝ := fun t => δ / K * (1 - 2 / (K : ℝ)) ^ (K - t)
    (∀ t ∈ Finset.Icc 1 K, 0 ≤ π t) ∧
    ∑ t ∈ Finset.Icc 1 K, π t = 1 ∧
    (∀ ρ : ℕ → ℝ,
      ∑ t ∈ Finset.Icc 1 K, π t * (2 * ∑ τ ∈ Finset.Icc 1 (t - 1), ρ τ + K * ρ t) =
        ∑ t ∈ Finset.Icc 1 K, ρ t * (K * π t + ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ)) ∧
    ∀ t ∈ Finset.Icc 1 K,
      K * π t + ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ =
          δ * (1 - 2 / (K : ℝ)) ^ (K - t) +
            2 * δ / K * ∑ τ ∈ Finset.range (K - t), (1 - 2 / (K : ℝ)) ^ τ ∧
        δ * (1 - 2 / (K : ℝ)) ^ (K - t) +
            2 * δ / K * ∑ τ ∈ Finset.range (K - t), (1 - 2 / (K : ℝ)) ^ τ = δ := by
  intro δ π
  have hδdef : δ = 2 / (1 - (1 - 2 / (K : ℝ)) ^ K) := rfl
  have hπ : ∀ t, π t = δ / K * (1 - 2 / (K : ℝ)) ^ (K - t) := fun t => rfl
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 - 2 / (K : ℝ) := ⟨_, rfl⟩
  rw [← hq] at hδdef hπ ⊢
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hKne : (K:ℝ) ≠ 0 := hKpos.ne'
  have h1q : 1 - q = 2 / K := by rw [hq]; ring
  have hqK : 0 < 1 - q ^ K := by
    by_cases hK1 : K = 1
    · subst hK1
      rw [hq]; norm_num
    · have h2 : (2:ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      have hq0 : 0 ≤ q := by
        rw [hq]
        have : 2 / (K:ℝ) ≤ 1 := (div_le_one hKpos).2 h2
        linarith
      have hq1 : q < 1 := by
        rw [hq]
        have : 0 < 2 / (K:ℝ) := by positivity
        linarith
      have := pow_lt_one₀ hq0 hq1 (show K ≠ 0 by omega)
      linarith
  have hδK : δ * (1 - q ^ K) = 2 := by rw [hδdef]; exact div_mul_cancel₀ 2 hqK.ne'
  have hδ0 : 0 ≤ δ := by rw [hδdef]; exact div_nonneg (by norm_num) hqK.le
  have hgeom : ∀ m : ℕ, (∑ s ∈ Finset.range m, q ^ s) * (2 / K) = 1 - q ^ m := by
    intro m
    rw [← h1q]
    have := geom_sum_mul q m
    linarith
  have reidx : ∀ a : ℕ, ∑ τ ∈ Finset.Icc (a + 1) K, q ^ (K - τ) =
      ∑ s ∈ Finset.range (K - a), q ^ s := by
    intro a
    apply Finset.sum_bij' (fun τ _ => K - τ) (fun s _ => K - s)
    · intro τ h
      simp only [Finset.mem_Icc] at h
      simp only [Finset.mem_range]
      omega
    · intro s h
      simp only [Finset.mem_range] at h
      simp only [Finset.mem_Icc]
      omega
    · intro τ h
      simp only [Finset.mem_Icc] at h
      omega
    · intro s h
      simp only [Finset.mem_range] at h
      omega
    · intro τ _
      rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hπ]
    simp only [Finset.mem_Icc] at ht
    apply mul_nonneg (div_nonneg hδ0 hKpos.le)
    by_cases hK1 : K = 1
    · have : K - t = 0 := by omega
      rw [this, pow_zero]
      exact zero_le_one
    · have h2 : (2:ℝ) ≤ K := by exact_mod_cast (show 2 ≤ K by omega)
      have hq0 : 0 ≤ q := by
        rw [hq]
        have : 2 / (K:ℝ) ≤ 1 := (div_le_one hKpos).2 h2
        linarith
      exact pow_nonneg hq0 _
  · have e : ∑ t ∈ Finset.Icc 1 K, π t = δ / K * ∑ s ∈ Finset.range K, q ^ s := by
      have h0 := reidx 0
      simp only [zero_add, Nat.sub_zero] at h0
      rw [← h0, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => hπ t)
    rw [e]
    have : δ / K * ∑ s ∈ Finset.range K, q ^ s =
        δ / 2 * ((∑ s ∈ Finset.range K, q ^ s) * (2 / K)) := by
      ring
    rw [this, hgeom K]
    linarith
  · intro ρ
    have hswap : ∑ t ∈ Finset.Icc 1 K, ∑ τ ∈ Finset.Icc 1 (t - 1), π t * ρ τ =
        ∑ τ ∈ Finset.Icc 1 K, ∑ t ∈ Finset.Icc (τ + 1) K, π t * ρ τ :=
      Finset.sum_comm' (fun t τ => by simp only [Finset.mem_Icc]; omega)
    have hL : ∑ t ∈ Finset.Icc 1 K, π t * (2 * ∑ τ ∈ Finset.Icc 1 (t - 1), ρ τ + K * ρ t) =
        2 * (∑ t ∈ Finset.Icc 1 K, ∑ τ ∈ Finset.Icc 1 (t - 1), π t * ρ τ) +
          ∑ t ∈ Finset.Icc 1 K, (K:ℝ) * π t * ρ t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum]
      ring
    have hR : ∑ t ∈ Finset.Icc 1 K, ρ t * (K * π t + ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ) =
        2 * (∑ t ∈ Finset.Icc 1 K, ∑ τ ∈ Finset.Icc (t + 1) K, π τ * ρ t) +
          ∑ t ∈ Finset.Icc 1 K, (K:ℝ) * π t * ρ t := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      ring
    rw [hL, hR, hswap]
  · intro t ht
    have hs : ∑ τ ∈ Finset.Icc (t + 1) K, 2 * π τ =
        2 * δ / K * ∑ s ∈ Finset.range (K - t), q ^ s := by
      rw [← reidx t, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro τ _
      rw [hπ]
      ring
    have hKt : (K:ℝ) * π t = δ * q ^ (K - t) := by
      rw [hπ, ← mul_assoc, mul_div_cancel₀ δ hKne]
    refine ⟨by rw [hs, hKt], ?_⟩
    have : 2 * δ / K * ∑ s ∈ Finset.range (K - t), q ^ s =
        δ * ((∑ s ∈ Finset.range (K - t), q ^ s) * (2 / K)) := by ring
    rw [this, hgeom]
    ring
