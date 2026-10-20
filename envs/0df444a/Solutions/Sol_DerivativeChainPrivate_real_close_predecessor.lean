-- Prove2me | solution 1 for DerivativeChainPrivate.real_close_predecessor
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-17T03:08:51.138168+00:00
-- url     : https://prove2.me/submissions/25c46e3c-b012-4eee-bfde-daf924bac387

-- D2 proof: real disk lemma. No sorry. Self-contained (D1 identity inlined
-- so this file checks standalone; DAG-wise D2 reuses D1).
import Mathlib

open scoped BigOperators

set_option autoImplicit false

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (p a : ι → ℝ) (b : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hsum : ∑ i ∈ s, p i = 1)
    (hb : b = ∑ i ∈ s, p i * a i)
    (hmem : ∀ i ∈ s, |a i| ≤ 1) :
    ∃ i ∈ s, (a i - b) ^ 2 ≤ 1 - b ^ 2 := by
  -- Step 1 (D1): energy identity.
  have hexpand : ∀ i : ι, p i * (a i - b) ^ 2
      = p i * (a i) ^ 2 - 2 * b * (p i * a i) + b ^ 2 * p i := by
    intro i
    ring
  have hsum_eq : ∑ i ∈ s, p i * (a i - b) ^ 2
      = ∑ i ∈ s, (p i * (a i) ^ 2 - 2 * b * (p i * a i) + b ^ 2 * p i) :=
    Finset.sum_congr rfl (fun i _ => hexpand i)
  have hmid : ∑ i ∈ s, (2 * b * (p i * a i)) = 2 * b * ∑ i ∈ s, p i * a i := by
    rw [Finset.mul_sum]
  have hlast : ∑ i ∈ s, (b ^ 2 * p i) = b ^ 2 * ∑ i ∈ s, p i := by
    rw [Finset.mul_sum]
  have henergy : ∑ i ∈ s, p i * (a i - b) ^ 2
      = ∑ i ∈ s, p i * (a i) ^ 2 - b ^ 2 := by
    rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      hmid, hlast, ← hb, hsum]
    ring
  -- Step 2: second moment ≤ 1 from |aᵢ| ≤ 1 and weights.
  have hsq : ∀ i ∈ s, (a i) ^ 2 ≤ 1 := by
    intro i hi
    exact (sq_le_one_iff_abs_le_one _).mpr (hmem i hi)
  have hterm : ∀ i ∈ s, p i * (a i) ^ 2 ≤ p i * 1 := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (hsq i hi) (hp i hi)
  have hsecond : ∑ i ∈ s, p i * (a i) ^ 2 ≤ 1 := by
    calc ∑ i ∈ s, p i * (a i) ^ 2 ≤ ∑ i ∈ s, p i * 1 :=
          Finset.sum_le_sum hterm
      _ = ∑ i ∈ s, p i := by simp
      _ = 1 := hsum
  have havg : ∑ i ∈ s, p i * (a i - b) ^ 2 ≤ 1 - b ^ 2 := by
    rw [henergy]
    linarith
  -- Step 3: minimizer of (aᵢ−b)² attains at most the weighted average.
  obtain ⟨i₀, hi₀mem, hi₀min⟩ :=
    Finset.exists_min_image s (fun i => (a i - b) ^ 2) hs
  have hmin_le : ∀ i ∈ s, (a i₀ - b) ^ 2 ≤ (a i - b) ^ 2 := by
    intro i hi
    exact hi₀min i hi
  have hsingle : (a i₀ - b) ^ 2 ≤ ∑ i ∈ s, p i * (a i - b) ^ 2 := by
    have hbase : (a i₀ - b) ^ 2 = ∑ i ∈ s, p i * (a i₀ - b) ^ 2 := by
      conv_lhs => rw [← one_mul ((a i₀ - b) ^ 2), ← hsum, Finset.sum_mul]
    rw [hbase]
    exact Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hmin_le i hi) (hp i hi))
  exact ⟨i₀, hi₀mem, le_trans hsingle havg⟩
