-- Prove2me | solution 1 for ComplexNorms.norm_add_le_two_mul_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:03:05.492777+00:00
-- url     : https://prove2.me/submissions/ee604bc0-ee74-4664-8382-09e4393e8d61

import Mathlib

set_option maxHeartbeats 2000000

-- ===== Salt.Weil.MultiExtract =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Weil track, node W-DESC-EXT — the multi-root modulus extraction

This is the last lemma-node before the final Weil-bound assembly. It is pure finite complex
analysis, standalone (`import Mathlib` only).

## Main results

* `forall_norm_le_of_powerSum_bound` — the master lemma. If the power sums `∑ i, z i ^ n` of a
  finite family of complex numbers satisfy `‖∑ i, z i ^ n‖ ≤ C ρ^n` for all `n ≥ N₀`, then every
  root obeys `‖z i‖ ≤ ρ`. Proof by a fully finite mean-square / Cesàro argument.
* `norm_eq_sqrt_of_pair_of_le` — the exact-modulus upgrade: from `‖α β‖ = q` and both
  `‖α‖, ‖β‖ ≤ √q` we get `‖α‖ = ‖β‖ = √q`.
* `norm_add_le_two_mul_sqrt` — the convenience corollary `‖α + β‖ ≤ 2√q`.
-/

namespace Salt.Weil

open Finset in
/-- **The master lemma (multi-root modulus extraction).**
If the power sums of a finite family `z : ι → ℂ` satisfy `‖∑ i, z i ^ n‖ ≤ C ρ^n` for every
`n ≥ N₀` (with `ρ > 0`), then every root has modulus `≤ ρ`.

The proof is a fully finite mean-square (Cesàro) argument: assuming some root has modulus
`r > ρ`, normalise the cross terms `w (i,i') = z i · conj (z i') / r²` (so `‖w‖ ≤ 1` and the
diagonal `w (j,j) = 1` at a maximal root `j`), expand `‖∑ z i ^ n‖²` as a double sum of `w`
powers, and sum over `n ∈ [N₀, N)`. The `w = 1` terms contribute `N − N₀`, the geometric
`w ≠ 1` terms are bounded uniformly, while the whole sum is bounded by a geometric constant
`C²/(1 − ρ²/r²)`. Choosing `N` large enough forces a contradiction. -/
theorem forall_norm_le_of_powerSum_bound {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (C ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (hbound : ∀ n : ℕ, N₀ ≤ n → ‖∑ i, z i ^ n‖ ≤ C * ρ ^ n) :
    ∀ i, ‖z i‖ ≤ ρ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  haveI : Nonempty ι := ⟨i₀⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖z i‖
  set r : ℝ := ‖z j‖ with hr_def
  have hρr : ρ < r := lt_of_lt_of_le hi₀ (hj i₀)
  have hr_pos : 0 < r := lt_trans hρ hρr
  have hr2_pos : (0 : ℝ) < r ^ 2 := by positivity
  have hrC_ne : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr_pos
  -- normalized cross terms
  set w : ι × ι → ℂ := fun p => z p.1 * (starRingEnd ℂ) (z p.2) / (r : ℂ) ^ 2 with hw_def
  -- ‖w p‖ ≤ 1
  have hwnorm : ∀ p : ι × ι, ‖w p‖ ≤ 1 := by
    intro p
    have h1 : ‖z p.1‖ ≤ r := hj p.1
    have h2 : ‖z p.2‖ ≤ r := hj p.2
    have hval : ‖w p‖ = ‖z p.1‖ * ‖z p.2‖ / r ^ 2 := by
      simp only [hw_def, norm_div, norm_mul, norm_pow, RCLike.norm_conj,
        Complex.norm_of_nonneg hr_pos.le]
    rw [hval, div_le_one hr2_pos]
    calc ‖z p.1‖ * ‖z p.2‖ ≤ r * r := by
            apply mul_le_mul h1 h2 (norm_nonneg _) (le_of_lt hr_pos)
      _ = r ^ 2 := by ring
  -- diagonal is 1
  have hwjj : w (j, j) = 1 := by
    have hns : Complex.normSq (z j) = r ^ 2 := by
      rw [hr_def]; exact Complex.normSq_eq_norm_sq _
    simp only [hw_def]
    rw [Complex.mul_conj, hns, Complex.ofReal_pow]
    exact div_self (pow_ne_zero 2 hrC_ne)
  -- the crux algebraic identity
  have hcrux : ∀ n : ℕ, ∑ p : ι × ι, w p ^ n
      = ((Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n) : ℝ) : ℂ) := by
    intro n
    have hconj : (∑ i, ((starRingEnd ℂ) (z i)) ^ n) = (starRingEnd ℂ) (∑ i, z i ^ n) := by
      rw [map_sum]; simp only [map_pow]
    calc ∑ p : ι × ι, w p ^ n
        = ∑ p : ι × ι, (z p.1 * (starRingEnd ℂ) (z p.2)) ^ n / ((r : ℂ) ^ 2) ^ n := by
          simp only [hw_def, div_pow]
      _ = (∑ p : ι × ι, (z p.1) ^ n * ((starRingEnd ℂ) (z p.2)) ^ n) / ((r : ℂ) ^ 2) ^ n := by
          rw [← Finset.sum_div]; simp only [mul_pow]
      _ = ((∑ i, z i ^ n) * (starRingEnd ℂ) (∑ i, z i ^ n)) / ((r : ℂ) ^ 2) ^ n := by
          congr 1
          rw [← hconj, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
      _ = (Complex.normSq (∑ i, z i ^ n) : ℂ) / ((r : ℂ) ^ 2) ^ n := by rw [Complex.mul_conj]
      _ = ((Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n) : ℝ) : ℂ) := by
          rw [← pow_mul, ← Complex.ofReal_pow, ← Complex.ofReal_div]
  -- t = (ρ/r)² ∈ [0,1)
  set t : ℝ := ρ ^ 2 / r ^ 2 with ht_def
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t < 1 := by
    rw [ht_def, div_lt_one hr2_pos]
    nlinarith [hρr, hρ, hr_pos]
  have h1t : 0 < 1 - t := by linarith
  -- the per-term upper bound
  have halg : ∀ n : ℕ, C ^ 2 * t ^ n = (C * ρ ^ n) ^ 2 / r ^ (2 * n) := by
    intro n
    rw [ht_def, div_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n 2]
    ring
  have hterm_up : ∀ n : ℕ, N₀ ≤ n →
      Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n) ≤ C ^ 2 * t ^ n := by
    intro n hn
    have hb := hbound n hn
    have hsq : Complex.normSq (∑ i, z i ^ n) = ‖∑ i, z i ^ n‖ ^ 2 :=
      Complex.normSq_eq_norm_sq _
    rw [hsq, halg n]
    gcongr
  -- geometric constant B₁
  have hUpper : ∀ N : ℕ, ∑ n ∈ Finset.Ico N₀ N,
      Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n) ≤ C ^ 2 / (1 - t) := by
    intro N
    calc ∑ n ∈ Finset.Ico N₀ N, Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n)
        ≤ ∑ n ∈ Finset.Ico N₀ N, C ^ 2 * t ^ n := by
          apply Finset.sum_le_sum
          intro n hn
          exact hterm_up n (Finset.mem_Ico.mp hn).1
      _ ≤ ∑ n ∈ Finset.range N, C ^ 2 * t ^ n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
          · intro n _ _; positivity
      _ = C ^ 2 * ∑ n ∈ Finset.range N, t ^ n := by rw [Finset.mul_sum]
      _ ≤ C ^ 2 * (1 / (1 - t)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmul : (1 - t) * (∑ n ∈ Finset.range N, t ^ n) = 1 - t ^ N := by
            linear_combination -geom_sum_mul t N
          have hsum_range : ∑ n ∈ Finset.range N, t ^ n = (1 - t ^ N) / (1 - t) := by
            rw [eq_div_iff (ne_of_gt h1t), mul_comm]; exact hmul
          rw [hsum_range]
          gcongr
          · nlinarith [pow_nonneg ht0 N]
      _ = C ^ 2 / (1 - t) := by rw [mul_one_div]
  -- B₂ : the fixed geometric-tail constant over the off-diagonal (w ≠ 1) pairs
  set B₂ : ℝ := ∑ p ∈ Finset.univ.filter (fun p => ¬ w p = 1), 2 / ‖w p - 1‖ with hB₂
  set m : ℕ := ⌈C ^ 2 / (1 - t) + B₂⌉₊ + 1 with hm
  set N : ℕ := N₀ + m with hN
  have hNN : N₀ ≤ N := by rw [hN]; exact Nat.le_add_right _ _
  -- upper bound on the double-sum real part
  have hG_upper : (∑ n ∈ Finset.Ico N₀ N, ∑ p : ι × ι, w p ^ n).re ≤ C ^ 2 / (1 - t) := by
    have hEq : (∑ n ∈ Finset.Ico N₀ N, ∑ p : ι × ι, w p ^ n)
        = ((∑ n ∈ Finset.Ico N₀ N, Complex.normSq (∑ i, z i ^ n) / r ^ (2 * n) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [hcrux n]
    rw [hEq, Complex.ofReal_re]
    exact hUpper N
  -- the "w = 1" diagonal terms: each equals N - N₀
  have hfirst : ∀ p ∈ Finset.univ.filter (fun p => w p = 1),
      (∑ n ∈ Finset.Ico N₀ N, w p ^ n).re = ((N - N₀ : ℕ) : ℝ) := by
    intro p hp
    have hwp : w p = 1 := (Finset.mem_filter.mp hp).2
    simp only [hwp, one_pow, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one,
      Complex.natCast_re]
  have hfirst_sum : ((N - N₀ : ℕ) : ℝ)
      ≤ ∑ p ∈ Finset.univ.filter (fun p => w p = 1), (∑ n ∈ Finset.Ico N₀ N, w p ^ n).re := by
    rw [Finset.sum_congr rfl hfirst, Finset.sum_const, nsmul_eq_mul]
    have hcard : 1 ≤ (Finset.univ.filter (fun p => w p = 1)).card :=
      Finset.card_pos.mpr ⟨(j, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwjj⟩⟩
    calc ((N - N₀ : ℕ) : ℝ)
        = 1 * ((N - N₀ : ℕ) : ℝ) := (one_mul _).symm
      _ ≤ ((Finset.univ.filter (fun p => w p = 1)).card : ℝ) * ((N - N₀ : ℕ) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast hcard
  -- the "w ≠ 1" off-diagonal terms: each ≥ -(2 / ‖w p - 1‖)
  have hsecond : ∀ p ∈ Finset.univ.filter (fun p => ¬ w p = 1),
      -(2 / ‖w p - 1‖) ≤ (∑ n ∈ Finset.Ico N₀ N, w p ^ n).re := by
    intro p hp
    have hwp : w p ≠ 1 := (Finset.mem_filter.mp hp).2
    have hBpos : 0 < ‖w p - 1‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hwp
    have hAle : ‖w p ^ N - w p ^ N₀‖ ≤ 2 := by
      calc ‖w p ^ N - w p ^ N₀‖ ≤ ‖w p ^ N‖ + ‖w p ^ N₀‖ := norm_sub_le _ _
        _ = ‖w p‖ ^ N + ‖w p‖ ^ N₀ := by rw [norm_pow, norm_pow]
        _ ≤ 1 + 1 := by
            gcongr <;> exact pow_le_one₀ (norm_nonneg _) (hwnorm p)
        _ = 2 := by norm_num
    have hnorm : ‖(w p ^ N - w p ^ N₀) / (w p - 1)‖ ≤ 2 / ‖w p - 1‖ := by
      rw [le_div_iff₀ hBpos, norm_div, div_mul_cancel₀ _ (ne_of_gt hBpos)]
      exact hAle
    have hre : -‖(w p ^ N - w p ^ N₀) / (w p - 1)‖
        ≤ ((w p ^ N - w p ^ N₀) / (w p - 1)).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    rw [geom_sum_Ico hwp hNN]
    linarith [hre, hnorm]
  have hsecond_sum : -B₂
      ≤ ∑ p ∈ Finset.univ.filter (fun p => ¬ w p = 1), (∑ n ∈ Finset.Ico N₀ N, w p ^ n).re := by
    rw [hB₂]
    have h := Finset.sum_le_sum hsecond
    rwa [Finset.sum_neg_distrib] at h
  -- lower bound on the double-sum real part
  have hlow : ((N - N₀ : ℕ) : ℝ) - B₂
      ≤ (∑ n ∈ Finset.Ico N₀ N, ∑ p : ι × ι, w p ^ n).re := by
    rw [Finset.sum_comm, Complex.re_sum,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p => w p = 1)]
    linarith [hfirst_sum, hsecond_sum]
  -- combine and refute
  have hmain : ((N - N₀ : ℕ) : ℝ) ≤ C ^ 2 / (1 - t) + B₂ := by
    linarith [hG_upper, hlow]
  have hNsub : N - N₀ = m := by omega
  rw [hNsub, hm] at hmain
  push_cast at hmain
  have hceil := Nat.le_ceil (C ^ 2 / (1 - t) + B₂)
  linarith [hceil, hmain]

/-- **The exact-modulus pair lemma.** From `‖α β‖ = q` and both `‖α‖, ‖β‖ ≤ √q` we conclude
`‖α‖ = ‖β‖ = √q`. -/
theorem norm_eq_sqrt_of_pair_of_le (α β : ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hprod : ‖α * β‖ = q) (hα : ‖α‖ ≤ Real.sqrt q) (hβ : ‖β‖ ≤ Real.sqrt q) :
    ‖α‖ = Real.sqrt q ∧ ‖β‖ = Real.sqrt q := by
  have hab : ‖α‖ * ‖β‖ = q := by rw [← norm_mul, hprod]
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  rcases eq_or_lt_of_le hq with hq0 | hq0
  · -- q = 0
    have hsqrt0 : Real.sqrt q = 0 := by rw [← hq0, Real.sqrt_zero]
    rw [hsqrt0] at hα hβ ⊢
    exact ⟨le_antisymm hα (norm_nonneg _), le_antisymm hβ (norm_nonneg _)⟩
  · -- 0 < q
    have hspos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
    have keyα : Real.sqrt q ≤ ‖α‖ := by
      nlinarith [norm_nonneg α, norm_nonneg β, Real.sqrt_nonneg q, hα, hβ, hab, hs, hspos]
    have keyβ : Real.sqrt q ≤ ‖β‖ := by
      nlinarith [norm_nonneg α, norm_nonneg β, Real.sqrt_nonneg q, hα, hβ, hab, hs, hspos]
    exact ⟨le_antisymm hα keyα, le_antisymm hβ keyβ⟩

/-- Convenience corollary for the descent: `‖α + β‖ ≤ 2√q` from `‖α‖, ‖β‖ ≤ √q`. -/
theorem norm_add_le_two_mul_sqrt (α β : ℂ) (q : ℝ)
    (hα : ‖α‖ ≤ Real.sqrt q) (hβ : ‖β‖ ≤ Real.sqrt q) :
    ‖α + β‖ ≤ 2 * Real.sqrt q := by
  calc ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
    _ ≤ Real.sqrt q + Real.sqrt q := by gcongr
    _ = 2 * Real.sqrt q := by ring

end Salt.Weil

end




section


theorem solution (α β : ℂ) (q : ℝ)
    (hα : ‖α‖ ≤ Real.sqrt q) (hβ : ‖β‖ ≤ Real.sqrt q) :
    ‖α + β‖ ≤ 2 * Real.sqrt q := by
  apply Salt.Weil.norm_add_le_two_mul_sqrt <;> assumption

end

