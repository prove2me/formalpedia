-- Prove2me | solution 1 for GRH.exponential_smoothing_of_partialSums_isBigO_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T00:04:25.617045+00:00
-- url     : https://prove2.me/submissions/fa4e4aea-f0f1-4af2-be4b-41b55308c4d0

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

open Filter Asymptotics
open scoped BigOperators Topology

private theorem affine_geometric_smoothing (a : ℕ → ℂ) (C ε r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n : ℕ, ‖∑ k ∈ Finset.range (n + 1), a k‖ ≤ C + ε * n) :
    ‖∑' n : ℕ, a n * (r : ℂ) ^ n‖ ≤ C + ε * (r / (1 - r)) := by
  let A (n : ℕ) := ∑ k ∈ Finset.range n, a k
  let b (n : ℕ) := A (n + 1) * (r : ℂ) ^ n
  let d (n : ℕ) := A n * (r : ℂ) ^ n
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have major : HasSum (fun n : ℕ => (C + ε * n) * r ^ n)
      (C * (1 - r)⁻¹ + ε * (r / (1-r)^2)) := by
    apply (((hasSum_geometric_of_lt_one hr0 hr1).mul_left C).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).mul_left ε)).congr_fun
    intro n
    ring
  have bound (n : ℕ) : ‖b n‖ ≤ (C + ε * n) * r ^ n := by
    dsimp only [b]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_right (h n) (pow_nonneg hr0 _)
  have hbn := major.summable.of_nonneg_of_le (fun n => norm_nonneg (b n)) bound
  have hb := hbn.of_norm
  have hd' : HasSum (fun n : ℕ => d (n + 1)) ((∑' n : ℕ, b n) * (r : ℂ)) := by
    simpa [b,d, pow_succ, mul_assoc] using hb.hasSum.mul_right (r : ℂ)
  have hd : HasSum d ((∑' n : ℕ, b n) * (r : ℂ)) := by
    have := (hasSum_nat_add_iff (f := d) 1).mp hd'
    simpa [d,A] using this
  have ha : HasSum (fun n : ℕ => a n * (r : ℂ) ^ n)
      ((∑' n : ℕ, b n) - (∑' n : ℕ, b n) * (r : ℂ)) := by
    apply (hb.hasSum.sub hd).congr_fun
    intro n
    simp [b,d,A,Finset.sum_range_succ,add_mul]
  have he : ‖∑' n : ℕ, a n * (r : ℂ) ^ n‖ =
      ‖∑' n : ℕ, b n‖ * (1-r) := by
    rw [ha.tsum_eq, ← mul_one_sub, norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hr1)]
  rw [he]
  calc
    _ ≤ (C * (1-r)⁻¹ + ε * (r / (1-r)^2)) * (1-r) := by
      apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hr1.le)
      exact (norm_tsum_le_tsum_norm hbn).trans
        ((hbn.tsum_le_tsum bound major.summable).trans_eq major.tsum_eq)
    _ = _ := by field_simp [(sub_pos.mpr hr1).ne']

private theorem affine_exp_smoothing (a : ℕ → ℂ) (B L D : ℝ)
    (hDpos : 0 < D) (hL : 0 ≤ L)
    (affine : ∀ n : ℕ, ‖∑ k ∈ Finset.range (n+1), a k‖ ≤ B + L * n) :
    ‖∑' n : ℕ, a n * (Real.exp (-(n : ℝ) * D⁻¹) : ℂ)‖ ≤ B + L * D := by
  let r := Real.exp (-D⁻¹)
  have hro : 0 < r := Real.exp_pos _
  have hr : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (inv_pos.mpr hDpos))
  have small : r / (1-r) ≤ D := by
    have prod : r * (D⁻¹ + 1) ≤ 1 := calc
      _ ≤ r * Real.exp D⁻¹ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hro.le
      _ = 1 := by dsimp [r]; rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne']
    apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
    have prod' := mul_le_mul_of_nonneg_right prod hDpos.le
    rw [add_comm D⁻¹ 1, mul_add, add_mul, one_mul, mul_one, mul_assoc, inv_mul_cancel₀ hDpos.ne', mul_one] at prod'
    linarith
  have smooth (n : ℕ) : (Real.exp (-(n : ℝ) * D⁻¹) : ℂ) = (r : ℂ)^n := by
    rw [← Complex.ofReal_pow]
    congr 1
    simpa [r, neg_mul, mul_neg] using Real.exp_nat_mul (-D⁻¹) n
  simp only [smooth]
  exact (affine_geometric_smoothing a B L r hro.le hr affine).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left small hL) _)

theorem solution (a : ℕ → ℂ) (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h : (fun n : ℕ => ∑ k ∈ Finset.range (n+1), a k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ)) :
    (fun D : ℝ => ∑' n : ℕ, a n * (Real.exp (-(n : ℝ) * D⁻¹) : ℂ))
      =O[atTop] (fun D : ℝ => D ^ σ) := by
  obtain ⟨K,hK,hbound⟩ := h.exists_nonneg
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound.bound
  let A (n : ℕ) := ∑ k ∈ Finset.range (n+1), a k
  let B := ∑ n ∈ Finset.range N, ‖A n‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  apply IsBigO.of_bound (B + 2*K)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with D hD
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hDσ : 1 ≤ D^σ := Real.one_le_rpow hD hσ0
  have hL : 0 ≤ K * D^(σ-1) := mul_nonneg hK (Real.rpow_nonneg hDpos.le _)
  have scale : D^(σ-1)*D = D^σ := by
    rw [Real.rpow_sub_one hDpos.ne', div_mul_cancel₀ _ hDpos.ne']
  have affine (n : ℕ) : ‖A n‖ ≤ B + K * D^σ + (K * D^(σ-1)) * n := by
    rcases le_or_gt N n with hn | hn
    · have hn' := hN n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] at hn'
      change ‖A n‖ ≤ K * (n:ℝ)^σ at hn'
      rcases le_or_gt (n:ℝ) D with hnD | hnD
      · have small := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Nat.cast_nonneg n) hnD hσ0) hK
        linarith only [hB, mul_nonneg hL (Nat.cast_nonneg n), hn', small]
      · have hnpos := hDpos.trans hnD
        have negpow := Real.rpow_le_rpow_of_nonpos hDpos hnD.le (sub_nonpos.mpr hσ1)
        rw [Real.rpow_sub_one hnpos.ne'] at negpow
        have large := mul_le_mul_of_nonneg_left ((div_le_iff₀ hnpos).mp negpow) hK
        rw [← mul_assoc] at large
        linarith only [hB, mul_nonneg hK (by positivity : 0 ≤ D^σ), hn', large]
    · have hprefix : ‖A n‖ ≤ B := Finset.single_le_sum (fun i _ => norm_nonneg (A i))
          (Finset.mem_range.mpr hn)
      linarith only [hprefix, mul_nonneg hK (by positivity : 0 ≤ D^σ),
        mul_nonneg hL (Nat.cast_nonneg n)]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hDpos _)]
  calc
    _ ≤ B + K * D^σ + (K * D^(σ-1)) * D :=
      affine_exp_smoothing a _ _ _ hDpos hL affine
    _ ≤ (B + 2*K) * D^σ := by
      rw [mul_assoc, scale]
      nlinarith only [mul_le_mul_of_nonneg_left hDσ hB]
