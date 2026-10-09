-- Prove2me | solution 1 for GaussianMatrix.tw_gamma_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T08:30:47.755417+00:00
-- url     : https://prove2.me/submissions/a8610e14-bcae-4b60-91f5-f49c7525bbc0

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- Squared Gautschi/Wendel inequality `Γ(z + 1/2)² ≤ z Γ(z)²`, from log-convexity of `Γ`. -/
lemma gamma_add_half_sq_le {z : ℝ} (hz : 0 < z) :
    Real.Gamma (z + 1 / 2) ^ 2 ≤ z * Real.Gamma z ^ 2 := by
  have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := z) (t := z + 1)
    (a := 1 / 2) (b := 1 / 2) hz (by linarith) (by norm_num) (by norm_num) (by norm_num)
  have he : (1 / 2 : ℝ) * z + 1 / 2 * (z + 1) = z + 1 / 2 := by ring
  rw [he] at h
  have hg := Real.Gamma_pos_of_pos hz
  have hg1 := Real.Gamma_pos_of_pos (show 0 < z + 1 by linarith)
  have h0 : 0 ≤ Real.Gamma (z + 1 / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  calc Real.Gamma (z + 1 / 2) ^ 2
      ≤ (Real.Gamma z ^ (1 / 2 : ℝ) * Real.Gamma (z + 1) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = Real.Gamma z * Real.Gamma (z + 1) := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hg.le,
          Real.sq_sqrt hg1.le]
    _ = z * Real.Gamma z ^ 2 := by rw [Real.Gamma_add_one hz.ne']; ring

/-- Iterated Gautschi: `Γ((r+n)/2)² ≤ Γ(r/2)² ∏_{i<n} (r+i)/2`. -/
lemma gamma_half_sq_le_prod {r : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    Real.Gamma (((r : ℝ) + n) / 2) ^ 2
      ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * ∏ i ∈ Finset.range n, (((r : ℝ) + i) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
    have hz : (0 : ℝ) < ((r : ℝ) + n) / 2 := by positivity
    have hg := gamma_add_half_sq_le hz
    have he : ((r : ℝ) + n) / 2 + 1 / 2 = ((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2 := by
      push_cast; ring
    rw [he] at hg
    rw [Finset.prod_range_succ]
    calc Real.Gamma (((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2) ^ 2
        ≤ ((r : ℝ) + n) / 2 * Real.Gamma (((r : ℝ) + n) / 2) ^ 2 := hg
      _ ≤ ((r : ℝ) + n) / 2 * (Real.Gamma ((r : ℝ) / 2) ^ 2
            * ∏ i ∈ Finset.range n, (((r : ℝ) + i) / 2)) :=
          mul_le_mul_of_nonneg_left ih hz.le
      _ = _ := by ring

/-- AM–GM by pairing: `∏_{i=0}^{n} (r+i) ≤ ((2r+n)/2)^(n+1)`. -/
lemma prod_range_add_le (r : ℝ) (hr : 0 ≤ r) (n : ℕ) :
    ∏ i ∈ Finset.range (n + 1), (r + i) ≤ ((2 * r + n) / 2) ^ (n + 1) := by
  set M := (2 * r + n) / 2 with hM
  have hpos : ∀ i ∈ Finset.range (n + 1), 0 ≤ r + (i : ℝ) := fun i _ => by positivity
  have hP : 0 ≤ ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := Finset.prod_nonneg hpos
  have hMpos : 0 ≤ M := by rw [hM]; positivity
  have hrefl : ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ))
      = ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)) := by
    have := Finset.prod_range_reflect (fun i : ℕ => r + (i : ℝ)) (n + 1)
    simpa using this
  have hsq : (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) ^ 2 ≤ (M ^ (n + 1)) ^ 2 := by
    rw [sq]
    calc (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))) * ∏ i ∈ Finset.range (n + 1), (r + (i : ℝ))
        = (∏ i ∈ Finset.range (n + 1), (r + (i : ℝ)))
            * ∏ i ∈ Finset.range (n + 1), (r + ((n - i : ℕ) : ℝ)) := by rw [hrefl]
      _ = ∏ i ∈ Finset.range (n + 1), ((r + (i : ℝ)) * (r + ((n - i : ℕ) : ℝ))) :=
          (Finset.prod_mul_distrib).symm
      _ ≤ ∏ _i ∈ Finset.range (n + 1), M ^ 2 := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i hi
            have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
            rw [Nat.cast_sub hin, hM]
            nlinarith [sq_nonneg ((i : ℝ) - ((n : ℝ) - i))]
      _ = (M ^ (n + 1)) ^ 2 := by rw [Finset.prod_const, Finset.card_range, ← pow_mul,
            ← pow_mul, mul_comm]
  exact (pow_le_pow_iff_left₀ hP (pow_nonneg hMpos _) two_ne_zero).1 hsq

end GaussianMatrix

open GaussianMatrix

theorem solution {r k : ℕ} (hr : 1 ≤ r) (hrk : r ≤ k) :
    2 ^ (((k : ℝ) - r - 1) / 2) * Real.Gamma (((k : ℝ) + 1) / 2)
        / (Real.Gamma ((r : ℝ) / 2) * Real.Gamma ((k : ℝ) - r + 1))
      ≤ (((k : ℝ) + r) / 2) ^ (((k : ℝ) - r + 1) / 2) / (2 * Real.Gamma ((k : ℝ) - r + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hrk
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  push_cast
  have e1 : ((r : ℝ) + n) - r - 1 = (n : ℝ) - 1 := by ring
  have e2 : ((r : ℝ) + n) - r + 1 = (n : ℝ) + 1 := by ring
  rw [e1, e2]
  set M : ℝ := ((r : ℝ) + n + r) / 2 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  have gR := Real.Gamma_pos_of_pos (show (0 : ℝ) < r / 2 by positivity)
  have gK := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((r : ℝ) + n + 1) / 2 by positivity)
  have gN := Real.Gamma_pos_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by positivity)
  -- squared key inequality: 2^(n+1) Γ((k+1)/2)² ≤ Γ(r/2)² M^(n+1)
  have key : 2 ^ (n + 1) * Real.Gamma (((r : ℝ) + n + 1) / 2) ^ 2
      ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * M ^ (n + 1) := by
    have h1 := gamma_half_sq_le_prod hr (n + 1)
    have h2 := prod_range_add_le (r : ℝ) hrpos.le n
    have hc : ((r : ℝ) + ((n + 1 : ℕ) : ℝ)) / 2 = ((r : ℝ) + n + 1) / 2 := by push_cast; ring
    rw [hc] at h1
    have hprod : ∏ i ∈ Finset.range (n + 1), (((r : ℝ) + i) / 2)
        = (∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i)) / 2 ^ (n + 1) := by
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range]
    rw [hprod] at h1
    have hM' : (2 * (r : ℝ) + n) / 2 = M := by rw [hM]; ring
    rw [hM'] at h2
    have h2pos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    calc 2 ^ (n + 1) * Real.Gamma (((r : ℝ) + n + 1) / 2) ^ 2
        ≤ 2 ^ (n + 1) * (Real.Gamma ((r : ℝ) / 2) ^ 2
            * ((∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i)) / 2 ^ (n + 1))) :=
          mul_le_mul_of_nonneg_left h1 h2pos.le
      _ = Real.Gamma ((r : ℝ) / 2) ^ 2 * ∏ i ∈ Finset.range (n + 1), ((r : ℝ) + i) := by
          field_simp
      _ ≤ Real.Gamma ((r : ℝ) / 2) ^ 2 * M ^ (n + 1) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  -- take square roots: 2^((n+1)/2) Γ((k+1)/2) ≤ Γ(r/2) M^((n+1)/2)
  have hsqrt : (2 : ℝ) ^ (((n : ℝ) + 1) / 2) * Real.Gamma (((r : ℝ) + n + 1) / 2)
      ≤ Real.Gamma ((r : ℝ) / 2) * M ^ (((n : ℝ) + 1) / 2) := by
    have hx : ∀ x : ℝ, 0 ≤ x → x ^ (((n : ℝ) + 1) / 2) = Real.sqrt (x ^ (n + 1)) := by
      intro x hx
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
      congr 1; push_cast; ring
    rw [hx 2 (by norm_num), hx M hMpos.le]
    have := Real.sqrt_le_sqrt key
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq gK.le,
      Real.sqrt_mul (by positivity), Real.sqrt_sq gR.le] at this
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2split : (2 : ℝ) ^ (((n : ℝ) + 1) / 2) = 2 ^ (((n : ℝ) - 1) / 2) * 2 := by
    rw [show ((n : ℝ) + 1) / 2 = ((n : ℝ) - 1) / 2 + 1 by ring, Real.rpow_add (by norm_num),
      Real.rpow_one]
  rw [h2split] at hsqrt
  have hgN := gN.le
  nlinarith [mul_le_mul_of_nonneg_right hsqrt hgN]
