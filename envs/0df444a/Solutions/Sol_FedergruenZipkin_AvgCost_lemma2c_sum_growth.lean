-- Prove2me | solution 1 for FedergruenZipkin.AvgCost.lemma2c_sum_growth
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:39:53.753572+00:00
-- url     : https://prove2.me/submissions/3cdc2396-ea63-4f09-b703-4611151902e8

import Mathlib

set_option autoImplicit false

namespace D39cda3a

open Real Finset MeasureTheory

lemma rpow_mul_exp_neg_le (c y : ℝ) (hc : 0 ≤ c) (hy : 0 ≤ y) :
    y ^ c * Real.exp (-y) ≤ 1 + ((Nat.ceil c).factorial : ℝ) := by
  set N := Nat.ceil c
  have hfac : (0:ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h1 : y ^ c ≤ 1 + y ^ N := by
    rcases le_or_gt y 1 with h | h
    · have : y ^ c ≤ 1 := Real.rpow_le_one hy h hc
      have : 0 ≤ y ^ N := pow_nonneg hy N
      linarith
    · have : y ^ c ≤ y ^ (N:ℝ) := Real.rpow_le_rpow_of_exponent_le h.le (Nat.le_ceil c)
      rw [Real.rpow_natCast] at this
      linarith
  have h2 : y ^ N ≤ N.factorial * Real.exp y := by
    have := Real.pow_div_factorial_le_exp (x := y) hy N
    rw [div_le_iff₀ hfac] at this; linarith
  have hE : 0 < Real.exp (-y) := Real.exp_pos _
  have hEE : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have hE1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc y ^ c * Real.exp (-y) ≤ (1 + y ^ N) * Real.exp (-y) := by gcongr
    _ = Real.exp (-y) + y ^ N * Real.exp (-y) := by ring
    _ ≤ 1 + N.factorial * Real.exp y * Real.exp (-y) :=
        add_le_add hE1 (mul_le_mul_of_nonneg_right h2 hE.le)
    _ = 1 + N.factorial := by rw [mul_assoc, hEE, mul_one]

lemma sum_exp_le (b p : ℝ) (hb : 0 < b) (hp : 0 < p) (n : ℕ) :
    ∑ i ∈ range n, Real.exp (-b * (i:ℝ) ^ p) ≤ 1 + b ^ (-1 / p) * Real.Gamma (1 / p + 1) := by
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ p)) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (by norm_num) hp hb
    refine this.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp
  have hI := integral_exp_neg_mul_rpow hp hb
  have hnn : ∀ x : ℝ, 0 ≤ Real.exp (-b * x ^ p) := fun x => (Real.exp_pos _).le
  have hanti : ∀ m : ℕ, AntitoneOn (fun x : ℝ => Real.exp (-b * x ^ p)) (Set.Icc 0 (0 + m)) := by
    intro m x hx y hy hxy
    simp only
    apply Real.exp_le_exp.mpr
    have : x ^ p ≤ y ^ p := Real.rpow_le_rpow hx.1 hxy hp.le
    nlinarith
  have hGpos : 0 ≤ b ^ (-1 / p) * Real.Gamma (1 / p + 1) := by
    have := Real.Gamma_pos_of_pos (show (0:ℝ) < 1 / p + 1 by positivity)
    positivity
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
  | succ m =>
    rw [Finset.sum_range_succ']
    have h0 : Real.exp (-b * ((0:ℕ):ℝ) ^ p) = 1 := by
      simp [Real.zero_rpow hp.ne']
    have hs := (hanti m).sum_le_integral
    simp only [zero_add] at hs
    have hle : ∫ x in (0:ℝ)..m, Real.exp (-b * x ^ p) ≤
        ∫ x in Set.Ioi (0:ℝ), Real.exp (-b * x ^ p) := by
      rw [intervalIntegral.integral_of_le (Nat.cast_nonneg m)]
      exact setIntegral_mono_set hint (ae_of_all _ (fun x => hnn x))
        (Set.Ioc_subset_Ioi_self.eventuallyLE)
    rw [h0]
    linarith

end D39cda3a

theorem solution (r β a : ℝ) (hr : 0 ≤ r) (ha : 0 < a) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t →
      Summable (fun j : ℕ => (j : ℝ) ^ r * Real.exp (-((j : ℝ) ^ β) / (a * Real.sqrt t))) ∧
        ∑' j : ℕ, (j : ℝ) ^ r * Real.exp (-((j : ℝ) ^ β) / (a * Real.sqrt t)) ≤
          C * (t : ℝ) ^ (((r + 1) / β) / 2) := by
  set c := r / β with hc_def
  have hc : 0 ≤ c := div_nonneg hr hβ.le
  set K : ℝ := 1 + ((Nat.ceil c).factorial : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set G : ℝ := Real.Gamma (1 / β + 1) with hG_def
  have hG : 0 ≤ G := (Real.Gamma_pos_of_pos (by positivity)).le
  refine ⟨(2 * a) ^ c * K * (1 + (2 * a) ^ (1 / β) * G), fun t ht => ?_⟩
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0:ℝ) ≤ t := by linarith
  have hu1 : 1 ≤ Real.sqrt t := Real.one_le_sqrt.mpr ht'
  have hRHS : (t:ℝ) ^ (((r + 1) / β) / 2) = Real.sqrt t ^ c * Real.sqrt t ^ (1 / β) := by
    rw [← Real.rpow_add (by linarith), Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    congr 1; rw [hc_def]; field_simp
  rw [hRHS]
  set u := Real.sqrt t with hu
  set s := a * u with hs_def
  have hs : 0 < s := by positivity
  set b : ℝ := (2 * s)⁻¹ with hb_def
  have hb : 0 < b := by positivity
  have hpt : ∀ j : ℕ, (j:ℝ) ^ r * Real.exp (-((j:ℝ) ^ β) / s) ≤
      (2 * s) ^ c * K * Real.exp (-b * (j:ℝ) ^ β) := by
    intro j
    have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
    set y := b * (j:ℝ) ^ β with hy_def
    have hy : 0 ≤ y := by positivity
    have h1 : (j:ℝ) ^ r = (2 * s) ^ c * y ^ c := by
      rw [← Real.mul_rpow (by positivity) hy]
      have : 2 * s * y = (j:ℝ) ^ β := by rw [hy_def, hb_def]; field_simp
      rw [this, ← Real.rpow_mul hj]; congr 1; rw [hc_def]; field_simp
    have h2 : Real.exp (-((j:ℝ) ^ β) / s) = Real.exp (-y) * Real.exp (-y) := by
      rw [← Real.exp_add]; congr 1; rw [hy_def, hb_def]; field_simp; ring
    rw [h1, h2, show -b * (j:ℝ) ^ β = -y by rw [hy_def]; ring]
    have := D39cda3a.rpow_mul_exp_neg_le c y hc hy
    have hpos : 0 ≤ (2 * s) ^ c := by positivity
    have hE : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
    calc (2 * s) ^ c * y ^ c * (Real.exp (-y) * Real.exp (-y))
        = (2 * s) ^ c * (y ^ c * Real.exp (-y)) * Real.exp (-y) := by ring
      _ ≤ (2 * s) ^ c * K * Real.exp (-y) := by gcongr
  have hgsum : Summable (fun j : ℕ => Real.exp (-b * (j:ℝ) ^ β)) :=
    summable_of_sum_range_le (fun n => (Real.exp_pos _).le) (D39cda3a.sum_exp_le b β hb hβ)
  have htsg : ∑' j : ℕ, Real.exp (-b * (j:ℝ) ^ β) ≤ 1 + b ^ (-1 / β) * G :=
    Real.tsum_le_of_sum_range_le (fun n => (Real.exp_pos _).le) (D39cda3a.sum_exp_le b β hb hβ)
  have hfnn : ∀ j : ℕ, 0 ≤ (j:ℝ) ^ r * Real.exp (-((j:ℝ) ^ β) / s) := fun j => by positivity
  have hsum : Summable (fun j : ℕ => (j:ℝ) ^ r * Real.exp (-((j:ℝ) ^ β) / s)) :=
    Summable.of_nonneg_of_le hfnn hpt (hgsum.mul_left _)
  refine ⟨hsum, ?_⟩
  have hbpow : b ^ (-1 / β) = (2 * s) ^ (1 / β) := by
    rw [hb_def, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    congr 1; ring
  have h2s : 2 * s = (2 * a) * u := by rw [hs_def]; ring
  have hu0 : 0 ≤ u := by positivity
  have hv : 1 ≤ u ^ (1 / β) := Real.one_le_rpow hu1 (by positivity)
  calc ∑' j : ℕ, (j:ℝ) ^ r * Real.exp (-((j:ℝ) ^ β) / s)
      ≤ ∑' j : ℕ, (2 * s) ^ c * K * Real.exp (-b * (j:ℝ) ^ β) :=
        hsum.tsum_le_tsum hpt (hgsum.mul_left _)
    _ = (2 * s) ^ c * K * ∑' j : ℕ, Real.exp (-b * (j:ℝ) ^ β) := tsum_mul_left
    _ ≤ (2 * s) ^ c * K * (1 + (2 * s) ^ (1 / β) * G) := by rw [← hbpow]; gcongr
    _ ≤ (2 * a) ^ c * K * (1 + (2 * a) ^ (1 / β) * G) * (u ^ c * u ^ (1 / β)) := by
      rw [h2s, Real.mul_rpow (by positivity) hu0, Real.mul_rpow (by positivity) hu0]
      have hA : 0 ≤ (2 * a) ^ c * K * u ^ c := by positivity
      have hB : 0 ≤ (2 * a) ^ (1 / β) * G := by positivity
      nlinarith [mul_nonneg hA (sub_nonneg.2 hv), mul_nonneg (mul_nonneg hA hB) (sub_nonneg.2 hv)]
