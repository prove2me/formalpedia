-- Prove2me | solution 1 for BehrendWindows.exists_large_atMostTwoPerAP
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:59:31.665181+00:00
-- url     : https://prove2.me/submissions/f123f59f-1901-4027-811c-c61296699e20

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP
import Theorems.Thm_BehrendWindows_exists_atMostTwoPerAP_of_box
import Theorems.Thm_BehrendWindows_small_range_bound

open BehrendWindows

/-- A one-point set is `m`-sparse. -/
private lemma atMostTwoPerAP_singleton (m : ℕ) : AtMostTwoPerAP {0} m := by
  intro a d hd k₁ k₂ k₃ h1 _ _ ⟨m1, m2, _⟩
  simp only [Finset.mem_singleton] at m1 m2
  have : ((k₂ : ℤ) - k₁) * d = 0 := by linear_combination m2 - m1
  rcases mul_eq_zero.1 this with h | h
  · omega
  · exact hd h

/-- The analytic core: with `ℓ = log m ≥ 1`, `L = log N = u² ℓ`, `u ≥ 8` and `S = ⌊u⌋₊`,
`S log(2m) + log S + 2L/S ≤ 8 u ℓ`. -/
private lemma exponent_bound (u ℓ L : ℝ) (S : ℕ) (m : ℕ) (hℓ : 1 ≤ ℓ) (hlm : Real.log m = ℓ)
    (hm : 3 ≤ m) (hu : 8 ≤ u) (hL : L = u ^ 2 * ℓ) (hS1 : (S : ℝ) ≤ u) (hS2 : u < S + 1) :
    S * Real.log (2 * m) + Real.log S + (L / S + L / S) ≤ 8 * (u * ℓ) := by
  have hSpos : (0 : ℝ) < S := by linarith
  have hS_half : u ≤ 2 * S := by linarith
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  -- log(2m) ≤ 2ℓ
  have h2m : Real.log (2 * m) ≤ 2 * ℓ := by
    rw [Real.log_mul (by norm_num) hm0.ne', hlm]
    have h3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hA : S * Real.log (2 * m) ≤ u * (2 * ℓ) := by
    apply mul_le_mul hS1 h2m (Real.log_nonneg (by
      have : (3 : ℝ) ≤ m := by exact_mod_cast hm
      linarith)) (by linarith)
  have hB : Real.log S ≤ u * ℓ := by
    have := Real.log_le_sub_one_of_pos hSpos
    nlinarith
  have hC : L / S ≤ 2 * (u * ℓ) := by
    rw [div_le_iff₀ hSpos, hL]
    have : 0 ≤ u * ℓ := by positivity
    nlinarith
  have : 0 ≤ u * ℓ := mul_nonneg (by linarith) (by linarith)
  linarith

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, ∃ T : Finset ℤ,
      T ⊆ Finset.Ico (0 : ℤ) N ∧ AtMostTwoPerAP T m ∧
      (N : ℝ) * Real.exp (-C * Real.sqrt (Real.log N * Real.log m)) ≤ (T.card : ℝ) := by
  refine ⟨8, by norm_num, fun N m => ?_⟩
  -- Case `m ≤ 2`: the whole range works.
  by_cases hm2 : m ≤ 2
  · refine ⟨Finset.Ico (0 : ℤ) N, le_rfl, ?_, ?_⟩
    · intro a d _ k₁ k₂ k₃ h1 h2 h3; omega
    · rw [Int.card_Ico]
      simp only [sub_zero, Int.toNat_natCast]
      apply mul_le_of_le_one_right (Nat.cast_nonneg _)
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.2
      have := Real.sqrt_nonneg (Real.log N * Real.log m)
      nlinarith
  have hm : 3 ≤ m := by omega
  -- Case `N = 0`.
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    exact ⟨∅, by simp, by intro a d _ k₁ k₂ k₃ _ _ _ h; simp at h, by simp⟩
  have hN1 : 1 ≤ N := hNpos
  -- Case `N ≤ m ^ 64`: a single point works.
  by_cases hsmall : (N : ℝ) ≤ (m : ℝ) ^ ((8 : ℝ) ^ 2)
  · refine ⟨{0}, ?_, atMostTwoPerAP_singleton m, ?_⟩
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      simp only [Finset.mem_Ico, le_refl, true_and]
      exact_mod_cast hNpos
    · simpa using small_range_bound 8 (by norm_num) N m hN1 hsmall
  -- Main case.
  push Not at hsmall
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hNpos
  set ℓ := Real.log m with hℓdef
  set L := Real.log N with hLdef
  have hℓ1 : 1 ≤ ℓ := by
    rw [Real.le_log_iff_exp_le hm0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hLbig : 64 * ℓ < L := by
    have := Real.log_lt_log (by positivity) hsmall
    rw [Real.log_rpow hm0] at this
    norm_num at this
    linarith
  set u := Real.sqrt (L / ℓ) with hudef
  have hu2 : u ^ 2 = L / ℓ := Real.sq_sqrt (by positivity)
  have hL : L = u ^ 2 * ℓ := by rw [hu2]; field_simp
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu8 : 8 ≤ u := by
    have : (8 : ℝ) ^ 2 ≤ u ^ 2 := by
      rw [hu2, le_div_iff₀ hℓ0]; linarith
    nlinarith
  have hsq : Real.sqrt (L * ℓ) = u * ℓ := by
    have : L * ℓ = (L / ℓ) * (ℓ * ℓ) := by field_simp
    rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul_self hℓ0.le]
  -- parameters
  set S : ℕ := ⌊u⌋₊ with hSdef
  have hS1 : (S : ℝ) ≤ u := Nat.floor_le hu0
  have hS2 : u < S + 1 := Nat.lt_floor_add_one u
  have hSge : 1 ≤ S := Nat.le_floor (by simp; linarith)
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hSge
  have hSne : S ≠ 0 := by omega
  set r : ℝ := (N : ℝ) ^ ((S : ℝ)⁻¹) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos hN0 _
  have hrS : r ^ S = N := Real.rpow_inv_natCast_pow hN0.le hSne
  have hrexp : r = Real.exp (L / S) := by
    rw [hrdef, Real.rpow_def_of_pos hN0, div_eq_mul_inv]
  set d : ℕ := ⌊r / m⌋₊ with hddef
  have hd_le : (d : ℝ) ≤ r / m := Nat.floor_le (by positivity)
  have hd_lt : r / m < d + 1 := Nat.lt_floor_add_one _
  -- m ≤ r, so d ≥ 1
  have hmS : (m : ℝ) ^ S ≤ N := by
    have e1 : (m : ℝ) ^ S = Real.exp (S * ℓ) := by
      rw [Real.exp_nat_mul, hℓdef, Real.exp_log hm0]
    rw [e1, ← Real.exp_log hN0]
    apply Real.exp_le_exp.2
    rw [← hLdef, hL]
    have : (S : ℝ) * ℓ ≤ u * ℓ := mul_le_mul_of_nonneg_right hS1 hℓ0.le
    nlinarith
  have hmr : (m : ℝ) ≤ r := by
    rw [← pow_le_pow_iff_left₀ hm0.le hr0.le hSne, hrS]; exact hmS
  have hd1 : 1 ≤ d := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hm0]; linarith)
  have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hmd_le : (m : ℝ) * d ≤ r := by rwa [le_div_iff₀ hm0, mul_comm] at hd_le
  have hd_r : (d : ℝ) ≤ r := by
    have : (d : ℝ) ≤ m * d :=
      le_mul_of_one_le_left (Nat.cast_nonneg d) (by exact_mod_cast (by omega : 1 ≤ m))
    linarith
  have hr_lt : r < 2 * m * d := by
    have := (div_lt_iff₀ hm0).1 hd_lt
    nlinarith
  -- (m d)^S ≤ N
  have hbox : (m * d) ^ S ≤ N := by
    have : ((m : ℝ) * d) ^ S ≤ N := by
      rw [← hrS]; exact pow_le_pow_left₀ (by positivity) hmd_le S
    exact_mod_cast this
  -- N ≤ (2m)^S d^S
  have hNup : (N : ℝ) ≤ (2 * m) ^ S * d ^ S := by
    rw [← mul_pow, ← hrS]
    exact pow_le_pow_left₀ hr0.le hr_lt.le S
  obtain ⟨T, hTsub, hTap, hTcard⟩ := exists_atMostTwoPerAP_of_box S d m hSge hd1 hm
  refine ⟨T, hTsub.trans (Finset.Ico_subset_Ico_right (by exact_mod_cast hbox)), hTap, ?_⟩
  refine le_trans ?_ hTcard
  rw [hsq]
  -- exponent bound
  have hE := exponent_bound u ℓ L S m hℓ1 rfl hm hu8 hL hS1 hS2
  have hprod : (2 * (m : ℝ)) ^ S * S * r ^ 2 =
      Real.exp (S * Real.log (2 * m) + Real.log S + (L / S + L / S)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity),
      Real.exp_log hSpos, ← hrexp]
    ring
  have hA : Real.exp (-8 * (u * ℓ)) * ((2 * (m : ℝ)) ^ S * S * r ^ 2) ≤ 1 := by
    rw [hprod, ← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.2
    linarith
  have hden : (0 : ℝ) < S * (d : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  calc (N : ℝ) * Real.exp (-8 * (u * ℓ)) * (S * (d : ℝ) ^ 2)
      ≤ ((2 * m) ^ S * d ^ S) * Real.exp (-8 * (u * ℓ)) * (S * r ^ 2) := by
        gcongr
    _ = (d : ℝ) ^ S * (Real.exp (-8 * (u * ℓ)) * ((2 * (m : ℝ)) ^ S * S * r ^ 2)) := by ring
    _ ≤ (d : ℝ) ^ S := mul_le_of_le_one_right (by positivity) hA
