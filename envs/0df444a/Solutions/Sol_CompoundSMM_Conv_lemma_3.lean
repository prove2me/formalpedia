-- Prove2me | solution 1 for CompoundSMM.Conv.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:43:49.640231+00:00
-- url     : https://prove2.me/submissions/2d655a6b-0130-4d73-b4a7-f42b82a5773c

import Mathlib
import Definitions.Def_CompoundSMM_Conv_Setting
open CompoundSMM.Conv Filter

theorem solution (N : ℕ → ℕ) (hN : SampleSizeCond N) :
    Summable (fun ν : ℕ => (1 - ((N (ν - 1) : ℝ) / N ν) ^ 2) * (1 / Real.sqrt (N (ν - 1)))) ∧
    Summable (fun ν : ℕ =>
      ((N ν : ℝ) - N (ν - 1)) / N ν * (1 / Real.sqrt ((N ν : ℝ) - N (ν - 1)))) := by
  obtain ⟨νbar, hνbar, c1, c2, c3, hc1, hc2, hc3, h⟩ := hN
  -- basic consequences for ν > νbar
  have key : ∀ ν : ℕ, νbar < ν →
      (N (ν - 1) : ℝ) + 1 ≤ N ν ∧ c2 * (ν : ℝ) ^ (1 + 2 * c1) ≤ N ν ∧
      ((N ν : ℝ) - N (ν - 1)) * ν ≤ c3 * N ν := by
    intro ν hν
    obtain ⟨h1, h2⟩ := h ν hν
    have hm1 := (le_max_left _ _).trans h1
    have hm2 := (le_max_right _ _).trans h1
    refine ⟨hm1, hm2, ?_⟩
    have hνpos : (0 : ℝ) < ν := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hν)
    have ha : (0 : ℝ) ≤ N (ν - 1) := by positivity
    have hden : 0 < 1 - c3 / ν := by
      by_contra hc
      push Not at hc
      have : (N (ν - 1) : ℝ) / (1 - c3 / ν) ≤ 0 := div_nonpos_of_nonneg_of_nonpos ha hc
      linarith
    rw [le_div_iff₀ hden] at h2
    have : (N ν : ℝ) * (1 - c3 / ν) * ν = N ν * ν - c3 * N ν := by field_simp
    nlinarith
  constructor
  · -- comparison with K * (m ^ (3/2))⁻¹, m = ν - 1
    set K : ℝ := 2 * |c3| / Real.sqrt c2
    have hg : Summable (fun ν : ℕ => K * ((((ν - 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2))⁻¹) := by
      rw [← summable_nat_add_iff 1]
      simp only [Nat.add_sub_cancel]
      exact (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left K
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    rw [eventually_atTop]
    refine ⟨νbar + 2, fun ν hν => ?_⟩
    obtain ⟨hb1, -, hb3⟩ := key ν (by omega)
    obtain ⟨-, ha2, -⟩ := key (ν - 1) (by omega)
    have hmν : ((ν - 1 : ℕ) : ℝ) = (ν : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    set a : ℝ := ((N (ν - 1) : ℕ) : ℝ)
    set b : ℝ := ((N ν : ℕ) : ℝ)
    set m : ℝ := ((ν - 1 : ℕ) : ℝ) with hm
    have hm1 : (1 : ℝ) ≤ m := by rw [hm]; exact_mod_cast (by omega : 1 ≤ ν - 1)
    have hνm : m ≤ ν := by rw [hmν]; linarith
    -- a ≥ c2 * m
    have hpow : m ≤ m ^ (1 + 2 * c1) := by
      calc m = m ^ (1 : ℝ) := (Real.rpow_one m).symm
        _ ≤ m ^ (1 + 2 * c1) := Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
    have ha : c2 * m ≤ a := le_trans (by gcongr) ha2
    have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
    have hb0 : 0 < b := by linarith
    -- 0 ≤ 1 - (a/b)^2 ≤ 2 (b - a)/b ≤ 2 c3 / m
    have hr0 : 0 ≤ 1 - (a / b) ^ 2 := by
      rw [sub_nonneg, div_pow, div_le_one (by positivity)]
      exact pow_le_pow_left₀ ha0.le (by linarith) 2
    have hr1 : 1 - (a / b) ^ 2 ≤ 2 * |c3| / m := by
      have e : 1 - (a / b) ^ 2 = (b - a) * (b + a) / b ^ 2 := by field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      have hνr : (0 : ℝ) < ν := by linarith
      have h3 : (b - a) * m ≤ |c3| * b := by
        have := le_abs_self c3
        nlinarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ b + a)
      have h5 : (b + a) * (|c3| * b) ≤ (2 * b) * (|c3| * b) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith
    have hsqrt : Real.sqrt c2 * Real.sqrt m ≤ Real.sqrt a := by
      rw [← Real.sqrt_mul hc2.le]; exact Real.sqrt_le_sqrt ha
    have hm32 : m ^ ((3 : ℝ) / 2) = m * Real.sqrt m := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]; norm_num
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hm32]
    have hsc : 0 < Real.sqrt c2 := Real.sqrt_pos.mpr hc2
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
    calc (1 - (a / b) ^ 2) * (1 / Real.sqrt a)
        ≤ (2 * |c3| / m) * (1 / (Real.sqrt c2 * Real.sqrt m)) := by
          gcongr
      _ = K * (m * Real.sqrt m)⁻¹ := by
          simp only [K]; field_simp
  · set K : ℝ := Real.sqrt (|c3| / c2)
    have hg : Summable (fun ν : ℕ => K * ((ν : ℝ) ^ (1 + c1))⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left K
    refine Summable.of_norm_bounded_eventually_nat hg ?_
    rw [eventually_atTop]
    refine ⟨νbar + 1, fun ν hν => ?_⟩
    obtain ⟨hb1, hb2, hb3⟩ := key ν (by omega)
    set a : ℝ := ((N (ν - 1) : ℕ) : ℝ)
    set b : ℝ := ((N ν : ℕ) : ℝ)
    have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast (by omega : 1 ≤ ν)
    have hd : 1 ≤ b - a := by linarith
    have hb0 : 0 < b := by have : (0:ℝ) ≤ a := by positivity
                           linarith
    have hpow2 : ((ν : ℝ) ^ (1 + c1)) ^ 2 = ν * (ν : ℝ) ^ (1 + 2 * c1) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      rw [show (1 + c1) * ((2 : ℕ) : ℝ) = 1 + (1 + 2 * c1) by push_cast; ring]
      rw [Real.rpow_add (by linarith), Real.rpow_one]
    have hP : 0 < (ν : ℝ) ^ (1 + c1) := Real.rpow_pos_of_pos (by linarith) _
    have hP2 : 0 < (ν : ℝ) ^ (1 + 2 * c1) := Real.rpow_pos_of_pos (by linarith) _
    -- term = sqrt(b - a) / b
    have hterm : (b - a) / b * (1 / Real.sqrt (b - a)) = Real.sqrt (b - a) / b := by
      have hs : 0 < Real.sqrt (b - a) := Real.sqrt_pos.mpr (by linarith)
      field_simp
      rw [Real.sq_sqrt (by linarith)]
    rw [Real.norm_eq_abs, hterm, abs_of_nonneg (by positivity)]
    -- compare squares
    have hR : 0 ≤ K * ((ν : ℝ) ^ (1 + c1))⁻¹ := by positivity
    apply le_of_pow_le_pow_left₀ two_ne_zero hR
    rw [div_pow, Real.sq_sqrt (by linarith), mul_pow, inv_pow, hpow2, Real.sq_sqrt (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have h3 : (b - a) * ν ≤ |c3| * b := le_trans hb3 (by gcongr; exact le_abs_self c3)
    -- (b-a) ≤ |c3| b / ν and b ≥ c2 ν^(1+2c1)
    rw [show |c3| / c2 * (↑ν * (ν : ℝ) ^ (1 + 2 * c1))⁻¹ * b ^ 2
        = (|c3| * b) * b / (c2 * (ν : ℝ) ^ (1 + 2 * c1) * ν) by field_simp]
    rw [le_div_iff₀ (by positivity)]
    have hba : 0 ≤ b - a := by linarith
    calc (b - a) * (c2 * (ν : ℝ) ^ (1 + 2 * c1) * ↑ν)
        = ((b - a) * ν) * (c2 * (ν : ℝ) ^ (1 + 2 * c1)) := by ring
      _ ≤ (|c3| * b) * b := by
          apply mul_le_mul h3 hb2 (by positivity) (by positivity)
