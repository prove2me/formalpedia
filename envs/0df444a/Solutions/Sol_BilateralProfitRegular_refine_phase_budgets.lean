-- Prove2me | solution 1 for BilateralProfitRegular.refine_phase_budgets
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T16:29:15.023198+00:00
-- url     : https://prove2.me/submissions/8c01aa15-c532-4823-8f30-902638c73b9d

import Mathlib
import Definitions.Def_BilateralProfitRegular_Refinement


section BundlePart000


namespace BilateralProfitRegular

private theorem scale_factor (j : ℕ) :
    (4 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
  norm_num

private theorem double_scale_factor (j : ℕ) :
    (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num

private theorem log_eight (T : ℕ) (hT : 0 < T) :
    Real.log (8 * (T : ℝ)) =
      Real.log (2 * (T : ℝ)) + 2 * Real.log 2 := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  rw [show 8 * (T : ℝ) = 2 ^ 2 * (2 * T) by ring,
    Real.log_mul (by norm_num) (by positivity : (2 * (T : ℝ)) ≠ 0), Real.log_pow]
  norm_num
  ring

set_option maxHeartbeats 1200000 in
/-- One choice of the run-size constant simultaneously supports both probability
budgets and the normalized expected regret at every admissible phase. -/
private theorem refine_phase_budgets (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (T j : ℕ), 0 < T →
      (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) → ∀ δ : ℝ, 0 < δ →
      let n := phaseLen C₀ T j
      let M := numCopies C₀ T
      let ε := acc δ j
      0 < n ∧ 0 < ε ∧
      C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤ (n : ℝ) * ε / (800 * δ ^ 2) ∧
      (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) ∧
      (M : ℝ) * (2 * Real.exp (-(2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2))) ≤
        1 / (2 * (T : ℝ)) := by
  obtain ⟨D, hDbig, hD₁, hD₂⟩ : ∃ D : ℝ, 1000000 ≤ D ∧ C₁ ≤ D ∧ C₂ ≤ D := by
    refine ⟨1000000 * (1 + C₁ + C₂), ?_, ?_, ?_⟩ <;> linarith only [hC₁, hC₂]
  have hD : 0 < D := by linarith only [hDbig]
  have hD1 : 1 ≤ D := by linarith only [hDbig]
  refine ⟨D ^ 8, by positivity, ?_⟩
  intro T j hT hj δ hδ
  dsimp only
  let n := phaseLen (D ^ 8) T j
  let M := numCopies (D ^ 8) T
  let ε := acc δ j
  let L := Real.log (2 * (T : ℝ))
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hT' : (0 : ℝ) < T := by positivity
  have hlog2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith only [hT1])
  have hL : 1 / 2 ≤ L := by linarith only [Real.log_two_gt_d9, hlog2]
  have hL' : 0 < L := by linarith only [hL]
  have hlogLT : Real.log (T : ℝ) ≤ L := Real.log_le_log hT' (by linarith only [hT'])
  have hlog4 : Real.log 4 < 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have hlog8 : Real.log 8 < 3 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
    linarith only [Real.log_two_lt_d9]
  have hfloor : (4 : ℝ) ^ j * D ^ 8 * L ^ 4 ≤ n := by
    change _ ≤ (↑(4 ^ j * ⌈D ^ 8 * L ^ 4⌉₊) : ℝ)
    push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (by positivity)
  have hn' : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hfloor
  have hn : 0 < n := by exact_mod_cast hn'
  have hε : 0 < ε := by dsimp [ε, acc]; positivity
  have hsqrt : (2 : ℝ) ^ j * D ^ 4 * L ^ 2 ≤ Real.sqrt n := by
    apply Real.le_sqrt_of_sq_le
    convert hfloor using 1
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm j 2, pow_mul]
    ring
  have hCLR : (1 : ℝ) ≤ D ^ 8 * L ^ 4 := by
    have hg : (2 : ℝ) ^ 8 * (1 / 2 : ℝ) ^ 4 ≤ D ^ 8 * L ^ 4 := by gcongr <;> linarith only [hDbig, hL, hD, hD1]
    norm_num at hg
    linarith only [hg]
  have hCMR : (1 : ℝ) ≤ D ^ 8 * L := by
    have hg : (2 : ℝ) ^ 8 * (1 / 2 : ℝ) ≤ D ^ 8 * L := by gcongr <;> linarith only [hDbig, hL, hD, hD1]
    norm_num at hg
    linarith only [hg]
  have hlogn : Real.log (2 * (n : ℝ)) ≤ 24 * D * L := by
    by_cases hj0 : j = 0
    · subst j
      have hn0 : (n : ℝ) ≤ 2 * (D ^ 8 * L ^ 4) := by
        change (↑(4 ^ (0 : ℕ) * ⌈D ^ 8 * L ^ 4⌉₊) : ℝ) ≤ _
        simp only [pow_zero, one_mul]
        linarith only [hCLR, Nat.ceil_lt_add_one (show 0 ≤ D ^ 8 * L ^ 4 by positivity)]
      calc
        _ ≤ Real.log (4 * (D ^ 8 * L ^ 4)) := Real.log_le_log (by positivity) (by linarith only [hn0])
        _ = Real.log 4 + 8 * Real.log D + 4 * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
            Real.log_pow, Real.log_pow]
          push_cast
          ring
        _ ≤ 10 * D + 4 * L := by
          linarith only [hlog4, hD1, Real.log_le_sub_one_of_pos hD, Real.log_le_sub_one_of_pos hL']
        _ ≤ _ := by
          have hab : 10 * D ≤ 20 * D * L := by nlinarith only [mul_nonneg hD.le (sub_nonneg.mpr hL)]
          have hbc : 4 * L ≤ 4 * D * L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
          linarith only [hab, hbc]
    · have hj := hj.resolve_left hj0
      have hnj : n ≤ 4 * T := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        change 4 ^ (k + 1) * ⌈D ^ 8 * L ^ 4⌉₊ ≤ 4 * T
        have hprev : 4 ^ k * ⌈D ^ 8 * L ^ 4⌉₊ ≤ T := by simpa [phaseLen, L] using hj
        rw [pow_succ, mul_right_comm, mul_comm _ (4 : ℕ)]
        exact Nat.mul_le_mul_left _ hprev
      have hnj' : (n : ℝ) ≤ 4 * (T : ℝ) := by exact_mod_cast hnj
      calc
        _ ≤ Real.log (8 * (T : ℝ)) := Real.log_le_log (by positivity) (by linarith only [hnj'])
        _ = L + 2 * Real.log 2 := log_eight T hT
        _ ≤ 3 * L := by linarith only [hlog2]
        _ ≤ _ := by nlinarith only [hL', mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
  have hlogn_pos : 0 ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [h1]
  have hscaled_sqrt : δ * D ^ 4 * L ^ 2 ≤ ε * Real.sqrt n := by
    calc
      _ = ε * ((2 : ℝ) ^ j * D ^ 4 * L ^ 2) := by
        have hscale := double_scale_factor j
        change _ = (δ * (1 / 2) ^ j) * _
        calc
          _ = δ * ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) * D ^ 4 * L ^ 2 := by rw [hscale, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsqrt hε.le
  have hnorm : 800 * C₂ * (24 * D * L) ^ 2 ≤ D ^ 4 * L ^ 2 := by
    have h1 : 460800 * C₂ ≤ D ^ 2 := by
      calc
        _ ≤ D * D := mul_le_mul (by linarith only [hDbig]) hD₂ hC₂.le hD.le
        _ = _ := by ring
    calc
      _ = ((460800 : ℝ) * C₂) * (D ^ 2 * L ^ 2) := by ring
      _ ≤ D ^ 2 * (D ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = _ := by ring
  have hreg : C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤
      (n : ℝ) * ε / (800 * δ ^ 2) := by
    have h₁ : 800 * C₂ * Real.log (2 * (n : ℝ)) ^ 2 ≤ D ^ 4 * L ^ 2 := by
      refine le_trans ?_ hnorm
      gcongr
    have h₂ : δ * (800 * C₂ * Real.log (2 * (n : ℝ)) ^ 2) ≤ ε * Real.sqrt n :=
      (mul_le_mul_of_nonneg_left h₁ hδ.le).trans (by simpa only [mul_assoc] using hscaled_sqrt)
    have h₃ := mul_le_mul_of_nonneg_right h₂ (Real.sqrt_nonneg (n : ℝ))
    rw [mul_assoc ε, ← pow_two, Real.sq_sqrt hn'.le] at h₃
    apply (le_div_iff₀ (by positivity : 0 < 800 * δ ^ 2)).2
    convert h₃ using 1
    · field_simp
    · ring
  have hMlo : D ^ 8 * L ≤ M := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * (D ^ 8 * L) := by
    change (↑⌈D ^ 8 * L⌉₊ : ℝ) ≤ _
    linarith only [hCMR, Nat.ceil_lt_add_one (show 0 ≤ D ^ 8 * L by positivity)]
  have hfail : (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) := by
    have hL_M : L ≤ M := le_trans (le_mul_of_one_le_left hL'.le (one_le_pow₀ hD1)) hMlo
    have hlog4' : 1 ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
      linarith only [Real.log_two_gt_d9]
    have hM' : (0 : ℝ) ≤ M := by positivity
    have hprod := mul_le_mul_of_nonneg_left hlog4' hM'
    have hx : -(M : ℝ) * Real.log 4 ≤ -L := by linarith only [hprod, hL_M]
    have he := Real.exp_le_exp.mpr hx
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4),
      Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < 2 * (T : ℝ))] at he
    simpa only [one_div, inv_pow] using he
  refine ⟨hn, hε, hreg, hfail, ?_⟩
  let a := (2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2)
  have ha : D ^ 8 * L ^ 4 / (80000 * C₁ ^ 2) ≤ a := by
    calc
      _ = ((4 : ℝ) ^ j * ((1 / 2 : ℝ) ^ j) ^ 2) *
          (D ^ 8 * L ^ 4 / (80000 * C₁ ^ 2)) := by rw [scale_factor, one_mul]
      _ = (2 * ((4 : ℝ) ^ j * D ^ 8 * L ^ 4) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2) := by
        change _ = 2 * _ * (δ * (1 / 2) ^ j / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2
        field_simp
        ring
      _ ≤ a := by
        dsimp [a]
        gcongr
  have hA_L : 24 * D * L ≤ a := by
    have h8 : 15360000 * C₁ ^ 2 * D ≤ D ^ 8 := by
      have h₇ : 15360000 * C₁ ^ 2 ≤ D ^ 7 := by
        calc
          _ ≤ 15360000 * D ^ 2 := by gcongr
          _ ≤ D ^ 5 * D ^ 2 := by
            gcongr
            calc
              (15360000 : ℝ) ≤ (1000000 : ℝ) ^ 5 := by norm_num
              _ ≤ D ^ 5 := by gcongr
          _ = _ := by ring
      calc
        _ ≤ D ^ 7 * D := mul_le_mul_of_nonneg_right h₇ hD.le
        _ = _ := by ring
    have hL3 : (1 / 8 : ℝ) ≤ L ^ 3 := by
      calc
        _ = (1 / 2 : ℝ) ^ 3 := by norm_num
        _ ≤ _ := by gcongr
    have h4 : L / 8 ≤ L ^ 4 := by nlinarith only [mul_le_mul_of_nonneg_right hL3 hL'.le]
    refine le_trans ?_ ha
    apply (le_div_iff₀ (by positivity : 0 < 80000 * C₁ ^ 2)).2
    calc
      _ = (15360000 * C₁ ^ 2 * D) * (L / 8) := by ring
      _ ≤ D ^ 8 * L ^ 4 := by gcongr
  have hlog : Real.log (8 * (D ^ 8 * L) * (T : ℝ)) ≤ 24 * D * L := by
    calc
      _ = Real.log 8 + 8 * Real.log D + Real.log L + Real.log (T : ℝ) := by
        rw [Real.log_mul (by positivity) hT'.ne', Real.log_mul (by norm_num) (by positivity),
          Real.log_mul (by positivity) hL'.ne', Real.log_pow]
        push_cast
        ring
      _ ≤ 11 * D + 2 * L := by
        linarith only [hlog8, hD1, Real.log_le_sub_one_of_pos hD, Real.log_le_sub_one_of_pos hL', hlogLT]
      _ ≤ _ := by
        have hab : 11 * D ≤ 22 * D * L := by nlinarith only [mul_nonneg hD.le (sub_nonneg.mpr hL)]
        have hbc : 2 * L ≤ 2 * D * L := by nlinarith only [mul_nonneg (sub_nonneg.mpr hD1) hL'.le]
        linarith only [hab, hbc]
  have he : 8 * (D ^ 8 * L) * (T : ℝ) ≤ Real.exp a := by
    rw [← Real.exp_log (show 0 < 8 * (D ^ 8 * L) * (T : ℝ) by positivity), Real.exp_le_exp]
    exact hlog.trans hA_L
  change (M : ℝ) * (2 * Real.exp (-a)) ≤ 1 / (2 * (T : ℝ))
  apply (le_div_iff₀ (by positivity : 0 < 2 * (T : ℝ))).2
  rw [Real.exp_neg]
  calc
    _ ≤ (2 * (D ^ 8 * L)) * (2 * (Real.exp a)⁻¹) * (2 * (T : ℝ)) := by gcongr
    _ = (8 * (D ^ 8 * L) * (T : ℝ)) / Real.exp a := by ring
    _ ≤ 1 := by simpa only [div_le_one (Real.exp_pos _)] using he

end BilateralProfitRegular
end BundlePart000

open BilateralProfitRegular

theorem solution (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (T j : ℕ), 0 < T →
      (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) → ∀ δ : ℝ, 0 < δ →
      let n := phaseLen C₀ T j
      let M := numCopies C₀ T
      let ε := acc δ j
      0 < n ∧ 0 < ε ∧
      C₂ / δ * Real.sqrt n * Real.log (2 * (n : ℝ)) ^ 2 ≤ (n : ℝ) * ε / (800 * δ ^ 2) ∧
      (1 / 4 : ℝ) ^ M ≤ 1 / (2 * (T : ℝ)) ∧
      (M : ℝ) * (2 * Real.exp (-(2 * (n : ℝ) * (ε / (400 * δ ^ 2)) ^ 2 / (C₁ / δ) ^ 2))) ≤
        1 / (2 * (T : ℝ)) := by
  exact BilateralProfitRegular.refine_phase_budgets C₁ C₂ hC₁ hC₂
