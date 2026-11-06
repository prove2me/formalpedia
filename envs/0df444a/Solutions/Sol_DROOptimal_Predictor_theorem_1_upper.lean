-- Prove2me | solution 1 for DROOptimal.Predictor.theorem_1_upper
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:02:34.739842+00:00
-- url     : https://prove2.me/submissions/80b4d13b-34e5-440f-8468-b455232d39d9

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Theorems.Thm_DROOptimal_Predictor_theorem_2

open DROOptimal.Predictor Filter

theorem solution {d : ℕ} (ℙ : Δ d) (D : Set (Δ d)) (hD : MeasurableSet D) (s : ℝ)
    (hs : (s : EReal) < ⨅ ℙ' ∈ D, relEntropy ℙ' ℙ) :
    ∀ᶠ T : ℕ in Filter.atTop, empProb ℙ T D ≤ Real.exp (-(s * (T : ℝ))) := by
  obtain ⟨s', hs1, hs2⟩ := EReal.lt_iff_exists_real_btwn.mp hs
  have hss : s < s' := by exact_mod_cast hs1
  set b := s' - s with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  -- polynomial ≤ exponential eventually
  have hlo := isLittleO_pow_exp_pos_mul_atTop d hb0
  have hev : ∀ᶠ x : ℝ in atTop, ‖x ^ d‖ ≤ (1 / 2 ^ d) * ‖Real.exp (b * x)‖ :=
    hlo.def (by positivity)
  have hevN : ∀ᶠ T : ℕ in atTop, ‖(T : ℝ) ^ d‖ ≤ (1 / 2 ^ d) * ‖Real.exp (b * T)‖ :=
    tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN, eventually_ge_atTop 1] with T hT hT1
  have hT1' : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  have h2 := theorem_2 ℙ D hD T hT1 s' hs2.le
  have hpoly : ((T : ℝ) + 1) ^ d ≤ Real.exp (b * T) := by
    have hT0 : (0 : ℝ) ≤ T := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hT0 d),
      abs_of_pos (Real.exp_pos _)] at hT
    have : ((T : ℝ) + 1) ^ d ≤ (2 * T) ^ d := pow_le_pow_left₀ (by linarith) (by linarith) d
    rw [mul_pow] at this
    have h2pos : (0 : ℝ) < 2 ^ d := by positivity
    calc ((T : ℝ) + 1) ^ d ≤ 2 ^ d * (T : ℝ) ^ d := this
      _ ≤ 2 ^ d * ((1 / 2 ^ d) * Real.exp (b * T)) := mul_le_mul_of_nonneg_left hT h2pos.le
      _ = Real.exp (b * T) := by field_simp
  calc empProb ℙ T D ≤ ((T : ℝ) + 1) ^ d * Real.exp (-((T : ℝ) * s')) := h2
    _ ≤ Real.exp (b * T) * Real.exp (-((T : ℝ) * s')) :=
        mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = Real.exp (-(s * (T : ℝ))) := by
        rw [← Real.exp_add]; congr 1; rw [hb]; ring
