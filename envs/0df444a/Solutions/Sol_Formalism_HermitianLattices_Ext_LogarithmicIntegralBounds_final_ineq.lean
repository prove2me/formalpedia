-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.final_ineq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:23.742465+00:00
-- url     : https://prove2.me/submissions/bdb842f4-1ffa-437a-af34-1478c2e7a8dc

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
set_option maxHeartbeats 1000000
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (ε c₀ c₃ A₀ C₀ L u lm ℓm ℓ : ℝ) (hε : 0 < ε) (hc₀ : 0 < c₀) (hc₃ : 0 < c₃)
    (hL1 : 2 ≤ L) (hL2 : 8 * (ε / 5 + 5 + Real.log 128) / c₀ ≤ L)
    (hL3 : 8 * (3 + Real.log (32 * (|A₀| + 1))) / c₃ ≤ L) (hL4 : Real.log (32 * (|A₀| + 1)) ≤ L)
    (hL5 : 8 * |C₀| * (Real.log 806 + ε / 5 + 1) ≤ L)
    (hu1 : (1 / 4) * L ^ 2 * ℓm ≤ u) (hu2 : (200 + 16 / c₃) * L ^ 3 ≤ u)
    (hlogu : Real.log u ≤ (ε / 5 + 2) * L)
    (hℓm : ℓm ≤ 4 * Real.exp (ε / 5 * L))
    (hlm0 : 2 ≤ lm) (hlm : lm ≤ ℓ) (hℓ : ℓ ≤ ℓm + 800 * L) :
    C₀ * lm * Real.log (lm + 2) ≤ u ∧
    16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ Real.exp (-(3 * L)) / 8 ∧
    2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u))) ≤ Real.exp (-(3 * L)) / 8 ∧
    Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(3 * L)) / 4 := by
  have hL0 : 0 < L := by linarith
  have hL1' : 1 ≤ L := by linarith
  have hc3L3 : 0 ≤ 16 / c₃ * L ^ 3 := by positivity
  have hu200 : 200 * L ^ 3 ≤ u := by nlinarith [hu2]
  have hu0 : 0 < u := by nlinarith [pow_pos hL0 3]
  have hkey : L ^ 2 * (ℓm + 800 * L) / 8 ≤ u := by nlinarith [hu1, hu2]
  have hℓ0 : 0 < ℓ := by linarith
  have hlm0' : 0 < lm := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hlog_pos : 0 < Real.log (lm + 2) := Real.log_pos (by linarith)
    rcases le_or_gt C₀ 0 with hC | hC
    · have : C₀ * lm * Real.log (lm + 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC hlm0'.le) hlog_pos.le
      linarith
    · have hexp1 : 1 ≤ Real.exp (ε / 5 * L) := Real.one_le_exp (by positivity)
      have hlm2 : lm + 2 ≤ 806 * L * Real.exp (ε / 5 * L) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hexp1) (by linarith : (0 : ℝ) ≤ 806 * L - 4)]
      have hloglm : Real.log (lm + 2) ≤ Real.log 806 + Real.log L + ε / 5 * L := by
        calc Real.log (lm + 2) ≤ Real.log (806 * L * Real.exp (ε / 5 * L)) :=
              Real.log_le_log (by linarith) hlm2
          _ = Real.log 806 + Real.log L + ε / 5 * L := by
              rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
                Real.log_exp]
      have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
      have h806 : 0 ≤ Real.log 806 := Real.log_nonneg (by norm_num)
      have hlog2 : Real.log (lm + 2) ≤ L * (Real.log 806 + ε / 5 + 1) := by
        nlinarith [mul_nonneg (sub_nonneg.2 hL1') h806]
      rw [abs_of_pos hC] at hL5
      have hC' : C₀ * Real.log (lm + 2) ≤ L ^ 2 / 8 := by
        calc C₀ * Real.log (lm + 2) ≤ C₀ * (L * (Real.log 806 + ε / 5 + 1)) :=
              mul_le_mul_of_nonneg_left hlog2 hC.le
          _ = L * (C₀ * (Real.log 806 + ε / 5 + 1)) := by ring
          _ ≤ L * (L / 8) := mul_le_mul_of_nonneg_left (by linarith) hL0.le
          _ = L ^ 2 / 8 := by ring
      calc C₀ * lm * Real.log (lm + 2) = lm * (C₀ * Real.log (lm + 2)) := by ring
        _ ≤ lm * (L ^ 2 / 8) := mul_le_mul_of_nonneg_left hC' hlm0'.le
        _ ≤ (ℓm + 800 * L) * (L ^ 2 / 8) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ u := by linarith [hkey]
  ·
    have hlog128 : 0 < Real.log 128 := Real.log_pos (by norm_num)
    have harg : 3 * L + Real.log 128 + Real.log u ≤ c₀ / ℓ * u := by
      have h1 : ℓ * L ^ 2 / 8 ≤ u := by
        nlinarith [hkey, mul_le_mul_of_nonneg_right (show ℓ ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]
      have h2 : c₀ * L ^ 2 / 8 ≤ c₀ / ℓ * u := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hℓ0]
        nlinarith [mul_le_mul_of_nonneg_left h1 hc₀.le]
      have h3 : 3 * L + Real.log 128 + Real.log u ≤ c₀ * L ^ 2 / 8 := by
        have : ε / 5 + 5 + Real.log 128 ≤ c₀ * L / 8 := by
          rw [div_le_iff₀ hc₀] at hL2
          linarith
        nlinarith [mul_le_mul_of_nonneg_left this hL0.le, mul_nonneg (sub_nonneg.2 hL1') hlog128.le]
      linarith
    calc 16 * u * Real.exp (-(c₀ / ℓ * u)) ≤ 16 * u * Real.exp (-(3 * L + Real.log 128 + Real.log u)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by linarith)
      _ = Real.exp (-(3 * L)) / 8 := by
          rw [show -(3 * L + Real.log 128 + Real.log u) = -(3 * L) - Real.log (128 * u) by
                rw [Real.log_mul (by norm_num) hu0.ne']; ring,
            Real.exp_sub, Real.exp_log (by linarith)]
          field_simp
          ring
  ·
    obtain ⟨B, hBdef⟩ : ∃ B, B = Real.log (32 * (|A₀| + 1)) := ⟨_, rfl⟩
    rw [← hBdef] at hL3 hL4
    have hA1 : 0 < 32 * (|A₀| + 1) := by positivity
    have hB0 : 0 < B := by rw [hBdef]; exact Real.log_pos (by linarith [abs_nonneg A₀])
    have hexpB : Real.exp (-(3 * L + B)) = Real.exp (-(3 * L)) / (32 * (|A₀| + 1)) := by
      rw [show -(3 * L + B) = -(3 * L) - B by ring, Real.exp_sub, hBdef, Real.exp_log hA1]
    have hc3L : 3 + B ≤ c₃ * L / 8 := by
      rw [div_le_iff₀ hc₃] at hL3
      linarith
    have hE1 : Real.exp (-(c₃ * u / lm)) ≤ Real.exp (-(3 * L + B)) := by
      apply Real.exp_le_exp.2
      have h1 : lm * L ^ 2 / 8 ≤ u := by
        nlinarith [hkey, mul_le_mul_of_nonneg_right (show lm ≤ ℓm + 800 * L by linarith) (sq_nonneg L)]
      have h2 : c₃ * L ^ 2 / 8 ≤ c₃ * u / lm := by
        rw [le_div_iff₀ hlm0']
        nlinarith [mul_le_mul_of_nonneg_left h1 hc₃.le]
      have h3 : 3 * L + B ≤ c₃ * L ^ 2 / 8 := by
        nlinarith [mul_le_mul_of_nonneg_left hc3L hL0.le, mul_nonneg (sub_nonneg.2 hL1') hB0.le]
      linarith
    have hE2 : Real.exp (-Real.sqrt (c₃ * u)) ≤ Real.exp (-(3 * L + B)) := by
      apply Real.exp_le_exp.2
      have h0 : c₃ * ((200 + 16 / c₃) * L ^ 3) ≤ c₃ * u := mul_le_mul_of_nonneg_left hu2 hc₃.le
      have e' : c₃ * ((200 + 16 / c₃) * L ^ 3) = 200 * c₃ * L ^ 3 + 16 * L ^ 3 := by
        field_simp
      rw [e'] at h0
      have hL23 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL1' (by norm_num)
      have h1 : (4 * L) ^ 2 ≤ c₃ * u := by nlinarith [mul_pos hc₃ (pow_pos hL0 3)]
      have h2 : 4 * L ≤ Real.sqrt (c₃ * u) := by
        have := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_sq (by linarith)] at this
      linarith
    have ht1 : 0 < |A₀| + 1 := by positivity
    have hsum : Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u)) ≤
        2 * (Real.exp (-(3 * L)) / (32 * (|A₀| + 1))) := by
      rw [← hexpB]
      linarith
    calc 2 * |A₀| * (Real.exp (-(c₃ * u / lm)) + Real.exp (-Real.sqrt (c₃ * u)))
        ≤ 2 * |A₀| * (2 * (Real.exp (-(3 * L)) / (32 * (|A₀| + 1)))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp (-(3 * L)) / 8 * (|A₀| / (|A₀| + 1)) := by
          field_simp
          ring
      _ ≤ Real.exp (-(3 * L)) / 8 * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one ht1).2 (by linarith)) (by positivity)
      _ = Real.exp (-(3 * L)) / 8 := mul_one _
  ·
    have hlog4 : Real.log 4 < 2 := by
      have e4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have := Real.log_two_lt_d9
      linarith
    have hL3' : 4 * L ≤ L ^ 3 := by
      nlinarith [mul_nonneg hL0.le (show (0 : ℝ) ≤ L ^ 2 - 4 by nlinarith)]
    have h : 3 * L + Real.log 4 ≤ 2 / 5 * u := by nlinarith
    calc Real.exp (-(2 / 5 * u)) ≤ Real.exp (-(3 * L + Real.log 4)) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp (-(3 * L)) / 4 := by
          rw [show -(3 * L + Real.log 4) = -(3 * L) - Real.log 4 by ring, Real.exp_sub,
            Real.exp_log (by norm_num)]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
