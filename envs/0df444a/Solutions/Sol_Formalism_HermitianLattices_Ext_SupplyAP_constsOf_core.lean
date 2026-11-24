-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.constsOf_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.41656+00:00
-- url     : https://prove2.me/submissions/70152aac-96c2-4021-ae5c-fb8eed068b82

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution (n : ℕ) (c c₀ C R l T M : ℝ) (hn : 1 ≤ n) (hc : 0 < c) (hc₀ : 0 < c₀)
    (hC : 0 ≤ C)
    (hA1 : 4 * (n : ℝ) + 4 * (24 / c₀) ≤ R) (hA2 : (n : ℝ) + 2 * C / c₀ ≤ c * R) (hl : 1 ≤ l)
    (hT : R ^ 2 * l ^ 2 ≤ T) (hM : 0 < M) (hMl : M ≤ Real.exp l) :
    4 ≤ T ∧ M ≤ Real.exp (c * Real.sqrt T) ∧
      3 * (Real.exp (T / 2) * T) ≤
        c₀ * Real.exp T / M ^ n - C * Real.exp T * Real.exp (-c * Real.sqrt T) := by
  set a : ℝ := (n : ℝ) with ha
  have ha1 : 1 ≤ a := by rw [ha]; exact_mod_cast hn
  set D : ℝ := 24 / c₀ with hD
  set B : ℝ := 2 * C / c₀ with hB
  have hD0 : 0 < D := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hcD : c₀ * D = 24 := by rw [hD]; field_simp
  have hcB : c₀ * B = 2 * C := by rw [hB]; field_simp
  have hA4 : 4 ≤ R := by linarith
  have hAl : R ≤ R * l := by nlinarith
  have hAl1 : 1 ≤ R * l := by linarith
  have hAl2 : R * l ≤ R ^ 2 * l ^ 2 := by nlinarith
  have hTA : R * l ≤ T := le_trans hAl2 hT
  have hs : R * l ≤ Real.sqrt T := by
    apply Real.le_sqrt_of_sq_le
    calc (R * l) ^ 2 = R ^ 2 * l ^ 2 := by ring
      _ ≤ T := hT
  have hcs : c * (R * l) ≤ c * Real.sqrt T := mul_le_mul_of_nonneg_left hs hc.le
  have hcAl : (a + B) * l ≤ c * (R * l) := by
    have := mul_le_mul_of_nonneg_right hA2 (by linarith : (0 : ℝ) ≤ l)
    linarith
  have hBl : B ≤ B * l := by nlinarith
  have hal : l ≤ a * l := by nlinarith
  have hM2 : M ^ n ≤ Real.exp (a * l) := by
    have : Real.exp (a * l) = Real.exp l ^ n := by
      rw [ha, Real.exp_nat_mul]
    rw [this]
    exact pow_le_pow_left₀ hM.le hMl n
  have hE : 0 < Real.exp T := Real.exp_pos T
  refine ⟨by linarith, ?_, ?_⟩
  · refine le_trans hMl (Real.exp_le_exp.mpr ?_)
    nlinarith
  ·
    have hT4 : T ≤ 4 * Real.exp (T / 4) := by
      have := Real.add_one_le_exp (T / 4)
      linarith
    have hDle : D ≤ T / 4 - a * l := by
      have h1 : (4 * a + 4 * D) * l ≤ R * l :=
        mul_le_mul_of_nonneg_right hA1 (by linarith : (0 : ℝ) ≤ l)
      have h2 : D ≤ D * l := by nlinarith
      linarith
    have hDexp : D ≤ Real.exp (T / 4 - a * l) := by
      have := Real.add_one_le_exp (T / 4 - a * l)
      linarith
    have hprod : Real.exp (T / 4 - a * l) * (Real.exp (T / 2) * Real.exp (T / 4) * Real.exp (a * l))
        = Real.exp T := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1; ring
    set Q : ℝ := Real.exp (T / 2) * Real.exp (T / 4) * Real.exp (a * l) with hQ
    have hQ0 : 0 < Q := by positivity
    have P1 : 3 * (Real.exp (T / 2) * T) * M ^ n ≤ c₀ / 2 * Real.exp T := by
      have h1 : 3 * (Real.exp (T / 2) * T) * M ^ n ≤ 12 * Q := by
        have hx : Real.exp (T / 2) * T ≤ Real.exp (T / 2) * (4 * Real.exp (T / 4)) :=
          mul_le_mul_of_nonneg_left hT4 (Real.exp_pos _).le
        have hb : Real.exp (T / 2) * T * M ^ n
            ≤ Real.exp (T / 2) * (4 * Real.exp (T / 4)) * Real.exp (a * l) :=
          mul_le_mul hx hM2 (by positivity) (by positivity)
        rw [hQ]; nlinarith
      have h2 : 12 * Q ≤ c₀ / 2 * Real.exp T := by
        rw [← hprod]
        have : D * Q ≤ Real.exp (T / 4 - a * l) * Q := mul_le_mul_of_nonneg_right hDexp hQ0.le
        have h3 : c₀ / 2 * (D * Q) ≤ c₀ / 2 * (Real.exp (T / 4 - a * l) * Q) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        have h4 : c₀ / 2 * (D * Q) = 12 * Q := by
          calc c₀ / 2 * (D * Q) = (c₀ * D) / 2 * Q := by ring
            _ = 12 * Q := by rw [hcD]; ring
        linarith
      exact le_trans h1 h2

    have hexp2 : Real.exp (-c * Real.sqrt T) * Real.exp (a * l) ≤ Real.exp (-B) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hBexp : B * Real.exp (-B) ≤ 1 := by
      have h1 : B ≤ Real.exp B := by
        have := Real.add_one_le_exp B
        linarith
      calc B * Real.exp (-B) ≤ Real.exp B * Real.exp (-B) :=
            mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hCexp : C * Real.exp (-B) ≤ c₀ / 2 := by
      have : C = c₀ / 2 * B := by linarith
      rw [this]
      calc c₀ / 2 * B * Real.exp (-B) = c₀ / 2 * (B * Real.exp (-B)) := by ring
        _ ≤ c₀ / 2 * 1 := mul_le_mul_of_nonneg_left hBexp (by positivity)
        _ = c₀ / 2 := by ring
    have P2 : C * Real.exp T * Real.exp (-c * Real.sqrt T) * M ^ n ≤ c₀ / 2 * Real.exp T := by
      have h1 : Real.exp (-c * Real.sqrt T) * M ^ n ≤ Real.exp (-B) :=
        le_trans (mul_le_mul_of_nonneg_left hM2 (Real.exp_pos _).le) hexp2
      have h2 : C * (Real.exp (-c * Real.sqrt T) * M ^ n) ≤ c₀ / 2 :=
        le_trans (mul_le_mul_of_nonneg_left h1 hC) hCexp
      calc C * Real.exp T * Real.exp (-c * Real.sqrt T) * M ^ n
          = Real.exp T * (C * (Real.exp (-c * Real.sqrt T) * M ^ n)) := by ring
        _ ≤ Real.exp T * (c₀ / 2) := mul_le_mul_of_nonneg_left h2 hE.le
        _ = c₀ / 2 * Real.exp T := by ring
    have hM2pos : 0 < M ^ n := by positivity
    rw [le_sub_iff_add_le, le_div_iff₀ hM2pos]
    linarith
end Formalism.HermitianLattices.Ext.SupplyAP
