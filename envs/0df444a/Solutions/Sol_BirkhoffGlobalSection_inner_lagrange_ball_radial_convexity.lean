-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_ball_radial_convexity
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T21:55:58.181986+00:00
-- url     : https://prove2.me/submissions/fc75f032-1c64-4cf3-979a-29637c7b5161

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open BirkhoffGlobalSection

lemma negative_region_distance_bound (ρ κ t : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (ht : 0 < t) (ht2 : t ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1)
    (hneg : 3 * (ρ - κ) ^ 2 < t ^ 2) :
    4 / 5 * (1 - ρ ^ 2) ≤ t := by
  by_contra hcon
  push_neg at hcon
  have hrel : 2 * ρ * (ρ - κ) = t ^ 2 + ρ ^ 2 - 1 := by linarith
  have h1 : 3 * (t ^ 2 + ρ ^ 2 - 1) ^ 2 < 4 * ρ ^ 2 * t ^ 2 := by
    rw [← hrel]
    have h := mul_lt_mul_of_pos_left hneg (show (0:ℝ) < 4 * ρ ^ 2 by positivity)
    have e : 3 * (2 * ρ * (ρ - κ)) ^ 2 = 4 * ρ ^ 2 * (3 * (ρ - κ) ^ 2) := by ring
    rw [e]; linarith
  have hA0 : 0 < 1 - ρ ^ 2 := by nlinarith
  have ht2' : t ^ 2 < 16 / 25 * (1 - ρ ^ 2) ^ 2 := by nlinarith
  have hA : (1 - ρ ^ 2) * (9 / 25 + 16 / 25 * ρ ^ 2) < 1 - ρ ^ 2 - t ^ 2 := by nlinarith
  have hB : 2 * ρ * t < 8 / 5 * ρ * (1 - ρ ^ 2) := by nlinarith
  have hpoly : (8 / 5 * ρ) ^ 2 ≤ 3 * (9 / 25 + 16 / 25 * ρ ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (ρ ^ 2 - 9 / 16), sq_nonneg (ρ - 3 / 4)]
  have hpos : 0 < (1 - ρ ^ 2) * (9 / 25 + 16 / 25 * ρ ^ 2) := by positivity
  have h2 : 4 * ρ ^ 2 * t ^ 2 < 3 * (1 - ρ ^ 2 - t ^ 2) ^ 2 := by
    have e1 : 4 * ρ ^ 2 * t ^ 2 = (2 * ρ * t) ^ 2 := by ring
    have e2 : (2 * ρ * t) ^ 2 < (8 / 5 * ρ * (1 - ρ ^ 2)) ^ 2 := by
      have : 0 ≤ 2 * ρ * t := by positivity
      nlinarith
    have e3 : (8 / 5 * ρ * (1 - ρ ^ 2)) ^ 2 ≤ 3 * ((1 - ρ ^ 2) * (9 / 25 + 16 / 25 * ρ ^ 2)) ^ 2 := by
      have : (8 / 5 * ρ * (1 - ρ ^ 2)) ^ 2 = (8 / 5 * ρ) ^ 2 * (1 - ρ ^ 2) ^ 2 := by ring
      rw [this]
      have : 3 * ((1 - ρ ^ 2) * (9 / 25 + 16 / 25 * ρ ^ 2)) ^ 2 =
          3 * (9 / 25 + 16 / 25 * ρ ^ 2) ^ 2 * (1 - ρ ^ 2) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hpoly (by positivity)
    have e4 : 3 * ((1 - ρ ^ 2) * (9 / 25 + 16 / 25 * ρ ^ 2)) ^ 2 < 3 * (1 - ρ ^ 2 - t ^ 2) ^ 2 := by
      nlinarith
    linarith
  have e : (t ^ 2 + ρ ^ 2 - 1) ^ 2 = (1 - ρ ^ 2 - t ^ 2) ^ 2 := by ring
  rw [e] at h1
  linarith

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (ρ κ : ℝ) (hρ0 : 0 < ρ) (hρd : ρ ≤ L 0 + μ)
    (hκ0 : -1 ≤ κ) (hκ1 : κ ≤ 1) :
    1 ≤ 1 + 2 * (1 - μ) / ρ ^ 3 +
      μ * (3 * (ρ - κ) ^ 2 - (ρ ^ 2 - 2 * ρ * κ + 1)) /
        Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 5 := by
  obtain ⟨hfree, hcrit, hlo, hhi, hL1⟩ := hL
  have hd0 : 0 < L 0 + μ := by linarith
  have hd1 : L 0 + μ < 1 := by linarith
  -- the collinear force balance at the inner Lagrange point
  have hpart := jacobi_partial_position_one μ L hfree
  have hzero : partialDerivative (jacobiHamiltonian μ) L 0 = 0 := by
    unfold partialDerivative; rw [hcrit.2]; rfl
  have hmom := (jacobi_critical_momentum μ L hcrit).2
  rw [hzero, hmom, hL1] at hpart
  have hs1 : Real.sqrt ((L 0 + μ) ^ 2 + (0:ℝ) ^ 2) = L 0 + μ := by
    rw [zero_pow two_ne_zero, add_zero]; exact Real.sqrt_sq hd0.le
  have hs2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + (0:ℝ) ^ 2) = 1 - (L 0 + μ) := by
    rw [zero_pow two_ne_zero, add_zero, show (L 0 - 1 + μ) ^ 2 = (1 - (L 0 + μ)) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [hs1, hs2] at hpart
  set d := L 0 + μ with hd
  have hL0 : L 0 = d - μ := by rw [hd]; ring
  rw [hL0] at hpart
  have h1d : 0 < 1 - d := by linarith
  have hbal : d - μ - (1 - μ) / d ^ 2 + μ / (1 - d) ^ 2 = 0 := by
    have e1 : (1 - μ) * d / d ^ 3 = (1 - μ) / d ^ 2 := by field_simp
    have e2 : μ * (d - μ - 1 + μ) / (1 - d) ^ 3 = -(μ / (1 - d) ^ 2) := by
      field_simp; ring
    rw [e1, e2] at hpart
    linarith
  clear_value d
  clear hpart hs1 hs2 hzero hmom hL0 hd hfree hcrit hlo hhi hL1
  -- the mass ratio is small compared with the Hill radius
  have hμd : μ * d ^ 3 ≤ 128 / 125 * (1 - μ) * (1 - d ^ 2) ^ 3 := by
    have hid : μ * d ^ 3 * (2 - d) = (1 - d) ^ 2 * (1 - μ - d ^ 3) := by
      have hd0' : d ≠ 0 := hd0.ne'
      have h1d' : 1 - d ≠ 0 := h1d.ne'
      have e : μ * d ^ 3 * (2 - d) - (1 - d) ^ 2 * (1 - μ - d ^ 3) =
          d ^ 2 * (1 - d) ^ 2 * (d - μ - (1 - μ) / d ^ 2 + μ / (1 - d) ^ 2) := by
        field_simp; ring
      rw [hbal, mul_zero] at e
      linarith
    have hstep : μ * d ^ 3 * (2 - d) ≤ (1 - μ) * (1 - d) ^ 3 * (1 + d + d ^ 2) := by
      rw [hid]
      have : 1 - μ - d ^ 3 ≤ (1 - μ) * (1 - d ^ 3) := by nlinarith [pow_pos hd0 3]
      have e : (1 - μ) * (1 - d) ^ 3 * (1 + d + d ^ 2) = (1 - d) ^ 2 * ((1 - μ) * (1 - d ^ 3)) := by
        ring
      rw [e]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hpoly : 1 + d + d ^ 2 ≤ 128 / 125 * (2 - d) * (1 + d) ^ 3 := by
      nlinarith [mul_pos hd0 h1d, pow_pos hd0 2, pow_pos hd0 3, mul_pos (pow_pos hd0 2) h1d]
    have h2d : 0 < 2 - d := by linarith
    have : μ * d ^ 3 * (2 - d) ≤ 128 / 125 * (1 - μ) * (1 - d ^ 2) ^ 3 * (2 - d) := by
      calc μ * d ^ 3 * (2 - d) ≤ (1 - μ) * (1 - d) ^ 3 * (1 + d + d ^ 2) := hstep
        _ ≤ (1 - μ) * (1 - d) ^ 3 * (128 / 125 * (2 - d) * (1 + d) ^ 3) :=
          mul_le_mul_of_nonneg_left hpoly (mul_nonneg (by linarith) (pow_nonneg h1d.le 3))
        _ = 128 / 125 * (1 - μ) * (1 - d ^ 2) ^ 3 * (2 - d) := by ring
    exact le_of_mul_le_mul_right this h2d
  have hρ1 : ρ < 1 := by linarith
  have hμρ : μ * ρ ^ 3 ≤ 128 / 125 * (1 - μ) * (1 - ρ ^ 2) ^ 3 := by
    have h1 : ρ ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hρ0.le hρd 3
    have h2 : (1 - d ^ 2) ^ 3 ≤ (1 - ρ ^ 2) ^ 3 :=
      pow_le_pow_left₀ (by nlinarith) (by nlinarith) 3
    have hμ1' : 0 < 1 - μ := by linarith
    have a1 := mul_le_mul_of_nonneg_left h1 hμ0.le
    have a2 := mul_le_mul_of_nonneg_left h2 (show (0:ℝ) ≤ 128 / 125 * (1 - μ) by positivity)
    linarith
  -- reduce to the sign of the tidal term
  have hQ : 0 < ρ ^ 2 - 2 * ρ * κ + 1 := by
    have h1 : 0 ≤ 2 * ρ * (1 - κ) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 < (1 - ρ) ^ 2 := by have : 0 < 1 - ρ := by linarith
                                    positivity
    nlinarith
  have ht0 : 0 < Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) := Real.sqrt_pos.2 hQ
  have ht2 : Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1 := Real.sq_sqrt hQ.le
  generalize Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) = t at ht0 ht2 ⊢
  rw [← ht2]
  have hc0 : 0 ≤ 2 * (1 - μ) / ρ ^ 3 := div_nonneg (by linarith) (by positivity)
  rcases le_or_gt (t ^ 2) (3 * (ρ - κ) ^ 2) with hnn | hneg
  · have : 0 ≤ μ * (3 * (ρ - κ) ^ 2 - t ^ 2) / t ^ 5 :=
      div_nonneg (mul_nonneg hμ0.le (by linarith)) (by positivity)
    linarith
  · have htb := negative_region_distance_bound ρ κ t hρ0 hρ1 ht0 ht2 hneg
    have hA0 : 0 < 1 - ρ ^ 2 := by nlinarith
    -- the tidal term is at least `-μ / t^3`
    have hlow : -(μ / t ^ 3) ≤ μ * (3 * (ρ - κ) ^ 2 - t ^ 2) / t ^ 5 := by
      have e : -(μ / t ^ 3) = μ * (-(t ^ 2)) / t ^ 5 := by field_simp
      rw [e]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [sq_nonneg (ρ - κ)]
    have hm : μ / t ^ 3 ≤ μ / (4 / 5 * (1 - ρ ^ 2)) ^ 3 :=
      div_le_div_of_nonneg_left hμ0.le (by positivity) (pow_le_pow_left₀ (by positivity) htb 3)
    have hfin : μ / (4 / 5 * (1 - ρ ^ 2)) ^ 3 ≤ 2 * (1 - μ) / ρ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
