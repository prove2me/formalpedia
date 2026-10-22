-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_ball_radial_force_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T21:43:26.079847+00:00
-- url     : https://prove2.me/submissions/89d84454-add2-4f76-be90-577b47cd8a27

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open BirkhoffGlobalSection

lemma bern_B (r w : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    0 ≤ -8*r^5*w^4 + 20*r^5*w^3 - 18*r^5*w^2 + 7*r^5*w - r^5 + 16*r^4*w^4 - 60*r^4*w^3 + 72*r^4*w^2 - 35*r^4*w + 6*r^4 - 8*r^3*w^4 + 60*r^3*w^3 - 108*r^3*w^2 + 70*r^3*w - 15*r^3 - 20*r^2*w^3 + 76*r^2*w^2 - 75*r^2*w + 22*r^2 - 18*r*w^2 + 39*r*w - 18*r - 6*w + 6 := by
  have hp : 0 ≤ 1 - r := by linarith
  have hq : 0 ≤ 1 - w := by linarith
  generalize hpd : 1 - r = p at hp
  generalize hqd : 1 - w = q at hq
  have e : -8*r^5*w^4 + 20*r^5*w^3 - 18*r^5*w^2 + 7*r^5*w - r^5 + 16*r^4*w^4 - 60*r^4*w^3 + 72*r^4*w^2 - 35*r^4*w + 6*r^4 - 8*r^3*w^4 + 60*r^3*w^3 - 108*r^3*w^2 + 70*r^3*w - 15*r^3 - 20*r^2*w^3 + 76*r^2*w^2 - 75*r^2*w + 22*r^2 - 18*r*w^2 + 39*r*w - 18*r - 6*w + 6 = (6:ℝ) * (r^0 * p^5 * w^0 * q^4) + (18:ℝ) * (r^0 * p^5 * w^1 * q^3) + (18:ℝ) * (r^0 * p^5 * w^2 * q^2) + (6:ℝ) * (r^0 * p^5 * w^3 * q^1) + (12:ℝ) * (r^1 * p^4 * w^0 * q^4) + (57:ℝ) * (r^1 * p^4 * w^1 * q^3) + (81:ℝ) * (r^1 * p^4 * w^2 * q^2) + (39:ℝ) * (r^1 * p^4 * w^3 * q^1) + (3:ℝ) * (r^1 * p^4 * w^4 * q^0) + (10:ℝ) * (r^2 * p^3 * w^0 * q^4) + (61:ℝ) * (r^2 * p^3 * w^1 * q^3) + (127:ℝ) * (r^2 * p^3 * w^2 * q^2) + (91:ℝ) * (r^2 * p^3 * w^3 * q^1) + (15:ℝ) * (r^2 * p^3 * w^4 * q^0) + (3:ℝ) * (r^3 * p^2 * w^0 * q^4) + (31:ℝ) * (r^3 * p^2 * w^1 * q^3) + (87:ℝ) * (r^3 * p^2 * w^2 * q^2) + (93:ℝ) * (r^3 * p^2 * w^3 * q^1) + (26:ℝ) * (r^3 * p^2 * w^4 * q^0) + (6:ℝ) * (r^4 * p^1 * w^1 * q^3) + (30:ℝ) * (r^4 * p^1 * w^2 * q^2) + (42:ℝ) * (r^4 * p^1 * w^3 * q^1) + (18:ℝ) * (r^4 * p^1 * w^4 * q^0) + (4:ℝ) * (r^5 * p^0 * w^2 * q^2) + (8:ℝ) * (r^5 * p^0 * w^3 * q^1) + (4:ℝ) * (r^5 * p^0 * w^4 * q^0) := by
    rw [← hpd, ← hqd]; ring
  rw [e]
  linarith [mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 0) (pow_nonneg hp 5)) (pow_nonneg hw 0)) (pow_nonneg hq 4), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 0) (pow_nonneg hp 5)) (pow_nonneg hw 1)) (pow_nonneg hq 3), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 0) (pow_nonneg hp 5)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 0) (pow_nonneg hp 5)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 1) (pow_nonneg hp 4)) (pow_nonneg hw 0)) (pow_nonneg hq 4), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 1) (pow_nonneg hp 4)) (pow_nonneg hw 1)) (pow_nonneg hq 3), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 1) (pow_nonneg hp 4)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 1) (pow_nonneg hp 4)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 1) (pow_nonneg hp 4)) (pow_nonneg hw 4)) (pow_nonneg hq 0), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hp 3)) (pow_nonneg hw 0)) (pow_nonneg hq 4), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hp 3)) (pow_nonneg hw 1)) (pow_nonneg hq 3), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hp 3)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hp 3)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hp 3)) (pow_nonneg hw 4)) (pow_nonneg hq 0), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hp 2)) (pow_nonneg hw 0)) (pow_nonneg hq 4), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hp 2)) (pow_nonneg hw 1)) (pow_nonneg hq 3), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hp 2)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hp 2)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hp 2)) (pow_nonneg hw 4)) (pow_nonneg hq 0), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 4) (pow_nonneg hp 1)) (pow_nonneg hw 1)) (pow_nonneg hq 3), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 4) (pow_nonneg hp 1)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 4) (pow_nonneg hp 1)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 4) (pow_nonneg hp 1)) (pow_nonneg hw 4)) (pow_nonneg hq 0), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 5) (pow_nonneg hp 0)) (pow_nonneg hw 2)) (pow_nonneg hq 2), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 5) (pow_nonneg hp 0)) (pow_nonneg hw 3)) (pow_nonneg hq 1), mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hr 5) (pow_nonneg hp 0)) (pow_nonneg hw 4)) (pow_nonneg hq 0)]


lemma radial_angle_gap (ρ κ t : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκ0 : -1 ≤ κ) (hκ1 : κ ≤ 1) (ht : 0 ≤ t) (ht2 : t ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1) :
    0 ≤ t ^ 3 - (1 - κ) * (1 - ρ) ^ 2 * t ^ 3 + (ρ - κ) * (1 - ρ) ^ 2 := by
  have hlo : 1 - ρ ≤ t := by nlinarith
  have hhi : t ≤ 1 + ρ := by nlinarith
  have hκ' : κ = (ρ ^ 2 + 1 - t ^ 2) / (2 * ρ) := by field_simp; linarith
  set w := (t - (1 - ρ)) / (2 * ρ) with hw
  have hw0 : 0 ≤ w := div_nonneg (by linarith) (by linarith)
  have hw1 : w ≤ 1 := by rw [hw, div_le_one (by linarith)]; linarith
  have ht' : t = 1 - ρ + 2 * ρ * w := by rw [hw]; field_simp; ring
  have e : t ^ 3 - (1 - κ) * (1 - ρ) ^ 2 * t ^ 3 + (ρ - κ) * (1 - ρ) ^ 2 =
      2 * ρ * w * (-8*ρ^5*w^4 + 20*ρ^5*w^3 - 18*ρ^5*w^2 + 7*ρ^5*w - ρ^5 + 16*ρ^4*w^4 - 60*ρ^4*w^3 + 72*ρ^4*w^2 - 35*ρ^4*w + 6*ρ^4 - 8*ρ^3*w^4 + 60*ρ^3*w^3 - 108*ρ^3*w^2 + 70*ρ^3*w - 15*ρ^3 - 20*ρ^2*w^3 + 76*ρ^2*w^2 - 75*ρ^2*w + 22*ρ^2 - 18*ρ*w^2 + 39*ρ*w - 18*ρ - 6*w + 6) := by
    rw [hκ']
    clear_value w
    subst ht'
    field_simp
    ring
  rw [e]
  have := bern_B ρ w hρ0.le hρ1.le hw0 hw1
  positivity

theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (ρ κ : ℝ) (hρ0 : 0 < ρ) (hρd : ρ < L 0 + μ)
    (hκ0 : -1 ≤ κ) (hκ1 : κ ≤ 1) :
    ρ - μ * κ - (1 - μ) / ρ ^ 2 -
      μ * (ρ - κ) / Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 3 < 0 := by
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
  -- the force on the axis is increasing in the radius
  have hu : ρ - μ - (1 - μ) / ρ ^ 2 + μ / (1 - ρ) ^ 2 < 0 := by
    have h1 : (1 - μ) / d ^ 2 < (1 - μ) / ρ ^ 2 :=
      div_lt_div_of_pos_left (by linarith) (by positivity) (by nlinarith)
    have h2 : μ / (1 - ρ) ^ 2 < μ / (1 - d) ^ 2 :=
      div_lt_div_of_pos_left hμ0 (by positivity) (by nlinarith)
    linarith
  -- off-axis directions have smaller radial force
  have hQ : 0 < ρ ^ 2 - 2 * ρ * κ + 1 := by nlinarith
  have ht0 : 0 < Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) := Real.sqrt_pos.2 hQ
  have ht2 : Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) ^ 2 = ρ ^ 2 - 2 * ρ * κ + 1 := Real.sq_sqrt hQ.le
  generalize Real.sqrt (ρ ^ 2 - 2 * ρ * κ + 1) = t at ht0 ht2 ⊢
  have hg := radial_angle_gap ρ κ t hρ0 (by linarith) hκ0 hκ1 ht0.le ht2
  have h1ρ : 0 < 1 - ρ := by linarith
  have hgap : 0 ≤ 1 / (1 - ρ) ^ 2 - 1 + κ + (ρ - κ) / t ^ 3 := by
    have e : 1 / (1 - ρ) ^ 2 - 1 + κ + (ρ - κ) / t ^ 3 =
        (t ^ 3 - (1 - κ) * (1 - ρ) ^ 2 * t ^ 3 + (ρ - κ) * (1 - ρ) ^ 2) / ((1 - ρ) ^ 2 * t ^ 3) := by
      field_simp; ring
    rw [e]; positivity
  have hmul := mul_nonneg hμ0.le hgap
  have e2 : μ * (1 / (1 - ρ) ^ 2 - 1 + κ + (ρ - κ) / t ^ 3) =
      μ / (1 - ρ) ^ 2 - μ + μ * κ + μ * (ρ - κ) / t ^ 3 := by ring
  rw [e2] at hmul
  linarith
