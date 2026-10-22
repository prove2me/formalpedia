-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_disk_vertical_tidal_factor
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T06:45:27.919668+00:00
-- url     : https://prove2.me/submissions/663fcef1-ded4-45ec-bd38-f1886e286a98

import Definitions.Def_BirkhoffGlobalSection
import Theorems.Thm_BirkhoffGlobalSection_jacobi_partial_position_one
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic

open BirkhoffGlobalSection

set_option maxHeartbeats 2000000 in
theorem solution (μ : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1) (L : Phase) (hL : IsInnerLagrangePoint μ L)
    (x y : ℝ) (hpos : 0 < (x + μ) ^ 2 + y ^ 2)
    (hr : (x + μ) ^ 2 + y ^ 2 < (L 0 + μ) ^ 2) :
    1 < (1 - μ) / Real.sqrt ((x + μ) ^ 2 + y ^ 2) ^ 3 +
      μ / Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) ^ 3 := by
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
  -- radii
  set ρ := Real.sqrt ((x + μ) ^ 2 + y ^ 2) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = (x + μ) ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
  have hρd : ρ < d := by
    rw [hρ, Real.sqrt_lt' hd0]; exact hr
  have habs : |x + μ| ≤ ρ := Real.abs_le_sqrt (by nlinarith [sq_nonneg y])
  have hu : -(x + μ) ≤ ρ := by linarith [neg_abs_le (x + μ)]
  have hu2 : x + μ ≤ ρ := by linarith [le_abs_self (x + μ)]
  have hr2e : (x - 1 + μ) ^ 2 + y ^ 2 = ρ ^ 2 - 2 * (x + μ) + 1 := by rw [hρ2]; ring
  have hs2pos : 0 < (x - 1 + μ) ^ 2 + y ^ 2 := by
    rw [hr2e]; nlinarith [sq_nonneg (1 - ρ)]
  set σ := Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hs2pos
  have hσ2 : σ ^ 2 = (x - 1 + μ) ^ 2 + y ^ 2 := Real.sq_sqrt hs2pos.le
  have hσρ : σ ≤ 1 + ρ := by
    have : σ ^ 2 ≤ (1 + ρ) ^ 2 := by rw [hσ2, hr2e]; nlinarith
    exact (pow_le_pow_iff_left₀ hσ0.le (by linarith) (by norm_num : (2:ℕ) ≠ 0)).1 this
  -- monotone comparison with the circle through the Lagrange point
  have h1 : (1 - μ) / d ^ 3 < (1 - μ) / ρ ^ 3 :=
    div_lt_div_of_pos_left (by linarith) (by positivity) (pow_lt_pow_left₀ hρd hρ0.le (by norm_num))
  have h2 : μ / (1 + d) ^ 3 ≤ μ / σ ^ 3 :=
    div_le_div_of_nonneg_left hμ0.le (by positivity) (pow_le_pow_left₀ hσ0.le (by linarith) 3)
  have hkey : 1 < (1 - μ) / d ^ 3 + μ / (1 + d) ^ 3 := by
    have e : (1 - μ) / d ^ 3 = 1 - μ / d + μ / (d * (1 - d) ^ 2) := by
      have h5 : (1 - μ) / d ^ 2 = d - μ + μ / (1 - d) ^ 2 := by linarith
      have h6 : (1 - μ) / d ^ 3 = ((1 - μ) / d ^ 2) / d := by
        rw [div_div]; ring_nf
      rw [h6, h5]
      field_simp
    rw [e]
    have h3 : μ / d < μ / (d * (1 - d) ^ 2) := by
      apply div_lt_div_of_pos_left hμ0 (by positivity)
      have hq : (1 - d) ^ 2 < 1 := by nlinarith
      calc d * (1 - d) ^ 2 < d * 1 := mul_lt_mul_of_pos_left hq hd0
        _ = d := mul_one d
    have h4 : 0 < μ / (1 + d) ^ 3 := by positivity
    linarith
  linarith [h1, h2, hkey]
