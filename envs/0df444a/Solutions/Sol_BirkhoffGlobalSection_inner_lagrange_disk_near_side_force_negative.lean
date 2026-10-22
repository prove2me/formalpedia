-- Prove2me | solution 1 for BirkhoffGlobalSection.inner_lagrange_disk_near_side_force_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T06:55:14.075985+00:00
-- url     : https://prove2.me/submissions/a4361e48-d30a-4197-b387-a53c9952ec74

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
    (x y : ℝ) (hx : -μ < x)
    (hr : (x + μ) ^ 2 + y ^ 2 < (L 0 + μ) ^ 2) :
    x - (1 - μ) * (x + μ) / Real.sqrt ((x + μ) ^ 2 + y ^ 2) ^ 3 -
      μ * (x - 1 + μ) / Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) ^ 3 < 0 := by
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
  set u := x + μ with hudef
  have hu0 : 0 < u := by linarith
  have hpos : 0 < (x + μ) ^ 2 + y ^ 2 := by positivity
  set ρ := Real.sqrt ((x + μ) ^ 2 + y ^ 2) with hρ
  have hρ0 : 0 < ρ := Real.sqrt_pos.2 hpos
  have hρ2 : ρ ^ 2 = u ^ 2 + y ^ 2 := Real.sq_sqrt hpos.le
  have hρd : ρ < d := by rw [hρ, Real.sqrt_lt' hd0]; exact hr
  have hρ1 : ρ < 1 := by linarith
  have huρ : u ≤ ρ := by
    have := Real.abs_le_sqrt (show (x + μ) ^ 2 ≤ (x + μ) ^ 2 + y ^ 2 by linarith [sq_nonneg y])
    linarith [le_abs_self (x + μ)]
  have hr2e : (x - 1 + μ) ^ 2 + y ^ 2 = 1 + ρ ^ 2 - 2 * u := by rw [hρ2]; ring
  have hs2pos : 0 < (x - 1 + μ) ^ 2 + y ^ 2 := by
    rw [hr2e]; have := sq_pos_of_pos (show 0 < 1 - ρ by linarith); nlinarith [this, huρ]
  set σ := Real.sqrt ((x - 1 + μ) ^ 2 + y ^ 2) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.2 hs2pos
  have hσ2 : σ ^ 2 = 1 + ρ ^ 2 - 2 * u := by rw [hσ, Real.sq_sqrt hs2pos.le, hr2e]
  -- the coefficient of `u`
  set B := 1 - (1 - μ) / ρ ^ 3 with hB
  have hBneg : B < 0 := by
    have e : (1 - μ) / d ^ 3 = 1 - μ / d + μ / (d * (1 - d) ^ 2) := by
      have h5 : (1 - μ) / d ^ 2 = d - μ + μ / (1 - d) ^ 2 := by linarith
      have h6 : (1 - μ) / d ^ 3 = ((1 - μ) / d ^ 2) / d := by rw [div_div]; ring_nf
      rw [h6, h5]; field_simp
    have h3 : μ / d < μ / (d * (1 - d) ^ 2) := by
      apply div_lt_div_of_pos_left hμ0 (by positivity)
      have hq : (1 - d) ^ 2 < 1 := by
        have := mul_pos hd0 (show 0 < 2 - d by linarith); linarith [show (1 - d) ^ 2 = 1 - d * (2 - d) by ring]
      calc d * (1 - d) ^ 2 < d * 1 := mul_lt_mul_of_pos_left hq hd0
        _ = d := mul_one d
    have h1 : (1 - μ) / d ^ 3 < (1 - μ) / ρ ^ 3 :=
      div_lt_div_of_pos_left (by linarith) (by positivity) (pow_lt_pow_left₀ hρd hρ0.le (by norm_num))
    rw [hB]; linarith
  -- a convex function of the distance to the second primary
  set H : ℝ → ℝ := fun t => ((1 + ρ ^ 2) / 2 * B - μ) + (-B / 2) * t ^ (2 : ℤ) +
    (μ * (1 - ρ ^ 2) / 2) * t ^ (-3 : ℤ) + (μ / 2) * t ^ (-1 : ℤ) with hH
  have hc3 : 0 ≤ μ * (1 - ρ ^ 2) / 2 := by
    have : 0 < 1 - ρ ^ 2 := by
      have := mul_pos (show 0 < 1 - ρ by linarith) (show 0 < 1 + ρ by linarith); linarith [show 1 - ρ ^ 2 = (1 - ρ) * (1 + ρ) by ring]
    positivity
  have hHconv : ConvexOn ℝ (Set.Ioi 0) H := by
    have c2 := (convexOn_zpow (𝕜 := ℝ) 2).smul (show 0 ≤ -B / 2 by linarith)
    have c3 := (convexOn_zpow (𝕜 := ℝ) (-3)).smul
      (show 0 ≤ μ * (1 - ρ ^ 2) / 2 from hc3)
    have c1 := (convexOn_zpow (𝕜 := ℝ) (-1)).smul (show 0 ≤ μ / 2 by positivity)
    have := ((c2.add c3).add c1).add_const ((1 + ρ ^ 2) / 2 * B - μ)
    refine this.congr ?_
    intro t _; simp only [hH, smul_eq_mul, Pi.add_apply]; ring
  have hHval : ∀ t : ℝ, 0 < t → H t =
      (1 + ρ ^ 2 - t ^ 2) / 2 * B - μ + μ * (1 - ρ ^ 2 + t ^ 2) / (2 * t ^ 3) := by
    intro t ht
    simp only [hH, zpow_neg, zpow_ofNat]
    field_simp; ring
  -- the endpoints
  have ht0 : 0 < 1 - ρ := by linarith
  set t1 := Real.sqrt (1 + ρ ^ 2) with ht1
  have ht1pos : 1 < t1 := by rw [ht1, Real.lt_sqrt (by norm_num)]; have := sq_pos_of_pos hρ0; linarith
  have ht1sq : t1 ^ 2 = 1 + ρ ^ 2 := Real.sq_sqrt (by positivity)
  have hσlo : 1 - ρ ≤ σ := by
    have : (1 - ρ) ^ 2 ≤ σ ^ 2 := by rw [hσ2]; linarith [show (1 - ρ) ^ 2 = 1 + ρ ^ 2 - 2 * ρ by ring]
    exact (pow_le_pow_iff_left₀ ht0.le hσ0.le (by norm_num : (2:ℕ) ≠ 0)).1 this
  have hσhi : σ ≤ t1 := by
    have : σ ^ 2 ≤ t1 ^ 2 := by rw [hσ2, ht1sq]; linarith
    exact (pow_le_pow_iff_left₀ hσ0.le (by linarith) (by norm_num : (2:ℕ) ≠ 0)).1 this
  have hmax := hHconv.le_max_of_mem_Icc (show (0:ℝ) < 1 - ρ from ht0)
    (show (0:ℝ) < t1 by linarith) ⟨hσlo, hσhi⟩
  have hHt1 : H t1 < 0 := by
    rw [hHval t1 (by linarith), ht1sq]
    have : μ * (1 - ρ ^ 2 + (1 + ρ ^ 2)) / (2 * t1 ^ 3) = μ / t1 ^ 3 := by
      field_simp; ring
    rw [this, show (1 + ρ ^ 2 - (1 + ρ ^ 2)) / 2 * B = 0 by ring, zero_sub]
    have : μ / t1 ^ 3 < μ := by
      rw [div_lt_iff₀ (by positivity)]
      have : 1 < t1 ^ 3 := one_lt_pow₀ ht1pos (by norm_num)
      have := mul_lt_mul_of_pos_left this hμ0
      linarith
    linarith
  have hHt0 : H (1 - ρ) < 0 := by
    rw [hHval _ ht0]
    have e : (1 + ρ ^ 2 - (1 - ρ) ^ 2) / 2 * B - μ + μ * (1 - ρ ^ 2 + (1 - ρ) ^ 2) / (2 * (1 - ρ) ^ 3)
        = ρ - μ - (1 - μ) / ρ ^ 2 + μ / (1 - ρ) ^ 2 := by
      rw [hB]; field_simp; ring
    rw [e]
    have h1 : (1 - μ) / d ^ 2 < (1 - μ) / ρ ^ 2 :=
      div_lt_div_of_pos_left (by linarith) (by positivity) (pow_lt_pow_left₀ hρd hρ0.le (by norm_num))
    have h2 : μ / (1 - ρ) ^ 2 < μ / (1 - d) ^ 2 :=
      div_lt_div_of_pos_left hμ0 (by positivity) (pow_lt_pow_left₀ (by linarith) h1d.le (by norm_num))
    linarith
  -- identify the horizontal force with `H σ`
  have hgoal : x - (1 - μ) * (x + μ) / ρ ^ 3 - μ * (x - 1 + μ) / σ ^ 3 = H σ := by
    rw [hHval σ hσ0]
    have hu' : u = (1 + ρ ^ 2 - σ ^ 2) / 2 := by rw [hσ2]; ring
    rw [hB]
    have hx' : x = u - μ := by rw [hudef]; ring
    rw [hx', hu']
    field_simp
    ring
  show x - (1 - μ) * (x + μ) / ρ ^ 3 - μ * (x - 1 + μ) / σ ^ 3 < 0
  rw [hgoal]
  exact lt_of_le_of_lt hmax (max_lt hHt0 hHt1)
