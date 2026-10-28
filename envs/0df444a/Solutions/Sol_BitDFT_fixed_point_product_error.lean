-- Prove2me | solution 1 for BitDFT.fixed_point_product_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:23:37.605959+00:00
-- url     : https://prove2.me/submissions/ad02f6c0-4fcd-4564-bfd2-942f0f4a3098

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open BitDFT

private theorem rounding_bridge_local (p : ℕ) (z : ℂ) :
    value p (roundPair p z) = IntMul.HvdH.rho p z := by
  simp only [value, roundPair, IntMul.HvdH.rho, IntMul.HvdH.rho0C, div_eq_mul_inv]
  ring

private theorem rho0_scalar_error (x : ℝ) :
    |(IntMul.HvdH.rho0 x : ℝ) - x| < 1 := by
  unfold IntMul.HvdH.rho0
  split
  · rename_i hx
    have hfloor := Int.floor_le x
    have hceil := Int.lt_floor_add_one x
    have hfloor' : (Int.floor x : ℝ) ≤ x := by exact_mod_cast hfloor
    have hceil' : x < (Int.floor x : ℝ) + 1 := by exact_mod_cast hceil
    rw [abs_lt]
    constructor <;> linarith
  · rename_i hx
    have hx' : x < 0 := lt_of_not_ge hx
    have hceil := Int.le_ceil x
    have hceil' : x ≤ (Int.ceil x : ℝ) := by exact_mod_cast hceil
    have hceil2 := Int.ceil_lt_add_one x
    have hceil2' : (Int.ceil x : ℝ) < x + 1 := by exact_mod_cast hceil2
    rw [abs_of_nonneg (sub_nonneg.mpr hceil')]
    linarith

private theorem rho0C_error (z : ℂ) :
    ‖IntMul.HvdH.rho0C z - z‖ < 2 := by
  have hre := rho0_scalar_error z.re
  have him := rho0_scalar_error z.im
  have hrepr : IntMul.HvdH.rho0C z - z =
      ((IntMul.HvdH.rho0 z.re : ℝ) - z.re : ℂ) +
        ((IntMul.HvdH.rho0 z.im : ℝ) - z.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [IntMul.HvdH.rho0C]
    · simp [IntMul.HvdH.rho0C]
  rw [hrepr]
  calc
    ‖((IntMul.HvdH.rho0 z.re : ℝ) - z.re : ℂ) +
        ((IntMul.HvdH.rho0 z.im : ℝ) - z.im : ℂ) * Complex.I‖
      ≤ ‖((IntMul.HvdH.rho0 z.re : ℝ) - z.re : ℂ)‖ +
        ‖((IntMul.HvdH.rho0 z.im : ℝ) - z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |(IntMul.HvdH.rho0 z.re : ℝ) - z.re| +
        |(IntMul.HvdH.rho0 z.im : ℝ) - z.im| := by
      congr 1
      · rw [← Complex.ofReal_sub]
        change ‖(((IntMul.HvdH.rho0 z.re : ℝ) - z.re : ℝ) : ℂ)‖ = _
        exact RCLike.norm_ofReal _
      · rw [norm_mul, ← Complex.ofReal_sub]
        change ‖(((IntMul.HvdH.rho0 z.im : ℝ) - z.im : ℝ) : ℂ)‖ * ‖Complex.I‖ = _
        have hnorm :
            ‖(((IntMul.HvdH.rho0 z.im : ℝ) - z.im : ℝ) : ℂ)‖ =
              |(IntMul.HvdH.rho0 z.im : ℝ) - z.im| := RCLike.norm_ofReal _
        rw [hnorm, Complex.norm_I, mul_one]
    _ < 2 := by linarith

theorem roundPair_ulp_error (p : ℕ) (z : ℂ) :
    ulpError p (roundPair p z) z < 2 := by
  let a : ℂ := (2 : ℂ) ^ p
  have ha0 : a ≠ 0 := by
    dsimp [a]
    exact pow_ne_zero p (by norm_num)
  have hcancel : a⁻¹ * (a * z) = z := by
    field_simp
  have hscale : IntMul.HvdH.rho p z - z =
      a⁻¹ * (IntMul.HvdH.rho0C (a * z) - a * z) := by
    rw [IntMul.HvdH.rho]
    dsimp [a]
    field_simp [ha0]
  have hnorm : ‖a⁻¹‖ = ((2 : ℝ) ^ p)⁻¹ := by
    dsimp [a]
    rw [norm_inv, norm_pow]
    simp
  rw [ulpError, rounding_bridge_local, hscale, norm_mul, hnorm]
  have hs : (2 : ℝ) ^ p ≠ 0 := by positivity
  have hcancelR : (2 : ℝ) ^ p * ((2 : ℝ) ^ p)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hs
  rw [show (2 : ℝ) ^ p * (((2 : ℝ) ^ p)⁻¹ *
      ‖IntMul.HvdH.rho0C (a * z) - a * z‖) =
      ‖IntMul.HvdH.rho0C (a * z) - a * z‖ by rw [← mul_assoc, hcancelR, one_mul]]
  exact rho0C_error (a * z)

/-- Fixed-point multiplication's numerical error: input errors add, and the
componentwise round-to-zero step contributes fewer than two ulps. -/
theorem solution (p : ℕ) (U V : ℤ × ℤ)
    (hU : inDisc p U) (hV : inDisc p V) (u v : ℂ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ulpError p (roundPair p (value p U * value p V)) (u * v) <
      ulpError p U u + ulpError p V v + 2 := by
  let a : ℂ := value p U
  let b : ℂ := value p V
  let z : ℂ := a * b
  have hUa : ‖a‖ ≤ 1 := hU
  have hVb : ‖b‖ ≤ 1 := hV
  have hmul : ‖z - u * v‖ ≤ ‖a - u‖ + ‖b - v‖ := by
    dsimp [z]
    calc
      ‖a * b - u * v‖ = ‖(a - u) * b + u * (b - v)‖ := by congr 1 <;> ring
      _ ≤ ‖(a - u) * b‖ + ‖u * (b - v)‖ := norm_add_le _ _
      _ = ‖a - u‖ * ‖b‖ + ‖u‖ * ‖b - v‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖a - u‖ + ‖b - v‖ := by nlinarith [norm_nonneg (a - u), norm_nonneg (b - v)]
  have hscale : 0 < (2 : ℝ) ^ p := by positivity
  have hround := roundPair_ulp_error p z
  have htri : ‖value p (roundPair p z) - u * v‖ ≤
      ‖value p (roundPair p z) - z‖ + ‖z - u * v‖ := by
    calc
      ‖value p (roundPair p z) - u * v‖ =
          ‖(value p (roundPair p z) - z) + (z - u * v)‖ := by congr 1 <;> ring
      _ ≤ _ := norm_add_le _ _
  dsimp [ulpError] at hround ⊢
  dsimp [a, b, z] at hmul
  rw [show roundPair p (value p U * value p V) = roundPair p z by rfl]
  calc
    (2 : ℝ) ^ p * ‖value p (roundPair p z) - u * v‖
        ≤ (2 : ℝ) ^ p * (‖value p (roundPair p z) - z‖ + ‖z - u * v‖) :=
          mul_le_mul_of_nonneg_left htri (le_of_lt hscale)
    _ = (2 : ℝ) ^ p * ‖value p (roundPair p z) - z‖ +
          (2 : ℝ) ^ p * ‖z - u * v‖ := by ring
    _ < 2 + (2 : ℝ) ^ p * (‖value p U - u‖ + ‖value p V - v‖) := by
          have hleft : (2 : ℝ) ^ p * ‖value p (roundPair p z) - z‖ < 2 := by
            simpa [z] using hround
          have hright : (2 : ℝ) ^ p * ‖z - u * v‖ ≤
              (2 : ℝ) ^ p * (‖value p U - u‖ + ‖value p V - v‖) :=
            mul_le_mul_of_nonneg_left hmul (le_of_lt hscale)
          linarith
    _ = ulpError p U u + ulpError p V v + 2 := by
          rw [ulpError, ulpError]
          ring
