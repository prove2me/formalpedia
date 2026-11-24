-- Prove2me | solution 1 for GaussianPerimeter.gaussianPrefactor_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:30.750927+00:00
-- url     : https://prove2.me/submissions/f460e293-6e35-465d-b0c6-851e0d848b44

module
public import Definitions.Def_GaussianPerimeter_ExpBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Definitions.Def_GaussianPerimeter_Prefactor
public import Theorems.Thm_GaussianPerimeter_expLower_le_exp


set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution :
    (0.938393 : ℝ) ≤
      (2387 / 1000 : ℝ) * (6131 / 5000) *
        Real.exp (-((6131 / 5000 : ℝ) ^ 4) / 4) / Real.sqrt Real.pi := by
  let q : ℚ := -((6131 / 5000 : ℚ) ^ 4) / 4
  have hq : (q : ℝ) = -((6131 / 5000 : ℝ) ^ 4) / 4 := by
    norm_num [q]
  have hcert : (56825898 / 100000000 : ℚ) ≤ expLower q := by decide +kernel
  have hexp : (56825898 / 100000000 : ℝ) ≤ Real.exp (q : ℝ) := by
    have hcast : (((56825898 / 100000000 : ℚ)) : ℝ) ≤ (expLower q : ℝ) :=
      Rat.cast_le.mpr hcert
    simpa using hcast.trans (expLower_le_exp q)
  have hsqrt : Real.sqrt Real.pi ≤ (1772454 / 1000000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · linarith [Real.pi_lt_d6]
  rw [← hq]
  calc
    (0.938393 : ℝ) ≤ (2387 / 1000 : ℝ) * (6131 / 5000) *
        (56825898 / 100000000) / (1772454 / 1000000) := by norm_num
    _ ≤ _ :=
      (div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.2 Real.pi_pos) hsqrt).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (Real.sqrt_nonneg _))
end GaussianPerimeter
