-- Prove2me | solution 1 for GaussianPerimeter.tendsto_quarter_power_ratio
-- status  : ACCEPTED   (prove)
-- author  : @bbchallenge_user
-- created : 2026-11-24T11:17:48.616503+00:00
-- url     : https://prove2.me/submissions/261996d3-550e-4eef-9ea4-1234b9607e35

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter

theorem solution :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (n + 1 : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 1) := by
  have h : (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (n + 1 : ℝ) ^ (1 / 4 : ℝ)) =
      fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) ^ (1 / 4 : ℝ) := by
    funext n
    rw [Real.div_rpow (by positivity) (by positivity)]
  rw [h]
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop 1
  simpa using h2.rpow_const (p := (1 / 4 : ℝ)) (Or.inl one_ne_zero)
