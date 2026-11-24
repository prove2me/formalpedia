-- Prove2me | solution 2 for GaussianPerimeter.tendsto_quarter_power_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:08.297435+00:00
-- url     : https://prove2.me/submissions/487ff26d-20e4-425f-bdfb-672bf981109d

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
namespace GaussianPerimeter
theorem _root_.solution :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (n + 1 : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hInv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop 1
  have hRatio : Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1) by
      simpa only [sub_zero] using tendsto_const_nhds.sub hInv).congr
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    field_simp
    ring
  have hPower := (Real.continuousAt_rpow_const 1 (1 / 4 : ℝ)
    (Or.inl one_ne_zero)).tendsto.comp hRatio
  rw [Real.one_rpow] at hPower
  apply hPower.congr
  intro n
  exact Real.div_rpow (Nat.cast_nonneg _) (by positivity) _
end GaussianPerimeter
