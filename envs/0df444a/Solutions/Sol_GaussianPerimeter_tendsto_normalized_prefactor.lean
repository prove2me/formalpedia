-- Prove2me | solution 1 for GaussianPerimeter.tendsto_normalized_prefactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:23:53.875488+00:00
-- url     : https://prove2.me/submissions/c68dfe81-27c9-4b47-af01-49f4608e6eb2

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
public import Theorems.Thm_GaussianPerimeter_tendsto_quarter_power_ratio
public import Theorems.Thm_GaussianPerimeter_fourthRoot_eq_rpow
public import Theorems.Thm_GaussianPerimeter_tendsto_floor_mul_scale


set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {s : ℕ → ℝ} {a b : ℝ}
    (hs : Tendsto s atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b)
    (hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        s n * (a * Real.sqrt (Real.sqrt n)) * Real.exp (-a ^ 4 / 4)) :
    Tendsto (fun n : ℕ => (⌊b / s n⌋₊ : ℝ) *
      (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
        (n + 1 : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 (b * a * Real.exp (-a ^ 4 / 4))) := by
  have h := (((tendsto_floor_mul_scale hs hpos hb).mul tendsto_quarter_power_ratio).mul_const a)
    |>.mul_const (Real.exp (-a ^ 4 / 4))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [hscale] with n hn
  rw [hn, fourthRoot_eq_rpow _ (Nat.cast_nonneg _)]
  ring
end GaussianPerimeter
