-- Prove2me | solution 1 for GaussianPerimeter.tendsto_floor_sub_one_mul_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:20.605549+00:00
-- url     : https://prove2.me/submissions/fdc2ae16-3235-4104-bfcf-1b9fa5205d5f

module
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Topology.Order.LiminfLimsup
public import Definitions.Def_GaussianPerimeter_Basic

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {s : ℕ → ℝ} {b : ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < s n) (hb : 0 ≤ b) :
    Tendsto (fun n => ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n) atTop (𝓝 b) := by
  have hlo : ∀ᶠ n in atTop,
      b - 2 * s n ≤ ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n := by
    filter_upwards [hpos] with n hn
    have hFloor := (div_lt_iff₀ hn).mp (Nat.lt_floor_add_one (b / s n))
    have hNat : ⌊b / s n⌋₊ ≤ (⌊b / s n⌋₊ - 1) + 1 := by omega
    have hCast : (⌊b / s n⌋₊ : ℝ) ≤ ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hNat
    have h := mul_le_mul_of_nonneg_right hCast hn.le
    linarith
  have hhi : ∀ᶠ n in atTop, ((⌊b / s n⌋₊ - 1 : ℕ) : ℝ) * s n ≤ b := by
    filter_upwards [hpos] with n hn
    apply (le_div_iff₀ hn).mp
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le (div_nonneg hb hn.le))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub (hs.const_mul 2)) tendsto_const_nhds hlo hhi
end GaussianPerimeter
