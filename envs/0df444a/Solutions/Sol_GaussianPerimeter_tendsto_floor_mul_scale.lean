-- Prove2me | solution 1 for GaussianPerimeter.tendsto_floor_mul_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:11:18.680724+00:00
-- url     : https://prove2.me/submissions/28fa8a1e-6e69-487a-ac36-b8dd6caee21c

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
    Tendsto (fun n => (⌊b / s n⌋₊ : ℝ) * s n) atTop (𝓝 b) := by
  have hlo : ∀ᶠ n in atTop, b - s n ≤ (⌊b / s n⌋₊ : ℝ) * s n := by
    filter_upwards [hpos] with n hn
    have h := (div_lt_iff₀ hn).mp (Nat.lt_floor_add_one (b / s n))
    linarith
  have hhi : ∀ᶠ n in atTop, (⌊b / s n⌋₊ : ℝ) * s n ≤ b := by
    filter_upwards [hpos] with n hn
    exact (le_div_iff₀ hn).mp (Nat.floor_le (div_nonneg hb hn.le))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub hs)
    tendsto_const_nhds hlo hhi
end GaussianPerimeter
