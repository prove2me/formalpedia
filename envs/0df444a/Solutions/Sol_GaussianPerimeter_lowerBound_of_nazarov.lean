-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_of_nazarov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:26:43.19585+00:00
-- url     : https://prove2.me/submissions/00a9b9b7-97e2-44f9-9ac2-ec2ad05fdc37

module
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Definitions.Def_GaussianPerimeter_CapAsymptotics
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Definitions.Def_GaussianPerimeter_NazarovLimit
public import Theorems.Thm_GaussianPerimeter_tendsto_capScale_zero
public import Theorems.Thm_GaussianPerimeter_capScale_mul_density
public import Theorems.Thm_GaussianPerimeter_shiftedRadialDensity_measurable
public import Theorems.Thm_GaussianPerimeter_shiftedCapTail_measurable
public import Theorems.Thm_GaussianPerimeter_capScale_pos
public import Theorems.Thm_GaussianPerimeter_eventually_capTail_le_capMajorant
public import Theorems.Thm_GaussianPerimeter_lowerBound_of_polytope_estimates
public import Theorems.Thm_GaussianPerimeter_radialDensity_nonneg
public import Theorems.Thm_GaussianPerimeter_tendsto_capMajorant_div_capScale
public import Theorems.Thm_GaussianPerimeter_tendsto_radialDensity_shift


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a b W : ℝ} (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W)
    (hPolytope : ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / capScale a n⌋₊ : ℝ) *
        (Real.exp (-(capRho a n ^ 2) / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (shiftedRadialDensity n w * (1 - shiftedCapTail a n w) ^ (⌊b / capScale a n⌋₊ - 1)))
        ≤ Γ (n + 1)) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by
  apply lowerBound_of_polytope_estimates ha hb hW (s := capScale a)
    (radial := shiftedRadialDensity) (p := shiftedCapTail a) (q := capMajorant a)
  · exact tendsto_capScale_zero ha
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact capScale_pos ha hn
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact capScale_mul_density ha hn
  · intro w
    apply (tendsto_radialDensity_shift w).congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    unfold shiftedRadialDensity
    rw [Nat.cast_sub hn, Nat.cast_one]
  · intro n w
    exact radialDensity_nonneg _ _
  · intro w
    exact tendsto_capMajorant_div_capScale a w ha
  · intro w
    filter_upwards [eventually_ge_atTop (2 : ℕ), eventually_capTail_le_capMajorant a w ha]
      with n hn hCap
    simpa only [shiftedCapTail, if_pos hn] using hCap
  · intro n
    exact ENNReal.continuous_ofReal.measurable.comp
      ((shiftedRadialDensity_measurable n).mul
        ((measurable_const.sub (shiftedCapTail_measurable a n)).pow_const _))
  · exact hPolytope
end GaussianPerimeter
