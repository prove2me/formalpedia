-- Prove2me | solution 1 for GaussianPerimeter.lintegral_gaussian_radial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:35.659091+00:00
-- url     : https://prove2.me/submissions/f55fec20-4236-4a66-9046-ef25472ba9f8

module
public import Definitions.Def_GaussianPerimeter_Radial
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Definitions.Def_GaussianPerimeter_RadialIntegration
public import Theorems.Thm_GaussianPerimeter_lintegral_norm_euclidean
public import Theorems.Thm_GaussianPerimeter_integral_radialKernel
public import Theorems.Thm_GaussianPerimeter_integral_radialKernel_pos

section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace GaussianPerimeter
local notation "Euc" => fun n => EuclideanSpace ℝ (Fin n)
private theorem radial_normalizing_constant (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) *
      (Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)) *
      (2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2) *
      (∫ r, radialKernel (n + 1) r) = 1 := by
  let d : ℝ := (n + 1 : ℕ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hπ := Real.pi_pos
  rw [integral_radialKernel _ (Nat.succ_pos _), ← Real.rpow_natCast,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hπ.le]
  change d * (Real.pi ^ (1 / 2 * d) / Real.Gamma (d / 2 + 1)) *
    (2 * Real.pi) ^ (-d / 2) *
    ((1 / 2 : ℝ) ^ (-d / 2) * (1 / 2) * Real.Gamma (d / 2)) = 1
  rw [Real.Gamma_add_one (by positivity), Real.div_rpow (by norm_num) (by norm_num),
    Real.one_rpow, Real.mul_rpow (by norm_num) hπ.le]
  rw [show -d / 2 = -(1 / 2 * d) by ring, Real.rpow_neg hπ.le]
  have hG := Real.Gamma_pos_of_pos (show 0 < d / 2 by positivity)
  have hp := Real.rpow_pos_of_pos hπ (1 / 2 * d)
  have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-(1 / 2 * d))
  field_simp
end GaussianPerimeter
end
end

set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory Set
open scoped ENNReal Topology
open GaussianPerimeter
local notation "Euc" => fun n => EuclideanSpace ℝ (Fin n)
namespace GaussianPerimeter
theorem _root_.solution (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) :
    (∫⁻ x : Euc (n + 1), ENNReal.ofReal
      ((2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / 2) * f ‖x‖)) =
      ∫⁻ r : ℝ, ENNReal.ofReal (radialDensity (n + 1) r * f r) := by
  let c : ℝ := (2 * Real.pi) ^ (-((n + 1 : ℕ) : ℝ) / 2)
  let v : ℝ := Real.sqrt Real.pi ^ (n + 1) / Real.Gamma (((n + 1 : ℕ) : ℝ) / 2 + 1)
  let C : ℝ := ((n + 1 : ℕ) : ℝ) * v * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hv : 0 ≤ v := by
    unfold v
    exact div_nonneg (by positivity) (Real.Gamma_pos_of_pos (by positivity)).le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hInv : C = (∫ r, radialKernel (n + 1) r)⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀
      (integral_radialKernel_pos (n + 1) (Nat.succ_pos _)).ne').mp
    exact radial_normalizing_constant n
  have hMeas : Measurable (fun r : ℝ => ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r)) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_const.mul (by fun_prop)).mul hf)
  have hPower : Measurable (fun r : ℝ => r ^ n) := by fun_prop
  have hMeas' : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ n * Real.exp (-r ^ 2 / 2) * f r)) :=
    ENNReal.continuous_ofReal.measurable.comp ((hPower.mul (by fun_prop)).mul hf)
  rw [lintegral_norm_euclidean n hMeas, EuclideanSpace.volume_ball, Fintype.card_fin]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal v *
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
      ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r)) = _
  have hPointwise : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r ^ n) *
      ENNReal.ofReal (c * Real.exp (-r ^ 2 / 2) * f r) =
        ENNReal.ofReal c * ENNReal.ofReal (r ^ n * Real.exp (-r ^ 2 / 2) * f r) := by
    intro r hr
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.out.le _), ← ENNReal.ofReal_mul hc]
    congr 1
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hPointwise, lintegral_const_mul _ hMeas',
    ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) hv)]
  change ENNReal.ofReal C * _ = _
  rw [← lintegral_const_mul _ hMeas']
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro r
  by_cases hr : r ∈ Ioi (0 : ℝ)
  · rw [indicator_of_mem hr, ← ENNReal.ofReal_mul hC]
    congr 1
    have hrKernel : radialKernel (n + 1) r = r ^ n * Real.exp (-r ^ 2 / 2) := by
      simp [radialKernel, hr]
    rw [hInv, radialDensity, hrKernel, div_eq_mul_inv]
    ring
  · simp [radialDensity, radialKernel, hr]
end GaussianPerimeter
