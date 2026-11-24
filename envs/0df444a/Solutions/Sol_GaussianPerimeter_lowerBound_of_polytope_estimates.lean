-- Prove2me | solution 1 for GaussianPerimeter.lowerBound_of_polytope_estimates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:25:54.929962+00:00
-- url     : https://prove2.me/submissions/98cb1267-d58d-4476-a817-a9c1d17904e9

module
public import Definitions.Def_GaussianPerimeter_Definitions
public import Definitions.Def_GaussianPerimeter_Scaling
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Definitions.Def_GaussianPerimeter_LimitBound
public import Theorems.Thm_GaussianPerimeter_lintegral_le_liminf_of_eventually_le_tendsto
public import Theorems.Thm_GaussianPerimeter_tendsto_floor_sub_one_mul_scale
public import Theorems.Thm_GaussianPerimeter_tendsto_no_success
public import Theorems.Thm_GaussianPerimeter_tendsto_normalized_prefactor


set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal Topology
open GaussianPerimeter
namespace GaussianPerimeter
theorem _root_.solution {a b W : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : 0 ≤ W)
    {s : ℕ → ℝ} {radial p q : ℕ → ℝ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hspos : ∀ᶠ n in atTop, 0 < s n)
    (hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        s n * (a * Real.sqrt (Real.sqrt n)) * Real.exp (-a ^ 4 / 4))
    (hRadial : ∀ w, Tendsto (fun n => radial n w) atTop
      (𝓝 (Real.exp (-w ^ 2) / Real.sqrt Real.pi)))
    (hRadialNonneg : ∀ n w, 0 ≤ radial n w)
    (hCap : ∀ w, Tendsto (fun n => q n w / s n) atTop (𝓝 (Real.exp (a ^ 2 * w))))
    (hCapLe : ∀ w, ∀ᶠ n in atTop, p n w ≤ q n w)
    (hMeas : ∀ n, Measurable (fun w => ENNReal.ofReal
      (radial n w * (1 - p n w) ^ (⌊b / s n⌋₊ - 1))))
    (hPolytope : ∀ᶠ n in atTop,
      ENNReal.ofReal ((⌊b / s n⌋₊ : ℝ) *
        (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi))) *
        (∫⁻ w in Set.Ioc (-W) W, ENNReal.ofReal
          (radial n w * (1 - p n w) ^ (⌊b / s n⌋₊ - 1))) ≤ Γ (n + 1)) :
    ENNReal.ofReal ((b * a * Real.exp (-a ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ w in (-W)..W, Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w)))) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by
  let N (n : ℕ) := ⌊b / s n⌋₊
  let coeff (n : ℕ) := (N n : ℝ) *
    (Real.exp (-(a * Real.sqrt (Real.sqrt n)) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) /
      (n + 1 : ℝ) ^ (1 / 4 : ℝ)
  let C := b * a * Real.exp (-a ^ 4 / 4)
  let f (n : ℕ) (w : ℝ) :=
    ENNReal.ofReal (coeff n) * ENNReal.ofReal (radial n w * (1 - p n w) ^ (N n - 1))
  let g (n : ℕ) (w : ℝ) :=
    ENNReal.ofReal (coeff n) * ENNReal.ofReal (radial n w * (1 - q n w) ^ (N n - 1))
  let F (w : ℝ) := Real.exp (-w ^ 2 - b * Real.exp (a ^ 2 * w))
  let μ := volume.restrict (Set.Ioc (-W) W)
  have hcoeff : Tendsto coeff atTop (𝓝 C) :=
    tendsto_normalized_prefactor hs hspos hb.le hscale
  have hF : Continuous F := by fun_prop
  have hFatou : (∫⁻ w, ENNReal.ofReal (C / Real.sqrt Real.pi * F w) ∂μ) ≤
      liminf (fun n => ∫⁻ w, f n w ∂μ) atTop := by
    apply lintegral_le_liminf_of_eventually_le_tendsto (g := g)
    · intro n
      exact measurable_const.mul (hMeas n)
    · intro w
      have hq := (hs.mul (hCap w)).congr' (by
        filter_upwards [hspos] with n hn
        exact mul_div_cancel₀ _ hn.ne')
      rw [zero_mul] at hq
      have hqpos : ∀ᶠ n in atTop, 0 < q n w := by
        filter_upwards [hspos, (hCap w).eventually_const_lt (Real.exp_pos _)] with n hn hr
        exact (div_pos_iff_of_pos_right hn).mp hr
      have hcount := ((tendsto_floor_sub_one_mul_scale hs hspos hb.le).mul (hCap w)).congr' (by
        filter_upwards [hspos] with n hn
        rw [mul_assoc, mul_div_cancel₀ _ hn.ne'])
      have hpow := tendsto_no_success hq hqpos hcount
      have hLimit : C * (Real.exp (-w ^ 2) / Real.sqrt Real.pi *
          Real.exp (-(b * Real.exp (a ^ 2 * w)))) = C / Real.sqrt Real.pi * F w := by
        dsimp [F]
        rw [sub_eq_add_neg, Real.exp_add]
        ring
      have h := ENNReal.tendsto_ofReal (hcoeff.mul ((hRadial w).mul hpow))
      rw [hLimit] at h
      apply h.congr
      intro n
      exact ENNReal.ofReal_mul (by dsimp [coeff, N]; positivity)
    · intro w
      have hq := (hs.mul (hCap w)).congr' (by
        filter_upwards [hspos] with n hn
        exact mul_div_cancel₀ _ hn.ne')
      rw [zero_mul] at hq
      filter_upwards [hCapLe w, hq.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)]
        with n hle hq1
      dsimp [f, g]
      apply mul_le_mul_right
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (hRadialNonneg n w)
      exact pow_le_pow_left₀ (sub_nonneg.mpr hq1.le) (sub_le_sub_left hle 1) _
  have hIntegral :
      ENNReal.ofReal (C / Real.sqrt Real.pi * (∫ w in (-W)..W, F w)) =
        ∫⁻ w, ENNReal.ofReal (C / Real.sqrt Real.pi * F w) ∂μ := by
    have hle : -W ≤ W := by linarith
    have hCont : Continuous (fun w => C / Real.sqrt Real.pi * F w) :=
      continuous_const.mul hF
    have hInt : Integrable (fun w => C / Real.sqrt Real.pi * F w) μ :=
      (hCont.intervalIntegrable (-W) W).1
    rw [intervalIntegral.integral_of_le hle, ← integral_const_mul,
      ofReal_integral_eq_lintegral_ofReal hInt]
    exact Eventually.of_forall fun w => by dsimp [C, F]; positivity
  rw [← liminf_nat_add _ 1]
  refine hIntegral.le.trans (hFatou.trans (liminf_le_liminf ?_))
  filter_upwards [hPolytope] with n hn
  dsimp [f]
  rw [lintegral_const_mul _ (hMeas n)]
  dsimp [coeff]
  have hden : 0 < (n + 1 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  rw [ENNReal.ofReal_div_of_pos hden, Nat.cast_add, Nat.cast_one]
  simpa only [N, μ, div_eq_mul_inv, mul_right_comm] using
    mul_le_mul_left hn (ENNReal.ofReal ((n + 1 : ℝ) ^ (1 / 4 : ℝ)))⁻¹
end GaussianPerimeter
