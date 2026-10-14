-- Prove2me | solution 1 for DbarRegularity.cauchyRiemann_lp_plane
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:54:26.827366+00:00
-- url     : https://prove2.me/submissions/92bcb757-d677-4ea0-9625-f9ee3842d1e1

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_truncatedSingularIntegral_lp
import Theorems.Thm_DbarRegularity_inv_sq_kernel_conditions
import Theorems.Thm_DbarRegularity_integral_dbar_mul_inv_sq_eq
import Theorems.Thm_DbarRegularity_tendsto_circle_average_div
import Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
import Theorems.Thm_DbarRegularity_setIntegral_mul_eq_integral_indicator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic



namespace DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal

theorem cauchyRiemann_lp_plane_aux (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin 2) → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1) +
            Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume := by
  set K : EuclideanSpace ℝ (Fin 2) → ℂ :=
    fun y => 1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2 with hKdef
  obtain ⟨B, hKm, hK1, hK2, hK3⟩ := inv_sq_kernel_conditions K (fun y => rfl)
  obtain ⟨A, hA, -⟩ := truncatedSingularIntegral_lp K B hKm hK1 hK2 hK3 p hp
  refine ⟨1 + A / NNReal.pi, fun f hf hfc => ?_⟩
  set P : ℝ≥0∞ := ENNReal.ofReal p with hP
  have hP1 : 1 ≤ P := ENNReal.one_le_ofReal.2 hp.le
  set f1 : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => fderiv ℝ f x (EuclideanSpace.single 0 1)
    with hf1
  set f2 : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => fderiv ℝ f x (EuclideanSpace.single 1 1)
    with hf2
  set G : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => f1 x + Complex.I * f2 x with hG
  set D : EuclideanSpace ℝ (Fin 2) → ℂ := fun x => f1 x - Complex.I * f2 x with hD
  have hc1 : Continuous f1 := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hc2 : Continuous f2 := (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcs1 : HasCompactSupport f1 := hfc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single 0 1)
  have hcs2 : HasCompactSupport f2 := hfc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single 1 1)
  have hGc : Continuous G := hc1.add (continuous_const.mul hc2)
  have hDc : Continuous D := hc1.sub (continuous_const.mul hc2)
  have hcs2' : HasCompactSupport ((fun _ => Complex.I) * f2) := hcs2.mul_left
  have hGs : HasCompactSupport G := by
    have h := hcs1.add hcs2'
    exact h
  have hGm : MemLp G P volume := hGc.memLp_of_hasCompactSupport hGs
  -- the truncations of `G` converge pointwise to `-π D`
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hlim : ∀ x, Tendsto (fun n : ℕ => ∫ y in {y : EuclideanSpace ℝ (Fin 2) |
      1 / ((n : ℝ) + 1) ≤ ‖y‖}, G (x - y) * K y) atTop (𝓝 (-(Real.pi : ℂ) * D x)) := by
    intro x
    have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Eventually.of_forall hpos⟩
    have := (tendsto_circle_average_div f hf x).comp hε
    refine this.congr fun n => ?_
    exact (integral_dbar_mul_inv_sq_eq f hf hfc x _ (hpos n)).symm
  have hTm : ∀ n : ℕ, AEStronglyMeasurable (fun x => ∫ y in {y : EuclideanSpace ℝ (Fin 2) |
      1 / ((n : ℝ) + 1) ≤ ‖y‖}, G (x - y) * K y) volume := by
    intro n
    have := aestronglyMeasurable_integral_mul_sub
      ({y : EuclideanSpace ℝ (Fin 2) | 1 / ((n : ℝ) + 1) ≤ ‖y‖}.indicator K) G
      (hKm.indicator (measurableSet_le measurable_const measurable_norm)) hGc.aestronglyMeasurable
    refine this.congr (Eventually.of_forall fun x => ?_)
    exact (setIntegral_mul_eq_integral_indicator K G _ x).symm
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := P) hTm _ (Eventually.of_forall hlim)
  have hDπ : (NNReal.pi : ℝ≥0∞) * eLpNorm D P volume ≤ A * eLpNorm G P volume := by
    have h1 : eLpNorm (fun x => -(Real.pi : ℂ) * D x) P volume =
        (NNReal.pi : ℝ≥0∞) * eLpNorm D P volume := by
      have : (fun x => -(Real.pi : ℂ) * D x) = (-(Real.pi : ℂ)) • D := rfl
      rw [this, eLpNorm_const_smul]
      congr 1
      rw [← ofReal_norm_eq_enorm, norm_neg, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    rw [← h1]
    refine hfat.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
    exact hA _ (hpos n) G hGm
  have hDle : eLpNorm D P volume ≤ (A / NNReal.pi : ℝ≥0) * eLpNorm G P volume := by
    have hpi0 : (NNReal.pi : ℝ≥0∞) ≠ 0 := by simp [NNReal.pi_ne_zero]
    have hpit : (NNReal.pi : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    calc eLpNorm D P volume
        = (NNReal.pi : ℝ≥0∞)⁻¹ * ((NNReal.pi : ℝ≥0∞) * eLpNorm D P volume) :=
          (ENNReal.inv_mul_cancel_left hpi0 hpit).symm
      _ ≤ (NNReal.pi : ℝ≥0∞)⁻¹ * (A * eLpNorm G P volume) := mul_le_mul' le_rfl hDπ
      _ = (A / NNReal.pi : ℝ≥0) * eLpNorm G P volume := by
          rw [ENNReal.coe_div NNReal.pi_ne_zero, div_eq_mul_inv]
          ring
  -- `2 f₁ = G + D`, `2 i f₂ = G - D`
  have h1 : 2 * eLpNorm f1 P volume ≤ eLpNorm G P volume + eLpNorm D P volume := by
    have : (2 : ℂ) • f1 = G + D := by
      funext x; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hG, hD]; ring
    have h := eLpNorm_add_le (μ := volume) hGc.aestronglyMeasurable hDc.aestronglyMeasurable hP1
    rw [← this, eLpNorm_const_smul] at h
    have h2 : ‖(2 : ℂ)‖ₑ = 2 := by
      rw [← ofReal_norm_eq_enorm]; simp
    rwa [h2] at h
  have h2 : 2 * eLpNorm f2 P volume ≤ eLpNorm G P volume + eLpNorm D P volume := by
    have : (2 * Complex.I) • f2 = G - D := by
      funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hG, hD]; ring
    have h := eLpNorm_sub_le (μ := volume) hGc.aestronglyMeasurable hDc.aestronglyMeasurable hP1
    rw [← this, eLpNorm_const_smul] at h
    have h2 : ‖(2 * Complex.I : ℂ)‖ₑ = 2 := by
      rw [← ofReal_norm_eq_enorm]; simp
    rwa [h2] at h
  have hsum : eLpNorm f1 P volume + eLpNorm f2 P volume ≤
      eLpNorm G P volume + eLpNorm D P volume := by
    have h3 : 2 * (eLpNorm f1 P volume + eLpNorm f2 P volume) ≤
        2 * (eLpNorm G P volume + eLpNorm D P volume) := by
      rw [mul_add, two_mul (eLpNorm G P volume + eLpNorm D P volume)]
      exact add_le_add h1 h2
    exact (ENNReal.mul_le_mul_iff_right two_ne_zero ENNReal.ofNat_ne_top).1 h3
  calc eLpNorm f1 P volume + eLpNorm f2 P volume
      ≤ eLpNorm G P volume + eLpNorm D P volume := hsum
    _ ≤ eLpNorm G P volume + (A / NNReal.pi : ℝ≥0) * eLpNorm G P volume :=
        add_le_add le_rfl hDle
    _ = ((1 + A / NNReal.pi : ℝ≥0) : ℝ≥0∞) * eLpNorm G P volume := by
        rw [ENNReal.coe_add, ENNReal.coe_one, add_mul, one_mul]

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin 2) → ℂ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1)) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume
        ≤ A * eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single 0 1) +
            Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)) (ENNReal.ofReal p) volume :=
  cauchyRiemann_lp_plane_aux p hp
