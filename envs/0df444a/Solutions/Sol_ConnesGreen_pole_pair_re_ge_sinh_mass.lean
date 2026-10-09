-- Prove2me | solution 1 for ConnesGreen.pole_pair_re_ge_sinh_mass
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T02:44:44.05141+00:00
-- url     : https://prove2.me/submissions/b0d15933-4212-4c68-8879-85406f27dfaa

import Definitions.Def_ConnesGreen_arithmetic_mass_budget
import Theorems.Thm_ConnesRZ_mellinHat_conv_starInv
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex MeasureTheory ConnesRZ ConnesRZFrontier Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
open WeilDefect WeilDefect.ConnesNative ConnesGreen
namespace ConnesRZFoundation
lemma integrable_mellinHat {g : ℝ → ℂ} (hg : IsTest g) (z : ℂ) :
    Integrable (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
  have hc : Continuous (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) :=
    hg.1.continuous.mul (by fun_prop)
  exact hc.integrable_of_hasCompactSupport hg.2.mul_right

end ConnesRZFoundation
namespace ConnesGreen
theorem pole_pair_eq_twice_re (g : ℝ → ℂ) (hg : IsTest g) :
    mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1 =
      ((2 * (mellinHat g 0 * starRingEnd ℂ (mellinHat g 1)).re : ℝ) : ℂ) := by
  rw [ConnesRZ.mellinHat_conv_starInv g hg,
    ConnesRZ.mellinHat_conv_starInv g hg]
  simp only [map_zero, map_one, sub_zero, sub_self]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring


theorem norm_integral_mul_sq_le_L2_product {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f w : α → ℂ) (hf : MemLp f 2 μ) (hw : MemLp w 2 μ) :
    ‖∫ x, f x * w x ∂μ‖ ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖w x‖ ^ 2 ∂μ) := by
  let u := hf.norm.toLp (fun x => ‖f x‖)
  let v := hw.norm.toLp (fun x => ‖w x‖)
  have hu : u =ᵐ[μ] fun x => ‖f x‖ := hf.norm.coeFn_toLp
  have hv : v =ᵐ[μ] fun x => ‖w x‖ := hw.norm.coeFn_toLp
  have he : inner ℝ u v = ∫ x, ‖f x‖ * ‖w x‖ ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu, hv] with x hux hvx
    simp only [hux, hvx, Real.inner_apply]
  have heu : ‖u‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp only [hx, Real.inner_apply, pow_two]
  have hev : ‖v‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [hx, Real.inner_apply, pow_two]
  have hn : ‖∫ x, f x * w x ∂μ‖ ≤ inner ℝ u v := by
    rw [he]
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => f x * w x)
  have hcs := hn.trans (real_inner_le_norm u v)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hcs 2
  simpa only [mul_pow, heu, hev] using hs

theorem integral_sinh_half_sq (T : ℝ) (hT : 0 ≤ T) :
    (∫ s in Icc (-T) T, Real.sinh (s / 2) ^ 2) = Real.sinh T - T := by
  have he (s : ℝ) : Real.sinh (s / 2) ^ 2 = (Real.cosh s - 1) / 2 := by
    have h := Real.cosh_two_mul (s / 2)
    rw [show 2 * (s / 2) = s by ring] at h
    nlinarith [Real.cosh_sq_sub_sinh_sq (s / 2)]
  have hd (s : ℝ) : HasDerivAt (fun s => (Real.sinh s - s) / 2)
      (Real.sinh (s / 2) ^ 2) s := by
    rw [he]
    simpa using ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)).div_const 2
  have hc : Continuous (fun s : ℝ => Real.sinh (s / 2) ^ 2) := by fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable (-T) T)
  rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hi
  rw [integral_Icc_eq_integral_Ioc, hi, Real.sinh_neg]
  ring

theorem pole_pair_re_eq_sum_sub_difference_sq (g : ℝ → ℂ) (hg : IsTest g) :
    (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re =
      (‖mellinHat g 0 + mellinHat g 1‖ ^ 2 -
        ‖mellinHat g 0 - mellinHat g 1‖ ^ 2) / 2 := by
  rw [pole_pair_eq_twice_re g hg]
  simp only [Complex.ofReal_re]
  have h := Complex.normSq_add (mellinHat g 0) (mellinHat g 1)
  have k := Complex.normSq_sub (mellinHat g 0) (mellinHat g 1)
  simp only [Complex.normSq_eq_norm_sq] at h k
  nlinarith

theorem pole_pair_re_ge_negative_difference_sq (g : ℝ → ℂ) (hg : IsTest g) :
    -(‖mellinHat g 0 - mellinHat g 1‖ ^ 2) / 2 ≤
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re := by
  rw [pole_pair_re_eq_sum_sub_difference_sq g hg]
  nlinarith [sq_nonneg ‖mellinHat g 0 + mellinHat g 1‖]

theorem mellin_pole_difference_eq_sinh (g : ℝ → ℂ) (hg : IsTest g) :
    mellinHat g 0 - mellinHat g 1 =
      -2 * (∫ s : ℝ, g s * (Real.sinh (s / 2) : ℂ)) := by
  rw [mellinHat, mellinHat, ← integral_sub
    (ConnesRZFoundation.integrable_mellinHat hg 0)
    (ConnesRZFoundation.integrable_mellinHat hg 1), ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun s => by
    dsimp only
    have h0 : (((0 : ℂ) - 1/2) * s) = ((-s/2 : ℝ) : ℂ) := by push_cast; ring
    have h1 : (((1 : ℂ) - 1/2) * s) = ((s/2 : ℝ) : ℂ) := by push_cast; ring
    rw [h0, h1, ← Complex.ofReal_exp, ← Complex.ofReal_exp, Real.sinh_eq]
    push_cast
    ring)

theorem supported_sinh_integral_mass_bound (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    ‖∫ s : ℝ, g s * (Real.sinh (s / 2) : ℂ)‖ ^ 2 ≤
      (Real.sinh T - T) * (∫ s : ℝ, ‖g s‖ ^ 2) := by
  let w : ℝ → ℂ := fun s => (Real.sinh (s / 2) : ℂ)
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hg2 : Integrable (fun s : ℝ => ‖g s‖ ^ 2) :=
    (hg.1.1.continuous.norm.pow 2).integrable_of_hasCompactSupport (by
      simpa only [pow_two, Pi.mul_apply] using hg.1.2.norm.mul_right (f' := fun s => ‖g s‖))
  have hgm : MemLp g 2 (volume.restrict (Icc (-T) T)) :=
    (memLp_two_iff_integrable_sq_norm hg.1.1.continuous.aestronglyMeasurable).mpr hg2.integrableOn
  have hwm : MemLp w 2 (volume.restrict (Icc (-T) T)) :=
    (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).mpr
      (hw.norm.pow 2).integrableOn_Icc
  have hcs := norm_integral_mul_sq_le_L2_product
    (volume.restrict (Icc (-T) T)) g w hgm hwm
  have he : (∫ s in Icc (-T) T, g s * w s) = ∫ s : ℝ, g s * w s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hn
    by_cases hgs : g s = 0
    · simp [hgs]
    have hm := hg.2 (subset_tsupport g hgs)
    exact False.elim (hn ⟨hm.1.le, hm.2.le⟩)
  have hwi : (∫ s in Icc (-T) T, ‖w s‖ ^ 2) = Real.sinh T - T := by
    simp only [w, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact integral_sinh_half_sq T hT
  rw [he, hwi] at hcs
  have hM := setIntegral_le_integral (s := Icc (-T) T) hg2
    (ae_of_all _ (fun s => sq_nonneg ‖g s‖))
  have hW : 0 ≤ Real.sinh T - T := sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hT)
  exact hcs.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hM hW)

end ConnesGreen
theorem solution (T : ℝ) (hT : 0 ≤ T)
    (g : ℝ → ℂ) (hg : SupportedTest T g) :
    -2 * (Real.sinh T - T) * (∫ s : ℝ, ‖g s‖ ^ 2) ≤
      (mellinHat (conv g (starInv g)) 0 + mellinHat (conv g (starInv g)) 1).re := by
  have hp := pole_pair_re_ge_negative_difference_sq g hg.1
  have hs := supported_sinh_integral_mass_bound T hT g hg
  rw [mellin_pole_difference_eq_sinh g hg.1, norm_mul] at hp
  norm_num only [norm_neg, norm_ofNat] at hp
  nlinarith
