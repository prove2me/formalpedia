-- Prove2me | solution 1 for DoCarmoDG.isoperimetric_inequality
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T01:55:17.175984+00:00
-- url     : https://prove2.me/submissions/4808ec37-4471-4997-8585-0fe51ff34187

/-
SPDX-License-Identifier: Apache-2.0
Complete proof of the canonical sharp plane isoperimetric inequality.
All custom proof bodies are included; only canonical definitions and Mathlib
are imported. The periodic Fourier argument and both circle equality directions are reconstructed.
-/
import Definitions.Def_DoCarmo_plane_curves
import Mathlib

/- Complete module: ComplexPlaneCurve -/
section

open MeasureTheory intervalIntegral

namespace DoCarmoDG.Proof

noncomputable def planeToComplex : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

noncomputable def complexCurve (α : ℝ → EuclideanSpace ℝ (Fin 2)) : ℝ → ℂ :=
  fun t => planeToComplex (α t)

lemma complexCurve_apply (α : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    complexCurve α t = (α t 0 : ℂ) + (α t 1 : ℂ) * Complex.I := rfl

lemma complexCurve_contDiff (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) : ContDiff ℝ (⊤ : ℕ∞) (complexCurve α) :=
  planeToComplex.toContinuousLinearEquiv.contDiff.comp hα

lemma deriv_complexCurve (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : Differentiable ℝ α) (t : ℝ) :
    deriv (complexCurve α) t = planeToComplex (deriv α t) := by
  exact (planeToComplex.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
    t (hα t).hasDerivAt).deriv

lemma norm_deriv_complexCurve (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : Differentiable ℝ α) (t : ℝ) :
    ‖deriv (complexCurve α) t‖ = ‖deriv α t‖ := by
  rw [deriv_complexCurve α hα, planeToComplex.norm_map]

noncomputable def complexArea (l : ℝ) (f : ℝ → ℂ) : ℝ :=
  (1 / 2) * ∫ t in (0 : ℝ)..l, (star (f t) * deriv f t).im

lemma complexArea_complexCurve (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : Differentiable ℝ α) : complexArea l (complexCurve α) = signedArea l α := by
  unfold complexArea signedArea
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [deriv_complexCurve α hα]
  simp [complexCurve_apply, planeToComplex, Complex.mul_im, Complex.mul_re, sub_eq_add_neg]

lemma curve_complex_data (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : IsClosedUnitSpeedCurve l α) :
    0 < l ∧ ContDiff ℝ (⊤ : ℕ∞) (complexCurve α) ∧
    (∀ t, complexCurve α (t + l) = complexCurve α t) ∧
    (∀ t, ‖deriv (complexCurve α) t‖ = 1) := by
  refine ⟨hα.1, complexCurve_contDiff α hα.2.1, ?_, ?_⟩
  · intro t
    simp only [complexCurve, hα.2.2.1 t]
  · intro t
    rw [norm_deriv_complexCurve α (hα.2.1.differentiable (by simp)), hα.2.2.2]

end DoCarmoDG.Proof

end

/- Complete module: ComplexCentering -/
section

open MeasureTheory intervalIntegral

namespace DoCarmoDG.Proof

noncomputable def centeredCurve (l : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => f t - (l : ℂ)⁻¹ * ∫ s in (0 : ℝ)..l, f s

lemma centeredCurve_contDiff (l : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (centeredCurve l f) := hf.sub contDiff_const

lemma deriv_centeredCurve (l : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    deriv (centeredCurve l f) t = deriv f t := by
  exact deriv_sub_const _

lemma integral_centeredCurve (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : Continuous f) : ∫ t in (0 : ℝ)..l, centeredCurve l f t = 0 := by
  unfold centeredCurve
  rw [integral_sub (hf.intervalIntegrable 0 l) (continuous_const.intervalIntegrable 0 l), intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  have h : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [← mul_assoc, mul_inv_cancel₀ h, one_mul, sub_self]

lemma complexArea_sub_const (l : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hp : f l = f 0) (c : ℂ) : complexArea l (fun t => f t - c) = complexArea l f := by
  have hd : Continuous (deriv f) := hf.continuous_deriv (by simp)
  have hi : IntervalIntegrable (deriv f) volume 0 l := hd.intervalIntegrable 0 l
  have hz : ∫ t in (0 : ℝ)..l, deriv f t = 0 := by
    rw [integral_deriv_eq_sub (fun t _ => hf.differentiable (by simp) t) hi, hp, sub_self]
  have hc : ∫ t in (0 : ℝ)..l, (star c * deriv f t).im = 0 := by
    change (∫ t in (0 : ℝ)..l, Complex.imCLM (star c * deriv f t)) = 0
    rw [Complex.imCLM.intervalIntegral_comp_comm (hi.const_mul (star c)),
      intervalIntegral.integral_const_mul, hz, mul_zero]
    rfl
  unfold complexArea
  have he : (fun t => (star (f t - c) * deriv (fun t => f t - c) t).im) =
      fun t => (star (f t) * deriv f t).im - (star c * deriv f t).im := by
    funext t
    rw [deriv_sub_const, star_sub, sub_mul, Complex.sub_im]
  have h1 : IntervalIntegrable (fun t => (star (f t) * deriv f t).im) volume 0 l :=
    (Complex.continuous_im.comp (hf.continuous.star.mul hd)).intervalIntegrable 0 l
  have h2 : IntervalIntegrable (fun t => (star c * deriv f t).im) volume 0 l :=
    (Complex.continuous_im.comp (continuous_const.mul hd)).intervalIntegrable 0 l
  rw [he, intervalIntegral.integral_sub h1 h2, hc, sub_zero]

lemma complexArea_centeredCurve (l : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hp : f l = f 0) : complexArea l (centeredCurve l f) = complexArea l f :=
  complexArea_sub_const l f hf hp _

end DoCarmoDG.Proof

end

/- Complete module: FourierDerivative -/
section

open MeasureTheory Set
open scoped Real

namespace DoCarmoDG.Proof

theorem fourierCoeffOn_periodic (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hend : f l = f 0) (n : ℤ) (hn : n ≠ 0) :
    fourierCoeffOn hl f n =
      ((l : ℂ) / (2 * Real.pi * Complex.I * n)) * fourierCoeffOn hl (deriv f) n := by
  have h := fourierCoeffOn_of_hasDerivAt hl hn
    (fun t _ => (hf.differentiable (by norm_num) t).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable 0 l)
  rw [hend, sub_self, mul_zero, zero_sub] at h
  simp only [Complex.ofReal_zero, sub_zero] at h
  exact h.trans (by ring)

theorem fourierCoeffOn_zero_mean (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hmean : ∫ t in (0 : ℝ)..l, f t = 0) :
    fourierCoeffOn hl f 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp [hmean]

theorem fourierCoeffOn_periodic_norm_le (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hend : f l = f 0)
    (hmean : ∫ t in (0 : ℝ)..l, f t = 0) (n : ℤ) :
    ‖fourierCoeffOn hl f n‖ ≤
      (l / (2 * Real.pi)) * ‖fourierCoeffOn hl (deriv f) n‖ := by
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_zero_mean l hl f hmean, norm_zero]
    positivity
  · rw [fourierCoeffOn_periodic l hl f hf hend n hn, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [norm_div, norm_mul, norm_mul, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl, Complex.norm_I,
      mul_one, abs_of_pos Real.pi_pos]
    norm_num only [Complex.norm_ofNat]
    have hn1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
      norm_cast
      exact_mod_cast Int.one_le_abs hn
    exact div_le_div_of_nonneg_left hl.le (by positivity) (by nlinarith [Real.pi_pos])

end DoCarmoDG.Proof

end

/- Complete module: PeriodicWirtinger -/
section

open MeasureTheory Set
open scoped Real

namespace DoCarmoDG.Proof

theorem continuous_memLp_two_Ioc (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    MemLp f 2 (volume.restrict (Ioc a b)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Ioc

theorem periodic_wirtinger (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hend : f l = f 0)
    (hmean : ∫ t in (0 : ℝ)..l, f t = 0) :
    (∫ t in (0 : ℝ)..l, ‖f t‖ ^ 2) ≤
      (l / (2 * Real.pi)) ^ 2 * ∫ t in (0 : ℝ)..l, ‖deriv f t‖ ^ 2 := by
  have hs := hasSum_sq_fourierCoeffOn hl (continuous_memLp_two_Ioc f hf.continuous 0 l)
  have hd := hasSum_sq_fourierCoeffOn hl
    (continuous_memLp_two_Ioc (deriv f) hf.continuous_deriv_one 0 l)
  have hpoint (n : ℤ) : ‖fourierCoeffOn hl f n‖ ^ 2 ≤
      (l / (2 * Real.pi)) ^ 2 * ‖fourierCoeffOn hl (deriv f) n‖ ^ 2 := by
    have h := fourierCoeffOn_periodic_norm_le l hl f hf hend hmean n
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa only [mul_pow] using hh
  have h := hs.summable.tsum_le_tsum hpoint
    (hd.mul_left ((l / (2 * Real.pi)) ^ 2)).summable
  rw [hs.tsum_eq, (hd.mul_left ((l / (2 * Real.pi)) ^ 2)).tsum_eq] at h
  simp only [sub_zero, smul_eq_mul] at h
  have hh := mul_le_mul_of_nonneg_left h hl.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hl.ne', one_mul, mul_one,
    mul_left_comm l ((l / (2 * Real.pi)) ^ 2)] using hh

end DoCarmoDG.Proof

end

/- Complete module: ComplexEnergy -/
section

open MeasureTheory

namespace DoCarmoDG.Proof

lemma norm_sub_rotation_sq (z d : ℂ) (w : ℝ) :
    ‖d - (w : ℂ) * Complex.I * z‖ ^ 2 =
      ‖d‖ ^ 2 + w ^ 2 * ‖z‖ ^ 2 - 2 * w * (star z * d).im := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

lemma rotation_defect_integral (l : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (w : ℝ) :
    (∫ t in (0 : ℝ)..l, ‖deriv f t - (w : ℂ) * Complex.I * f t‖ ^ 2) =
      (∫ t in (0 : ℝ)..l, ‖deriv f t‖ ^ 2) +
      w ^ 2 * (∫ t in (0 : ℝ)..l, ‖f t‖ ^ 2) - 4 * w * complexArea l f := by
  have hd := hf.continuous_deriv (by simp)
  simp_rw [norm_sub_rotation_sq]
  have h1 : IntervalIntegrable (fun t => ‖deriv f t‖ ^ 2) volume 0 l :=
    (hd.norm.pow 2).intervalIntegrable 0 l
  have h2 : IntervalIntegrable (fun t => w ^ 2 * ‖f t‖ ^ 2) volume 0 l :=
    (continuous_const.mul (hf.continuous.norm.pow 2)).intervalIntegrable 0 l
  have h3 : IntervalIntegrable (fun t => 2*w*(star (f t)*deriv f t).im) volume 0 l :=
    (continuous_const.mul (Complex.continuous_im.comp (hf.continuous.star.mul hd))).intervalIntegrable 0 l
  rw [intervalIntegral.integral_sub (h1.add h2) h3,
    intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold complexArea
  ring

lemma unit_speed_energy (l : ℝ) (f : ℝ → ℂ) (hu : ∀ t, ‖deriv f t‖ = 1) :
    (∫ t in (0 : ℝ)..l, ‖deriv f t‖ ^ 2) = l := by
  simp [hu]

lemma centered_energy_bound (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : f l = f 0)
    (hm : ∫ t in (0 : ℝ)..l, f t = 0) (hu : ∀ t, ‖deriv f t‖ = 1) :
    (2 * Real.pi / l) ^ 2 * (∫ t in (0 : ℝ)..l, ‖f t‖ ^ 2) ≤ l := by
  have hw := periodic_wirtinger l hl f hf hp hm
  rw [unit_speed_energy l f hu] at hw
  have h := mul_le_mul_of_nonneg_left hw (sq_nonneg (2 * Real.pi / l))
  have he : (2 * Real.pi / l) ^ 2 * ((l / (2 * Real.pi)) ^ 2 * l) = l := by
    field_simp
  rwa [he] at h

end DoCarmoDG.Proof

end

/- Complete module: ComplexIsoperimetric -/
section

open MeasureTheory

namespace DoCarmoDG.Proof

lemma defect_nonneg (l : ℝ) (hl : 0 ≤ l) (f : ℝ → ℂ) (w : ℝ) :
    0 ≤ ∫ t in (0 : ℝ)..l, ‖deriv f t - (w : ℂ) * Complex.I * f t‖ ^ 2 :=
  intervalIntegral.integral_nonneg hl (fun _ _ => sq_nonneg _)

lemma signed_area_bound (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : f l = f 0)
    (hm : ∫ t in (0 : ℝ)..l, f t = 0) (hu : ∀ t, ‖deriv f t‖ = 1)
    (w : ℝ) (hw : w ^ 2 = (2 * Real.pi / l) ^ 2) :
    4 * w * complexArea l f ≤ 2 * l := by
  have hb := centered_energy_bound l hl f hf hp hm hu
  have hn := defect_nonneg l hl.le f w
  rw [rotation_defect_integral l f hf w, unit_speed_energy l f hu, hw] at hn
  linarith

lemma centered_isoperimetric (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : f l = f 0)
    (hm : ∫ t in (0 : ℝ)..l, f t = 0) (hu : ∀ t, ‖deriv f t‖ = 1) :
    4 * Real.pi * |complexArea l f| ≤ l ^ 2 := by
  have hp' := signed_area_bound l hl f hf hp hm hu (2 * Real.pi / l) rfl
  have hn' := signed_area_bound l hl f hf hp hm hu (-(2 * Real.pi / l)) (by ring)
  have hp'' := mul_le_mul_of_nonneg_right hp' hl.le
  have hn'' := mul_le_mul_of_nonneg_right hn' hl.le
  field_simp at hp'' hn''
  rcases le_total 0 (complexArea l f) with h | h
  · rw [abs_of_nonneg h]
    nlinarith
  · rw [abs_of_nonpos h]
    nlinarith

lemma continuous_square_integral_zero (l : ℝ) (hl : 0 < l) (g : ℝ → ℂ)
    (hg : Continuous g) (hz : ∫ t in (0 : ℝ)..l, ‖g t‖ ^ 2 = 0) :
    ∀ t ∈ Set.Ioc 0 l, g t = 0 := by
  have hi : IntervalIntegrable (fun t => ‖g t‖ ^ 2) volume 0 l :=
    (hg.norm.pow 2).intervalIntegrable 0 l
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hl.le
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖g t‖)) hi).mp hz
  have he := Measure.eqOn_Ioc_of_ae_eq volume hae (hg.norm.pow 2).continuousOn continuous_const.continuousOn
  intro t ht
  have h := he ht
  simpa using h

lemma centered_extremal_radius (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f l)
    (hm : ∫ t in (0 : ℝ)..l, f t = 0) (hu : ∀ t, ‖deriv f t‖ = 1)
    (he : 4 * Real.pi * |complexArea l f| = l ^ 2) :
    ∀ t, ‖f t‖ = l / (2 * Real.pi) := by
  have hp0 : f l = f 0 := by simpa using hp 0
  let w : ℝ := if 0 ≤ complexArea l f then 2 * Real.pi / l else -(2 * Real.pi / l)
  have hw : w ^ 2 = (2 * Real.pi / l) ^ 2 := by unfold w; split_ifs <;> ring
  have hwabs : |w| = 2 * Real.pi / l := by
    have hpos : 0 ≤ 2 * Real.pi / l := le_of_lt (div_pos (by positivity) hl)
    unfold w
    split_ifs <;> simp [abs_of_nonneg hpos]
  have hwa : 4 * w * complexArea l f = 2 * l := by
    unfold w
    split_ifs with h
    · rw [abs_of_nonneg h] at he
      field_simp
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge h)] at he
      field_simp
      nlinarith
  have hb := centered_energy_bound l hl f hf hp0 hm hu
  have hn := defect_nonneg l hl.le f w
  have hz : (∫ t in (0 : ℝ)..l, ‖deriv f t - (w : ℂ) * Complex.I * f t‖ ^ 2) = 0 := by
    rw [rotation_defect_integral l f hf w, unit_speed_energy l f hu, hwa, hw]
    rw [rotation_defect_integral l f hf w, unit_speed_energy l f hu, hwa, hw] at hn
    linarith
  have hg : Continuous (fun t => deriv f t - (w : ℂ) * Complex.I * f t) :=
    (hf.continuous_deriv (by simp)).sub (continuous_const.mul hf.continuous)
  have hzero := continuous_square_integral_zero l hl _ hg hz
  intro t
  obtain ⟨u, huI, htu⟩ := hp.exists_mem_Ioc hl t 0
  rw [htu]
  have heq := sub_eq_zero.mp (hzero u (by simpa using huI))
  have hnorm := congrArg norm heq
  rw [hu, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, hwabs] at hnorm
  apply (eq_div_iff (ne_of_gt (by positivity : 0 < 2 * Real.pi))).mpr
  have hn' := congrArg (fun z : ℝ => z * l) hnorm
  field_simp at hn'
  nlinarith

end DoCarmoDG.Proof

end

/- Complete module: PlaneIsoperimetric -/
section

open MeasureTheory

namespace DoCarmoDG.Proof

lemma plane_isoperimetric_forward (l : ℝ) (α : ℝ → EuclideanSpace ℝ (Fin 2))
    (hα : IsClosedUnitSpeedCurve l α) :
    l ^ 2 - 4 * Real.pi * |signedArea l α| ≥ 0 ∧
    (l ^ 2 - 4 * Real.pi * |signedArea l α| = 0 →
      ∃ c : EuclideanSpace ℝ (Fin 2), ∃ r : ℝ, 0 < r ∧ ∀ t, ‖α t - c‖ = r) := by
  obtain ⟨hl, hfTop, hp, hu⟩ := curve_complex_data l α hα
  let f := complexCurve α
  have hf : ContDiff ℝ 1 f := hfTop.of_le (by simp)
  have hp0 : f l = f 0 := by simpa [f] using hp 0
  have hperiod : Function.Periodic f l := hp
  let g := centeredCurve l f
  have hg : ContDiff ℝ 1 g := centeredCurve_contDiff l f hf
  have hgp : Function.Periodic g l := by
    intro t
    simp only [g, centeredCurve, hperiod t]
  have hgp0 : g l = g 0 := by simpa using hgp 0
  have hgm : ∫ t in (0 : ℝ)..l, g t = 0 := integral_centeredCurve l hl f hf.continuous
  have hgu : ∀ t, ‖deriv g t‖ = 1 := by
    intro t
    rw [show g = centeredCurve l f from rfl, deriv_centeredCurve]
    exact hu t
  have harea : complexArea l g = signedArea l α := by
    rw [show g = centeredCurve l f from rfl, complexArea_centeredCurve l f hf hp0]
    exact complexArea_complexCurve l α (hα.2.1.differentiable (by simp))
  have hb := centered_isoperimetric l hl g hg hgp0 hgm hgu
  rw [harea] at hb
  refine ⟨by linarith, ?_⟩
  intro he
  have he' : 4 * Real.pi * |complexArea l g| = l ^ 2 := by rw [harea]; linarith
  have hn := centered_extremal_radius l hl g hg hgp hgm hgu he'
  let c : ℂ := (l : ℂ)⁻¹ * ∫ t in (0 : ℝ)..l, f t
  refine ⟨planeToComplex.symm c, l / (2 * Real.pi), by positivity, ?_⟩
  intro t
  rw [← planeToComplex.norm_map (α t - planeToComplex.symm c), map_sub,
    planeToComplex.apply_symm_apply]
  exact hn t

end DoCarmoDG.Proof

end

/- Complete module: CircleTangent -/
section

open Set

namespace DoCarmoDG.Proof

lemma continuous_sq_constant (v : ℝ → ℝ) (hv : Continuous v) (r : ℝ) (hr : 0 < r)
    (hsq : ∀ t, v t ^ 2 = r ^ 2) (t : ℝ) : v t = v 0 := by
  have hvals (x : ℝ) : v x = r ∨ v x = -r := (sq_eq_sq_iff_eq_or_eq_neg).mp (hsq x)
  rcases hvals t with ht | ht <;> rcases hvals 0 with h0 | h0
  · exact ht.trans h0.symm
  · obtain ⟨x, hx⟩ := intermediate_value_univ 0 t hv
      (show (0 : ℝ) ∈ Icc (v 0) (v t) by simp [ht, h0, hr.le])
    have := hsq x
    rw [hx] at this
    nlinarith
  · obtain ⟨x, hx⟩ := intermediate_value_univ t 0 hv
      (show (0 : ℝ) ∈ Icc (v t) (v 0) by simp [ht, h0, hr.le])
    have := hsq x
    rw [hx] at this
    nlinarith
  · exact ht.trans h0.symm

lemma circle_tangent_ode (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (r : ℝ)
    (hr : 0 < r) (hnorm : ∀ t, ‖f t‖ = r) (hspeed : ∀ t, ‖deriv f t‖ = 1) :
    ∃ w : ℝ, |w| * r = 1 ∧ ∀ t, deriv f t = (w : ℂ) * Complex.I * f t := by
  let v : ℝ → ℝ := fun t => (star (f t) * deriv f t).im
  have hre (t : ℝ) : (star (f t) * deriv f t).re = 0 := by
    have hd := (hf.differentiable (by norm_num) t).hasDerivAt.norm_sq
    have he : (fun t => ‖f t‖ ^ 2) = fun _ => r ^ 2 := funext fun t => by rw [hnorm]
    rw [he] at hd
    have hh := hd.unique (hasDerivAt_const t (r ^ 2))
    have hh' : 2 * (star (f t) * deriv f t).re = 0 := by
      simpa only [Complex.inner, Complex.star_def, mul_comm] using hh
    linarith
  have hsq (t : ℝ) : v t ^ 2 = r ^ 2 := by
    have hh := Complex.sq_norm (star (f t) * deriv f t)
    rw [norm_mul, norm_star, hnorm, hspeed, mul_one, Complex.normSq_apply, hre] at hh
    change (star (f t) * deriv f t).im ^ 2 = r ^ 2
    nlinarith
  have hv : Continuous v := Complex.continuous_im.comp
    (hf.continuous.star.mul hf.continuous_deriv_one)
  have hc := continuous_sq_constant v hv r hr hsq
  have hprod (t : ℝ) : star (f t) * deriv f t = (v 0 : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [hre]; simp
    · simpa [v] using hc t
  refine ⟨v 0 / r ^ 2, ?_, ?_⟩
  · have ha : |v 0| = r := by
      nlinarith [sq_abs (v 0), abs_nonneg (v 0), hsq 0]
    rw [abs_div, abs_pow, abs_of_pos hr, ha]
    field_simp
  · intro t
    have ht : f t ≠ 0 := by
      intro hz
      have := hnorm t
      simp [hz] at this
      linarith
    apply mul_left_cancel₀ (star_ne_zero.mpr ht)
    rw [hprod]
    have hn : star (f t) * f t = (r ^ 2 : ℝ) := by
      rw [Complex.star_def, Complex.conj_mul', hnorm, Complex.ofReal_pow]
    calc
      (v 0 : ℂ) * Complex.I = ((v 0 / r ^ 2 : ℝ) : ℂ) * Complex.I * (r ^ 2 : ℝ) := by
        push_cast
        field_simp [show (r : ℂ) ≠ 0 by exact_mod_cast hr.ne']
      _ = star (f t) * (((v 0 / r ^ 2 : ℝ) : ℂ) * Complex.I * f t) := by
        rw [← hn]
        ring

end DoCarmoDG.Proof

end

/- Complete module: RotationODE -/
section

namespace DoCarmoDG.Proof

lemma rotation_ode_solution (f : ℝ → ℂ) (c : ℂ)
    (hf : Differentiable ℝ f) (hode : ∀ t, deriv f t = c * f t) (t : ℝ) :
    f t = Complex.exp ((t : ℂ) * c) * f 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x : ℂ) * c) * f x
  have hg (x : ℝ) : HasDerivAt g 0 x := by
    have he := (((Complex.ofRealCLM.hasDerivAt : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x)).neg.mul_const c).cexp
    have hd := he.mul (hf x).hasDerivAt
    apply hd.congr_deriv
    simp only [Pi.neg_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, hode]
    ring
  have hc := is_const_of_deriv_eq_zero (fun x => (hg x).differentiableAt)
    (fun x => (hg x).deriv) t 0
  have hx := congrArg (fun z : ℂ => Complex.exp ((t : ℂ) * c) * z) hc
  simpa [g, ← mul_assoc, ← Complex.exp_add] using hx

lemma rotation_ode_norm (f : ℝ → ℂ) (w : ℝ)
    (hf : Differentiable ℝ f) (hode : ∀ t, deriv f t = (w : ℂ) * Complex.I * f t)
    (t : ℝ) : ‖f t‖ = ‖f 0‖ := by
  rw [rotation_ode_solution f ((w : ℂ) * Complex.I) hf hode t, norm_mul,
    Complex.norm_exp]
  simp

end DoCarmoDG.Proof

end

/- Complete module: CirclePeriod -/
section

open Set
open scoped Real

namespace DoCarmoDG.Proof

lemma rotation_simple_period (l r w : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hw : |w| * r = 1) (f : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hzero : f 0 ≠ 0) (hend : f l = f 0)
    (hinj : Set.InjOn f (Ico (0 : ℝ) l))
    (hode : ∀ t, deriv f t = (w : ℂ) * Complex.I * f t) :
    l = 2 * Real.pi * r := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have he (t : ℝ) := rotation_ode_solution f ((w : ℂ) * Complex.I) hf hode t
  have hel : Complex.exp ((l : ℂ) * ((w : ℂ) * Complex.I)) = 1 := by
    apply mul_right_cancel₀ hzero
    rw [← he, hend, one_mul]
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hel
  have hkreal : l * w = (k : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hk
    simpa using this
  have hk0 : k ≠ 0 := by
    intro h
    simp [h] at hkreal
    exact hkreal.elim hl.ne' hw0
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  have habs : l * |w| = |(k : ℝ)| * (2 * Real.pi) := by
    simpa [abs_mul, abs_of_pos hl, abs_of_pos Real.pi_pos] using congrArg abs hkreal
  have hlower : 2 * Real.pi * r ≤ l := by
    have ht := mul_le_mul_of_nonneg_right (show 2 * Real.pi ≤ l * |w| by nlinarith [Real.pi_pos]) hr.le
    nlinarith [hw]
  have hep : Complex.exp (((2 * Real.pi * r : ℝ) : ℂ) * ((w : ℂ) * Complex.I)) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    rcases le_total 0 w with hp | hn
    · refine ⟨1, ?_⟩
      rw [abs_of_nonneg hp] at hw
      apply Complex.ext <;> simp
      nlinarith [Real.pi_pos]
    · refine ⟨-1, ?_⟩
      rw [abs_of_nonpos hn] at hw
      apply Complex.ext <;> simp
      nlinarith [Real.pi_pos]
  have hupper : l ≤ 2 * Real.pi * r := by
    by_contra h
    have ht : 2 * Real.pi * r < l := lt_of_not_ge h
    have hp : 0 < 2 * Real.pi * r := by positivity
    have heq : f (2 * Real.pi * r) = f 0 := by rw [he, hep, one_mul]
    have := hinj ⟨hp.le, ht⟩ ⟨le_rfl, hl⟩ heq
    linarith
  exact le_antisymm hupper hlower

end DoCarmoDG.Proof

end

/- Complete module: CircleArea -/
section

open MeasureTheory Set
open scoped Real

namespace DoCarmoDG.Proof

lemma complexArea_of_rotation (l r w : ℝ) (f : ℝ → ℂ)
    (hnorm : ∀ t, ‖f t‖ = r)
    (hode : ∀ t, deriv f t = (w : ℂ) * Complex.I * f t) :
    complexArea l f = (1 / 2) * l * w * r ^ 2 := by
  have he (t : ℝ) : (star (f t) * deriv f t).im = w * r ^ 2 := by
    rw [hode]
    have hn : star (f t) * f t = ((r ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', hnorm, Complex.ofReal_pow]
    calc
      (star (f t) * ((w : ℂ) * Complex.I * f t)).im =
          (((w : ℂ) * Complex.I) * (star (f t) * f t)).im := by congr 1; ring
      _ = w * r ^ 2 := by
        rw [hn]
        simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
  unfold complexArea
  simp_rw [he]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

lemma complex_circle_equality (l : ℝ) (hl : 0 < l) (f : ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (hend : f l = f 0)
    (hspeed : ∀ t, ‖deriv f t‖ = 1) (hinj : Set.InjOn f (Ico (0 : ℝ) l))
    (c : ℂ) (r : ℝ) (hr : 0 < r) (hnorm : ∀ t, ‖f t - c‖ = r) :
    l ^ 2 - 4 * Real.pi * |complexArea l f| = 0 := by
  let g : ℝ → ℂ := fun t => f t - c
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hd (t : ℝ) : deriv g t = deriv f t := deriv_sub_const c
  have hgs (t : ℝ) : ‖deriv g t‖ = 1 := by rw [hd, hspeed]
  have hgn (t : ℝ) : ‖g t‖ = r := hnorm t
  obtain ⟨w, hw, hode⟩ := circle_tangent_ode g hg r hr hgn hgs
  have hz : g 0 ≠ 0 := by
    intro h
    have := hgn 0
    rw [h, norm_zero] at this
    linarith
  have he : g l = g 0 := by dsimp [g]; rw [hend]
  have hgi : Set.InjOn g (Ico (0 : ℝ) l) := by
    intro x hx y hy hxy
    apply hinj hx hy
    exact sub_left_injective hxy
  have hp := rotation_simple_period l r w hl hr hw g
    (hg.differentiable (by norm_num)) hz he hgi hode
  have ha := complexArea_of_rotation l r w g hgn hode
  have hag : complexArea l g = complexArea l f := complexArea_sub_const l f hf hend c
  rw [hag] at ha
  rw [ha, abs_mul, abs_mul, abs_mul, abs_of_pos hl, abs_pow, abs_of_pos hr]
  norm_num only [abs_div, abs_one, abs_two] 
  have hwr : |w| * r ^ 2 = r := by nlinarith [hw]
  rw [hp]
  nlinarith [sq_nonneg Real.pi]

end DoCarmoDG.Proof

end

/- Complete module: IsoperimetricRoot -/
section

namespace DoCarmoDG

theorem isoperimetric_inequality
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsSimpleClosedCurve l alpha) :
    l ^ 2 - 4 * Real.pi * |signedArea l alpha| ≥ 0 ∧
      (l ^ 2 - 4 * Real.pi * |signedArea l alpha| = 0 ↔
        ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧ ∀ t, ‖alpha t - c‖ = r) := by
  obtain ⟨hb, he⟩ := Proof.plane_isoperimetric_forward l alpha halpha.1
  refine ⟨hb, ⟨he, ?_⟩⟩
  rintro ⟨c, r, hr, hc⟩
  obtain ⟨hl, hfTop, hp, hu⟩ := Proof.curve_complex_data l alpha halpha.1
  have hf : ContDiff ℝ 1 (Proof.complexCurve alpha) := hfTop.of_le (by simp)
  have hend : Proof.complexCurve alpha l = Proof.complexCurve alpha 0 := by
    simpa using hp 0
  have hinj : Set.InjOn (Proof.complexCurve alpha) (Set.Ico (0 : ℝ) l) := by
    intro x hx y hy hxy
    by_contra hn
    apply halpha.2 x hx y hy hn
    exact Proof.planeToComplex.injective hxy
  have hn (t : ℝ) : ‖Proof.complexCurve alpha t - Proof.planeToComplex c‖ = r := by
    rw [Proof.complexCurve, ← map_sub, Proof.planeToComplex.norm_map]
    exact hc t
  have h := Proof.complex_circle_equality l hl (Proof.complexCurve alpha) hf hend hu hinj
    (Proof.planeToComplex c) r hr hn
  rwa [Proof.complexArea_complexCurve l alpha (halpha.1.2.1.differentiable (by simp))] at h

end DoCarmoDG

open DoCarmoDG

theorem solution
    (l : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 2))
    (halpha : IsSimpleClosedCurve l alpha) :
    l ^ 2 - 4 * Real.pi * |signedArea l alpha| ≥ 0 ∧
      (l ^ 2 - 4 * Real.pi * |signedArea l alpha| = 0 ↔
        ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧ ∀ t, ‖alpha t - c‖ = r) := by
  exact DoCarmoDG.isoperimetric_inequality l alpha halpha

end
