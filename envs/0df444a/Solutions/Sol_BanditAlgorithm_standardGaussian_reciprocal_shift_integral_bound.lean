-- Prove2me | solution 1 for BanditAlgorithm.standardGaussian_reciprocal_shift_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T00:01:05.564675+00:00
-- url     : https://prove2.me/submissions/50471634-534f-4543-8c42-91fa5d7731f3

import Theorems.Thm_BanditAlgorithm_standardGaussian_mills_lower_bound
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def Qcheck (u : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Ioi u)

private theorem shifted_tail_check (z a : ℝ) :
    (gaussianReal z 1).real (Set.Ioi (-a)) = Qcheck (-a - z) := by
  have hmap :
      (gaussianReal z 1).map (fun x ↦ x - z) = gaussianReal 0 1 := by
    simpa using
      (gaussianReal_map_sub_const (μ := z) (v := (1 : NNReal)) z)
  have happ := congrArg (fun P : Measure ℝ ↦ P.real (Set.Ioi (-a - z))) hmap
  change
    ((gaussianReal z 1).map (fun x ↦ x - z)).real (Set.Ioi (-a - z)) =
      (gaussianReal 0 1).real (Set.Ioi (-a - z)) at happ
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Ioi] at happ
  have hpre :
      (fun x : ℝ ↦ x - z) ⁻¹' Set.Ioi (-a - z) = Set.Ioi (-a) := by
    ext x
    change (-a - z < x - z) ↔ -a < x
    constructor <;> intro h <;> linarith
  simpa [Qcheck, hpre] using happ

private theorem Qcheck_compl (u : ℝ) :
    Qcheck u + Qcheck (-u) = 1 := by
  let P : Measure ℝ := gaussianReal 0 1
  have hmap :
      P.map (fun x ↦ -x) = P := by
    dsimp [P]
    simpa using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have happ := congrArg (fun M : Measure ℝ ↦ M.real (Set.Ioi (-u))) hmap
  change (P.map (fun x ↦ -x)).real (Set.Ioi (-u)) =
    P.real (Set.Ioi (-u)) at happ
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Ioi] at happ
  have hpre :
      (fun x : ℝ ↦ -x) ⁻¹' Set.Ioi (-u) = Set.Iio u := by
    ext x
    change (-u < -x) ↔ x < u
    constructor <;> intro h <;> linarith
  have hsym : Qcheck (-u) = P.real (Set.Iio u) := by
    simpa [Qcheck, P, hpre] using happ.symm
  have hzero : P.real (Set.Iic u \ Set.Iio u) = 0 := by
    letI : NullSingletonClass P := by
      dsimp [P]
      exact nullSingletonClass_gaussianReal (by norm_num)
    have hdiff : Set.Iic u \ Set.Iio u = {u} := by
      ext x
      simp
    rw [hdiff, Measure.real, measure_singleton]
    simp
  have hioic : P.real (Set.Iio u) = P.real (Set.Iic u) := by
    exact MeasureTheory.measureReal_eq_measureReal_of_null_diff Set.Iio_subset_Iic_self hzero
  have hcompl :=
    MeasureTheory.measureReal_add_measureReal_compl
      (μ := P) (s := Set.Ioi u) measurableSet_Ioi
  rw [show (Set.Ioi u)ᶜ = Set.Iic u by ext x; simp] at hcompl
  rw [hsym, hioic]
  simpa [Qcheck, P] using hcompl

private theorem Qcheck_zero : Qcheck 0 = 1 / 2 := by
  have h := Qcheck_compl 0
  norm_num at h ⊢
  linarith

private theorem Qcheck_antitone : Antitone Qcheck := by
  intro a b hab
  unfold Qcheck
  exact MeasureTheory.measureReal_mono (Set.Ioi_subset_Ioi hab)

private theorem Qcheck_pos (u : ℝ) : 0 < Qcheck u := by
  by_cases hu : 0 ≤ u
  · obtain ⟨c, hc, hmills⟩ := standardGaussian_mills_lower_bound
    have h := hmills u hu
    have hleft : 0 < c / (u + 1) * Real.exp (-u ^ 2 / 2) := by
      positivity
    exact hleft.trans_le h
  · have hle : Qcheck 0 ≤ Qcheck u :=
      Qcheck_antitone (le_of_not_ge hu)
    exact Qcheck_zero ▸ (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_le hle

private theorem Qcheck_upper (u : ℝ) (hu : 0 ≤ u) :
    Qcheck u ≤ Real.exp (-u ^ 2 / 2) := by
  have hsub :
      HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
    constructor
    · exact fun t ↦ integrable_exp_mul_gaussianReal t
    · intro t
      rw [mgf_id_gaussianReal]
      norm_num
  apply (MeasureTheory.measureReal_mono
    (show Set.Ioi u ⊆ {x : ℝ | u ≤ id x} by
      intro x hx
      change u < x at hx
      exact hx.le)).trans
  simpa using hsub.measure_ge_le hu

private theorem reciprocal_ratio_bad_check
    (c : ℝ) (hc : 0 < c)
    (hmills : ∀ u : ℝ, 0 ≤ u →
      c / (u + 1) * Real.exp (-u ^ 2 / 2) ≤ Qcheck u)
    (u : ℝ) (hu : 0 ≤ u) :
    1 / Qcheck u - 1 ≤
      (u + 1) / c * Real.exp (u ^ 2 / 2) := by
  have hq := Qcheck_pos u
  have hbpos :
      0 < c / (u + 1) * Real.exp (-u ^ 2 / 2) := by positivity
  have hinv :
      1 / Qcheck u ≤
        1 / (c / (u + 1) * Real.exp (-u ^ 2 / 2)) :=
    one_div_le_one_div_of_le hbpos (hmills u hu)
  have heq :
      1 / (c / (u + 1) * Real.exp (-u ^ 2 / 2)) =
        (u + 1) / c * Real.exp (u ^ 2 / 2) := by
    rw [show -u ^ 2 / 2 = -(u ^ 2 / 2) by ring, Real.exp_neg]
    field_simp
  rw [heq] at hinv
  linarith

private theorem reciprocal_ratio_good_check (u : ℝ) (hu : u < 0) :
    1 / Qcheck u - 1 ≤
      2 * Real.exp (-(-u) ^ 2 / 2) := by
  have hq := Qcheck_pos u
  have hqhalf : 1 / 2 ≤ Qcheck u := by
    have := Qcheck_antitone (show u ≤ 0 by linarith)
    simpa [Qcheck_zero] using this
  have hcomp : 1 - Qcheck u = Qcheck (-u) := by
    linarith [Qcheck_compl u]
  have hratio :
      1 / Qcheck u - 1 = (1 - Qcheck u) / Qcheck u := by
    field_simp
  rw [hratio, hcomp]
  have hqnonneg : 0 ≤ Qcheck (-u) := (Qcheck_pos (-u)).le
  calc
    Qcheck (-u) / Qcheck u ≤ Qcheck (-u) / (1 / 2) := by
      exact div_le_div_of_nonneg_left hqnonneg (by norm_num) hqhalf
    _ = 2 * Qcheck (-u) := by ring
    _ ≤ 2 * Real.exp (-(-u) ^ 2 / 2) := by
      gcongr
      exact Qcheck_upper (-u) (by linarith)

private theorem exp_moment_Ioi_gr (a : ℝ) (ha : 0 < a) :
    (∫ u : ℝ in Set.Ioi 0, (u + 1) * Real.exp (-(a * u))) =
      1 / a ^ 2 + 1 / a := by
  have h1 : IntegrableOn
      (fun u : ℝ ↦ u * Real.exp (-(a * u))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num) ha
    simpa only [Real.rpow_one, neg_mul] using h
  have h0 : IntegrableOn
      (fun u : ℝ ↦ Real.exp (-(a * u))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (by norm_num) (by norm_num) ha
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul] using h
  rw [show (fun u : ℝ ↦ (u + 1) * Real.exp (-(a * u))) =
      fun u ↦ u * Real.exp (-(a * u)) + Real.exp (-(a * u)) by
    funext u
    ring]
  rw [integral_add h1 h0]
  have hi1 := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := a) (by norm_num) ha
  have hi0 := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := a) (by norm_num) ha
  have hi1' :
      (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-(a * t))) =
        (1 / a) ^ (2 : ℝ) * Real.Gamma 2 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hi1
  have hi0' :
      (∫ t : ℝ in Set.Ioi 0, Real.exp (-(a * t))) =
        (1 / a) * Real.Gamma 1 := by
    simpa only [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, one_mul,
      one_div, Real.rpow_one] using hi0
  rw [hi1', hi0']
  rw [Real.rpow_two, show Real.Gamma 2 = 1 by
    simpa using (Real.Gamma_nat_eq_factorial 1), Real.Gamma_one]
  field_simp

private theorem translate_Ioi_gr (a : ℝ) (f : ℝ → ℝ) :
    (∫ x in Set.Ioi a, f (x - a) ∂volume) =
      ∫ u in Set.Ioi 0, f u ∂volume := by
  have hmp := measurePreserving_add_left (volume : Measure ℝ) a
  have hemb : MeasurableEmbedding (fun x : ℝ ↦ a + x) :=
    (Homeomorph.addLeft a).measurableEmbedding
  have h := hmp.setIntegral_preimage_emb hemb
    (fun y ↦ f (y - a)) (Set.Ioi a)
  have hpre : (fun x : ℝ ↦ a + x) ⁻¹' Set.Ioi a = Set.Ioi 0 := by
    ext x
    simp
  rw [hpre] at h
  simpa using h.symm

private theorem bad_region_integral_gr (a : ℝ) (ha : 0 < a) :
    (∫ z : ℝ in Set.Iic (-a),
        (1 - a - z) * Real.exp (a ^ 2 / 2 + a * z)) =
      Real.exp (-a ^ 2 / 2) * (1 / a ^ 2 + 1 / a) := by
  let f : ℝ → ℝ := fun x ↦
    (x - a + 1) * Real.exp (a ^ 2 / 2 - a * x)
  calc
    (∫ z : ℝ in Set.Iic (-a),
        (1 - a - z) * Real.exp (a ^ 2 / 2 + a * z)) =
        ∫ z : ℝ in Set.Iic (-a), f (-z) := by
          apply setIntegral_congr_fun measurableSet_Iic
          intro z hz
          dsimp [f]
          congr 1 <;> ring
    _ = ∫ x : ℝ in Set.Ioi a, f x := by
          simpa using integral_comp_neg_Iic (-a) f
    _ = ∫ u : ℝ in Set.Ioi 0,
          (u + 1) * Real.exp (-a ^ 2 / 2 - a * u) := by
          rw [← translate_Ioi_gr a
            (fun u ↦ (u + 1) * Real.exp (-a ^ 2 / 2 - a * u))]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro x hx
          dsimp [f]
          congr 1 <;> ring
    _ = Real.exp (-a ^ 2 / 2) *
          ∫ u : ℝ in Set.Ioi 0, (u + 1) * Real.exp (-(a * u)) := by
          rw [← integral_const_mul]
          apply setIntegral_congr_fun measurableSet_Ioi
          intro u hu
          change (u + 1) * Real.exp (-a ^ 2 / 2 - a * u) =
            Real.exp (-a ^ 2 / 2) * ((u + 1) * Real.exp (-(a * u)))
          rw [show -a ^ 2 / 2 - a * u =
            -a ^ 2 / 2 + -(a * u) by ring, Real.exp_add]
          ring
    _ = Real.exp (-a ^ 2 / 2) * (1 / a ^ 2 + 1 / a) := by
          rw [exp_moment_Ioi_gr a ha]

private theorem bad_region_integrable_gr (a : ℝ) (ha : 0 < a) :
    IntegrableOn
      (fun z : ℝ ↦
        (1 - a - z) * Real.exp (a ^ 2 / 2 + a * z))
      (Set.Iic (-a)) volume := by
  have h1 : IntegrableOn
      (fun u : ℝ ↦ u * Real.exp (-(a * u))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (by norm_num) (by norm_num) ha
    simpa only [Real.rpow_one, neg_mul] using h
  have h0 : IntegrableOn
      (fun u : ℝ ↦ Real.exp (-(a * u))) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (by norm_num) (by norm_num) ha
    simpa only [Real.rpow_zero, Real.rpow_one, one_mul, neg_mul] using h
  have hbase : IntegrableOn
      (fun u : ℝ ↦ (u + 1) * Real.exp (-(a * u))) (Set.Ioi 0) := by
    rw [show (fun u : ℝ ↦ (u + 1) * Real.exp (-(a * u))) =
      (fun u ↦ u * Real.exp (-(a * u))) +
        fun u ↦ Real.exp (-(a * u)) by
      funext u
      simp only [Pi.add_apply]
      ring]
    exact h1.add h0
  have hbasec : IntegrableOn
      (fun u : ℝ ↦ Real.exp (-a ^ 2 / 2) *
        ((u + 1) * Real.exp (-(a * u)))) (Set.Ioi 0) :=
    hbase.const_mul _
  let F : ℝ → ℝ := fun x ↦
    Real.exp (-a ^ 2 / 2) *
      ((x - a + 1) * Real.exp (-(a * (x - a))))
  have htrans : IntegrableOn F (Set.Ioi a) := by
    have hmp := measurePreserving_add_left (volume : Measure ℝ) a
    have hemb : MeasurableEmbedding (fun x : ℝ ↦ a + x) :=
      (Homeomorph.addLeft a).measurableEmbedding
    apply (hmp.integrableOn_comp_preimage hemb).mp
    have hpre : (fun x : ℝ ↦ a + x) ⁻¹' Set.Ioi a = Set.Ioi 0 := by
      ext x
      simp
    rw [hpre]
    simpa [F, Function.comp_def] using hbasec
  have hneg : IntegrableOn (fun z : ℝ ↦ F (-z)) (Set.Iio (-a)) := by
    have hmp := Measure.measurePreserving_neg (volume : Measure ℝ)
    have hemb : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    have hpre : (fun x : ℝ ↦ -x) ⁻¹' Set.Ioi a = Set.Iio (-a) := by
      ext x
      simp
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hemb).mpr htrans
  apply (integrableOn_Iic_iff_integrableOn_Iio (μ := volume)).mpr
  apply hneg.congr_fun _ measurableSet_Iio
  intro z hz
  dsimp [F]
  rw [show -z - a + 1 = 1 - a - z by ring]
  rw [show -(a * (-z - a)) = a * z + a ^ 2 by ring]
  calc
    Real.exp (-a ^ 2 / 2) *
        ((1 - a - z) * Real.exp (a * z + a ^ 2)) =
      (1 - a - z) *
        (Real.exp (-a ^ 2 / 2) * Real.exp (a * z + a ^ 2)) := by ring
    _ = (1 - a - z) * Real.exp (a ^ 2 / 2 + a * z) := by
      rw [← Real.exp_add]
      congr 2
      ring

private theorem good_region_integral_gr (a : ℝ) :
    (∫ z : ℝ in Set.Ioi (-a),
        Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2))) ≤
      Real.sqrt Real.pi * Real.exp (-a ^ 2 / 4) := by
  have heq (z : ℝ) :
      -(((a + z) ^ 2 + z ^ 2) / 2) =
        -(z + a / 2) ^ 2 - a ^ 2 / 4 := by ring
  have hpoint (z : ℝ) :
      Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2)) =
        Real.exp (-a ^ 2 / 4) * Real.exp (-(z + a / 2) ^ 2) := by
    rw [heq, show -(z + a / 2) ^ 2 - a ^ 2 / 4 =
      -a ^ 2 / 4 + -(z + a / 2) ^ 2 by ring, Real.exp_add]
  rw [show (fun z : ℝ ↦ Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2))) =
      fun z ↦ Real.exp (-a ^ 2 / 4) * Real.exp (-(z + a / 2) ^ 2) by
    funext z
    exact hpoint z]
  rw [integral_const_mul]
  rw [mul_comm (Real.sqrt Real.pi)]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∫ z : ℝ in Set.Ioi (-a), Real.exp (-(z + a / 2) ^ 2)) ≤
          ∫ z : ℝ, Real.exp (-(z + a / 2) ^ 2) := by
            apply setIntegral_le_integral
            · have h := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)
              simpa using h.comp_add_right (a / 2)
            · exact ae_of_all _ (fun z ↦ (Real.exp_pos _).le)
      _ = ∫ z : ℝ, Real.exp (-(z ^ 2)) := by
            simpa [add_comm] using
              (integral_add_right_eq_self
                (fun z : ℝ ↦ Real.exp (-(z ^ 2))) (a / 2))
      _ = Real.sqrt Real.pi := by
            simpa using integral_gaussian 1
  · positivity

private theorem good_region_integrable_gr (a : ℝ) :
    IntegrableOn
      (fun z : ℝ ↦
        Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2)))
      (Set.Ioi (-a)) volume := by
  have hgauss := integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)
  have hshift : Integrable
      (fun z : ℝ ↦ Real.exp (-(z + a / 2) ^ 2)) volume := by
    simpa using hgauss.comp_add_right (a / 2)
  have hconst : Integrable
      (fun z : ℝ ↦ Real.exp (-a ^ 2 / 4) *
        Real.exp (-(z + a / 2) ^ 2)) volume :=
    hshift.const_mul _
  apply hconst.integrableOn.congr_fun _ measurableSet_Ioi
  intro z hz
  change Real.exp (-a ^ 2 / 4) * Real.exp (-(z + a / 2) ^ 2) =
    Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2))
  rw [← Real.exp_add]
  congr 1
  ring

private theorem exp_sq_bad_scale_gr (a : ℝ) (ha : 0 < a) :
    Real.exp (-a ^ 2 / 2) * (1 / a ^ 2 + 1 / a) ≤
      3 / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  apply (le_div_iff₀ ha2).2
  have hexple : Real.exp (-a ^ 2 / 2) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg a])
  have hcore :
      Real.exp (-a ^ 2 / 2) * (1 + a) ≤ 3 := by
    by_cases ha1 : a ≤ 1
    · nlinarith [Real.exp_pos (-a ^ 2 / 2)]
    · have haa : a ≤ a ^ 2 := by nlinarith
      have hy := Real.mul_exp_neg_le_exp_neg_one (a ^ 2 / 2)
      have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
      have hy2 :
          a ^ 2 * Real.exp (-a ^ 2 / 2) ≤ 2 := by
        have hy' :
            a ^ 2 / 2 * Real.exp (-a ^ 2 / 2) ≤ 1 := by
          simpa [neg_div] using hy.trans he1
        nlinarith [hy']
      have haexp :
          a * Real.exp (-a ^ 2 / 2) ≤ 2 := by
        exact (mul_le_mul_of_nonneg_right haa (Real.exp_pos _).le).trans hy2
      nlinarith
  have hane : a ≠ 0 := ha.ne'
  have hrew : (1 / a ^ 2 + 1 / a) * a ^ 2 = 1 + a := by
    rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hane), pow_two, ← mul_assoc,
      div_mul_cancel₀ _ hane, one_mul]
  calc Real.exp (-a ^ 2 / 2) * (1 / a ^ 2 + 1 / a) * a ^ 2
      = Real.exp (-a ^ 2 / 2) * ((1 / a ^ 2 + 1 / a) * a ^ 2) := by ring
    _ = Real.exp (-a ^ 2 / 2) * (1 + a) := by rw [hrew]
    _ ≤ 3 := hcore

private theorem exp_sq_good_scale_gr (a : ℝ) (ha : 0 < a) :
    Real.exp (-a ^ 2 / 4) ≤ 4 / a ^ 2 := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  apply (le_div_iff₀ ha2).2
  have hy := Real.mul_exp_neg_le_exp_neg_one (a ^ 2 / 4)
  have he1 : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hy' :
      a ^ 2 / 4 * Real.exp (-a ^ 2 / 4) ≤ 1 := by
    simpa [neg_div] using hy.trans he1
  nlinarith [hy']

private theorem measurable_gaussianReal_real_Ioi_std (c : ℝ) :
    Measurable (fun p : ℝ × NNReal ↦
      (gaussianReal p.1 p.2).real (Set.Ioi c)) := by
  have hpdf :
      Measurable
        (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) := by
    rw [show
      (fun p : (ℝ × NNReal) × ℝ ↦ gaussianPDF p.1.1 p.1.2 p.2) =
        fun p ↦ ENNReal.ofReal
          ((Real.sqrt (2 * Real.pi * (p.1.2 : ℝ)))⁻¹ *
            Real.exp (-((p.2 - p.1.1) ^ 2) / (2 * (p.1.2 : ℝ)))) by
      funext p
      rfl]
    fun_prop
  have hint :
      Measurable
        (fun p : ℝ × NNReal ↦
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal) := by
    apply Measurable.ennreal_toReal
    have hrestricted :
        Measurable
          (fun z : (ℝ × NNReal) × ℝ ↦
            (Set.Ioi c).indicator
              (fun x ↦ gaussianPDF z.1.1 z.1.2 x) z.2) :=
      hpdf.indicator
        (measurableSet_Ioi.preimage measurable_snd)
    simpa only [lintegral_indicator measurableSet_Ioi] using
      (hrestricted.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have hzero :
      Measurable
        (fun p : ℝ × NNReal ↦ if c < p.1 then (1 : ℝ) else 0) :=
    Measurable.ite
      (measurableSet_lt measurable_const measurable_fst)
      measurable_const measurable_const
  have heq :
      (fun p : ℝ × NNReal ↦
        (gaussianReal p.1 p.2).real (Set.Ioi c)) =
        fun p ↦ if p.2 = 0 then
          (if c < p.1 then 1 else 0)
        else
          (∫⁻ x in Set.Ioi c, gaussianPDF p.1 p.2 x).toReal := by
    funext p
    by_cases hp : p.2 = 0
    · rw [if_pos hp, hp, gaussianReal_zero_var]
      by_cases hc : c < p.1 <;>
        simp [Measure.real, Set.indicator, hc]
    · rw [if_neg hp, Measure.real, gaussianReal_apply p.1 hp]
  rw [heq]
  exact Measurable.ite
    ((measurableSet_singleton (0 : NNReal)).preimage measurable_snd)
    hzero hint

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 < a →
        (∫⁻ z, ENNReal.ofReal
            (1 / (gaussianReal z 1).real {x | -a < x} - 1)
            ∂gaussianReal 0 1) ≤
          ENNReal.ofReal (C / a ^ 2) := by
  obtain ⟨c, hc, hmills⟩ := standardGaussian_mills_lower_bound
  let r : ℝ := Real.sqrt (2 * Real.pi)
  let kb : ℝ := 1 / (r * c)
  let kg : ℝ := 2 / r
  let C : ℝ := 3 * kb + 4 * kg * Real.sqrt Real.pi
  have hr : 0 < r := by dsimp [r]; positivity
  have hkb : 0 < kb := by dsimp [kb]; positivity
  have hkg : 0 < kg := by dsimp [kg]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro a ha
  let R : ℝ → ℝ := fun z ↦
    1 / (gaussianReal z 1).real (Set.Ioi (-a)) - 1
  have hRmeas : Measurable R := by
    dsimp [R]
    exact (measurable_const.div
      ((measurable_gaussianReal_real_Ioi_std (-a)).comp
        (measurable_id.prodMk measurable_const))).sub_const 1
  have hbadpoint (z : ℝ) (hz : z ∈ Set.Iic (-a)) :
      gaussianPDF 0 1 z * ENNReal.ofReal (R z) ≤
        ENNReal.ofReal
          (kb * ((1 - a - z) *
            Real.exp (a ^ 2 / 2 + a * z))) := by
    have hu : 0 ≤ -a - z := by
      change z ≤ -a at hz
      linarith
    have hratio := reciprocal_ratio_bad_check c hc hmills (-a - z) hu
    have hshift := shifted_tail_check z a
    rw [← hshift] at hratio
    change ENNReal.ofReal (gaussianPDFReal 0 1 z) *
        ENNReal.ofReal (R z) ≤ _
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 z)]
    apply ENNReal.ofReal_le_ofReal
    calc
      gaussianPDFReal 0 1 z * R z ≤
          gaussianPDFReal 0 1 z *
            (((-a - z + 1) / c) *
              Real.exp ((-a - z) ^ 2 / 2)) := by
            exact mul_le_mul_of_nonneg_left hratio
              (gaussianPDFReal_nonneg 0 1 z)
      _ = kb * ((1 - a - z) *
            Real.exp (a ^ 2 / 2 + a * z)) := by
            rw [gaussianPDFReal]
            simp only [NNReal.coe_one, mul_one, sub_zero]
            dsimp [kb, r]
            have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
            have hc0 : c ≠ 0 := hc.ne'
            calc
              (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) *
                    (((-a - z + 1) / c) *
                      Real.exp ((-a - z) ^ 2 / 2)) =
                  1 / (Real.sqrt (2 * Real.pi) * c) *
                    ((1 - a - z) *
                      (Real.exp (-z ^ 2 / 2) *
                        Real.exp ((-a - z) ^ 2 / 2))) := by
                    field_simp
                    ring
              _ = 1 / (Real.sqrt (2 * Real.pi) * c) *
                    ((1 - a - z) *
                      Real.exp (a ^ 2 / 2 + a * z)) := by
                    rw [← Real.exp_add]
                    congr 3
                    ring
  have hgoodpoint (z : ℝ) (hz : z ∈ Set.Ioi (-a)) :
      gaussianPDF 0 1 z * ENNReal.ofReal (R z) ≤
        ENNReal.ofReal
          (kg * Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2))) := by
    have hu : -a - z < 0 := by
      change -a < z at hz
      linarith
    have hratio := reciprocal_ratio_good_check (-a - z) hu
    have hshift := shifted_tail_check z a
    rw [← hshift] at hratio
    change ENNReal.ofReal (gaussianPDFReal 0 1 z) *
        ENNReal.ofReal (R z) ≤ _
    rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 z)]
    apply ENNReal.ofReal_le_ofReal
    calc
      gaussianPDFReal 0 1 z * R z ≤
          gaussianPDFReal 0 1 z *
            (2 * Real.exp (-(-(-a - z)) ^ 2 / 2)) := by
              exact mul_le_mul_of_nonneg_left hratio
                (gaussianPDFReal_nonneg 0 1 z)
      _ = kg * Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2)) := by
            rw [gaussianPDFReal]
            simp only [NNReal.coe_one, mul_one, sub_zero]
            dsimp [kg, r]
            have hsqrt : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
            calc
              (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) *
                    (2 * Real.exp (-(-(-a - z)) ^ 2 / 2)) =
                  2 / Real.sqrt (2 * Real.pi) *
                    (Real.exp (-z ^ 2 / 2) *
                      Real.exp (-(-(-a - z)) ^ 2 / 2)) := by
                    field_simp
              _ = 2 / Real.sqrt (2 * Real.pi) *
                    Real.exp (-(((a + z) ^ 2 + z ^ 2) / 2)) := by
                    rw [← Real.exp_add]
                    congr 2
                    ring
  change (∫⁻ z, ENNReal.ofReal (R z) ∂gaussianReal 0 1) ≤
    ENNReal.ofReal (C / a ^ 2)
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num)]
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gaussianPDF 0 1) hRmeas.ennreal_ofReal]
  change (∫⁻ z,
    gaussianPDF 0 1 z * ENNReal.ofReal (R z) ∂volume) ≤
      ENNReal.ofReal (C / a ^ 2)
  rw [← lintegral_add_compl
    (μ := volume)
    (fun z ↦ gaussianPDF 0 1 z * ENNReal.ofReal (R z))
    measurableSet_Iic]
  rw [show (Set.Iic (-a))ᶜ = Set.Ioi (-a) by ext z; simp]
  have hbad :
      (∫⁻ z in Set.Iic (-a),
          gaussianPDF 0 1 z * ENNReal.ofReal (R z) ∂volume) ≤
        ENNReal.ofReal
          (kb * (Real.exp (-a ^ 2 / 2) *
            (1 / a ^ 2 + 1 / a))) := by
    calc
      (∫⁻ z in Set.Iic (-a),
          gaussianPDF 0 1 z * ENNReal.ofReal (R z) ∂volume) ≤
          ∫⁻ z in Set.Iic (-a), ENNReal.ofReal
            (kb * ((1 - a - z) *
              Real.exp (a ^ 2 / 2 + a * z))) ∂volume := by
            exact setLIntegral_mono' measurableSet_Iic hbadpoint
      _ = ENNReal.ofReal
          (∫ z in Set.Iic (-a),
            kb * ((1 - a - z) *
              Real.exp (a ^ 2 / 2 + a * z)) ∂volume) := by
            symm
            apply ofReal_integral_eq_lintegral_ofReal
            · exact (bad_region_integrable_gr a ha).const_mul kb
            · filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
              have hz' : z ≤ -a := hz
              have : 0 ≤ 1 - a - z := by linarith
              positivity
      _ = ENNReal.ofReal
          (kb * (Real.exp (-a ^ 2 / 2) *
            (1 / a ^ 2 + 1 / a))) := by
            rw [integral_const_mul, bad_region_integral_gr a ha]
  have hgood :
      (∫⁻ z in Set.Ioi (-a),
          gaussianPDF 0 1 z * ENNReal.ofReal (R z) ∂volume) ≤
        ENNReal.ofReal
          (kg * (Real.sqrt Real.pi *
            Real.exp (-a ^ 2 / 4))) := by
    calc
      (∫⁻ z in Set.Ioi (-a),
          gaussianPDF 0 1 z * ENNReal.ofReal (R z) ∂volume) ≤
          ∫⁻ z in Set.Ioi (-a), ENNReal.ofReal
            (kg * Real.exp
              (-(((a + z) ^ 2 + z ^ 2) / 2))) ∂volume := by
            exact setLIntegral_mono' measurableSet_Ioi hgoodpoint
      _ = ENNReal.ofReal
          (∫ z in Set.Ioi (-a),
            kg * Real.exp
              (-(((a + z) ^ 2 + z ^ 2) / 2)) ∂volume) := by
            symm
            apply ofReal_integral_eq_lintegral_ofReal
            · exact (good_region_integrable_gr a).const_mul kg
            · exact ae_of_all _ (fun z ↦ by positivity)
      _ = ENNReal.ofReal
          (kg * (∫ z in Set.Ioi (-a),
            Real.exp
              (-(((a + z) ^ 2 + z ^ 2) / 2)) ∂volume)) := by
            rw [integral_const_mul]
      _ ≤ ENNReal.ofReal
          (kg * (Real.sqrt Real.pi *
            Real.exp (-a ^ 2 / 4))) := by
            apply ENNReal.ofReal_le_ofReal
            gcongr
            exact good_region_integral_gr a
  apply (add_le_add hbad hgood).trans
  have hbadscale :
      kb * (Real.exp (-a ^ 2 / 2) *
        (1 / a ^ 2 + 1 / a)) ≤ kb * (3 / a ^ 2) :=
    mul_le_mul_of_nonneg_left (exp_sq_bad_scale_gr a ha) hkb.le
  have hgoodscale :
      (kg * Real.sqrt Real.pi) * Real.exp (-a ^ 2 / 4) ≤
        (kg * Real.sqrt Real.pi) * (4 / a ^ 2) :=
    mul_le_mul_of_nonneg_left (exp_sq_good_scale_gr a ha)
      (mul_nonneg hkg.le (Real.sqrt_nonneg Real.pi))
  have hA :
      0 ≤ kb * (Real.exp (-a ^ 2 / 2) *
        (1 / a ^ 2 + 1 / a)) := by
    have hsum : 0 ≤ 1 / a ^ 2 + 1 / a := by positivity
    positivity
  have hB :
      0 ≤ kg * (Real.sqrt Real.pi *
        Real.exp (-a ^ 2 / 4)) := by positivity
  rw [← ENNReal.ofReal_add hA hB]
  apply ENNReal.ofReal_le_ofReal
  dsimp [C]
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  calc
    kb * (Real.exp (-a ^ 2 / 2) * (1 / a ^ 2 + 1 / a)) +
          kg * (Real.sqrt Real.pi * Real.exp (-a ^ 2 / 4)) ≤
        kb * (3 / a ^ 2) +
          (kg * Real.sqrt Real.pi) * (4 / a ^ 2) := by
            exact add_le_add hbadscale
              (by simpa [mul_assoc] using hgoodscale)
    _ = (3 * kb + 4 * kg * Real.sqrt Real.pi) / a ^ 2 := by
          field_simp
