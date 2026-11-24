-- Prove2me | solution 1 for DimdPolyLEAN.constantCenter_fastRotate_carrierArc_sq_le_defectSq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:57.424989+00:00
-- url     : https://prove2.me/submissions/e9702d02-cdfe-4b36-8620-a23cbe171433

module
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Definitions
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_RotationalAveraging
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Theorems.Thm_DimdPolyLEAN_carrierArc_length
public import Theorems.Thm_DimdPolyLEAN_carrierArc_left_lt_right
public import Theorems.Thm_DimdPolyLEAN_arcLength_nonneg
public import Theorems.Thm_DimdPolyLEAN_carrierArc_arcIntegral_eq_mk_image_Ioc
public import Theorems.Thm_DimdPolyLEAN_carrierArc_mk_image_Ioc_integral_eq_scaled
public import Theorems.Thm_DimdPolyLEAN_circleChar_eq_fourier_nat
public import Theorems.Thm_FockSPR_rotational_averaging_bound

section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
private theorem rotational_averaging_bound_complex (q : ℂ) :
    ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        ∂AddCircle.haarAddCircle ≥
      ‖q‖ ^ 2 / 8 := by
  by_cases hq : q = 0
  · simp [hq, FockSPR.rho, norm_zero]
  · set r := ‖q‖
    have hr_pos : 0 < r := norm_pos_iff.mpr hq
    set α := (r : ℂ)⁻¹ * q
    have hα_norm : ‖α‖ = 1 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr_pos]
      exact inv_mul_cancel₀ (ne_of_gt hr_pos)
    have h_rw : ∀ t : Circle,
        (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((r : ℂ) * ((fourier (1 : ℤ) t : ℂ) * α))) ^ 2 := by
      intro t
      congr 2
      show (fourier (1 : ℤ) t : ℂ) * q =
        ↑r * ((fourier (1 : ℤ) t : ℂ) * α)
      simp only [α]
      have hr_ne' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      field_simp
    simp_rw [h_rw]
    have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    obtain ⟨s, hs⟩ := (AddCircle.homeomorphCircle hT_ne).surjective
      ⟨α, by
        rw [← SetLike.mem_coe, Submonoid.coe_unitSphere,
          Metric.mem_sphere, dist_zero_right]
        exact hα_norm⟩
    rw [AddCircle.homeomorphCircle_apply] at hs
    have hα_eq : (fourier (1 : ℤ) s : ℂ) = α := by
      simp only [fourier_apply, one_zsmul]
      exact congr_arg Subtype.val hs
    have h_shift : ∀ t : Circle,
        (fourier (1 : ℤ) t : ℂ) * α = fourier (1 : ℤ) (t + s) := by
      intro t
      rw [← hα_eq]
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    simp_rw [h_shift]
    set F : Circle → ℝ :=
      fun u => (FockSPR.rho ((r : ℂ) * fourier (1 : ℤ) u)) ^ 2
    change ∫ t, F (t + s) ∂AddCircle.haarAddCircle ≥ r ^ 2 / 8
    simp_rw [show ∀ t : Circle, t + s = s + t from fun t => add_comm t s]
    rw [MeasureTheory.integral_add_left_eq_self]
    exact FockSPR.rotational_averaging_bound (r := r) (norm_nonneg q)
private theorem carrierArc_interval_rho_sq_eq_full_circle
    {N : Nat} (k : Fin N) (q : ℂ) :
    ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
      (N : ℝ)⁻¹ * ((2 * Real.pi) *
        ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
          ∂AddCircle.haarAddCircle) := by
  have hT_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr k.pos
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have fourier_rescale : ∀ s : ℝ,
      circleChar N (QuotientAddGroup.mk (s / ↑N) : Circle) =
      fourier (1 : ℤ) (QuotientAddGroup.mk s : Circle) := by
    intro s
    rw [circleChar_eq_fourier_nat]
    simp only [fourier_coe_apply]
    congr 1
    have hN_complex : (↑N : ℂ) ≠ 0 := by exact_mod_cast hN_ne
    have hT_complex : (↑(2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast hT_ne
    push_cast
    field_simp [hN_complex, hT_complex]
  set g : ℝ → ℝ := fun t =>
    (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2
  have h_eq_haar_int :
      ∫ t in (carrierArc N k).left..(carrierArc N k).right, g t =
        (↑N : ℝ)⁻¹ * ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
    have key := intervalIntegral.integral_comp_mul_left
      (fun s => g (s / ↑N)) hN_ne
      (a := (carrierArc N k).left) (b := (carrierArc N k).right)
    have h_simp : (fun x => g ((↑N : ℝ) * x / ↑N)) = g := by
      ext x
      show g (↑N * x / ↑N) = g x
      congr 1
      field_simp [hN_ne]
    rw [h_simp] at key
    have h_el : (↑N : ℝ) * (carrierArc N k).left =
        (2 * Real.pi) * ↑k.val := by
      unfold carrierArc
      field_simp [hN_ne]
    have h_er : (↑N : ℝ) * (carrierArc N k).right =
        (2 * Real.pi) * (↑k.val + 1) := by
      unfold carrierArc
      push_cast
      field_simp [hN_ne]
    rw [h_el, h_er] at key
    rw [key, smul_eq_mul]
    congr 1
    have h_congr :
        ∀ s ∈ Set.uIcc ((2 * Real.pi) * ↑k.val)
            ((2 * Real.pi) * (↑k.val + 1)),
          g (s / ↑N) =
            (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2 := by
      intro s _
      change (FockSPR.rho (circleChar N (↑(s / ↑N) : Circle) * q)) ^ 2 = _
      rw [fourier_rescale]
    rw [intervalIntegral.integral_congr h_congr]
    set g₁ : ℝ → ℝ := fun s =>
      (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
    have hg₁_periodic : Function.Periodic g₁ (2 * Real.pi) := by
      intro s
      change (FockSPR.rho
          ((fourier (1 : ℤ) (↑(s + 2 * Real.pi) : Circle) : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
      simp only [QuotientAddGroup.mk_add_of_mem _
        (AddSubgroup.mem_zmultiples (2 * Real.pi))]
    rw [show (2 * Real.pi) * (↑k.val + 1) =
        (2 * Real.pi) * ↑k.val + (2 * Real.pi) by ring]
    rw [hg₁_periodic.intervalIntegral_add_eq ((2 * Real.pi) * ↑k.val) 0]
    have h_preimage := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    have h_haar := @AddCircle.integral_haarAddCircle (2 * Real.pi) _ ℝ _ _
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    calc ∫ x in (0 : ℝ)..(0 + 2 * Real.pi), g₁ x
        = ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 :=
          h_preimage
      _ = (2 * Real.pi) *
          ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle := by
        rw [h_haar, smul_eq_mul]
        set V := ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        rw [mul_comm (2 * Real.pi) ((2 * Real.pi)⁻¹ * V), mul_assoc,
          mul_comm V (2 * Real.pi), ← mul_assoc, inv_mul_cancel₀ hT_ne, one_mul]
  exact h_eq_haar_int
private theorem carrierArc_interval_rho_sq_lower
    {N : Nat} (k : Fin N) (q : ℂ) :
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
      ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  rw [carrierArc_interval_rho_sq_eq_full_circle k q]
  calc
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8
        = (N : ℝ)⁻¹ * ((2 * Real.pi) * (‖q‖ ^ 2 / 8)) := by
          rw [carrierArc_length k]
          field_simp [hN_ne]
    _ <= (N : ℝ)⁻¹ *
        ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hN_pos))
      exact mul_le_mul_of_nonneg_left (rotational_averaging_bound_complex q).le (by positivity)
private lemma constant_center_defect_eq_norm_sq_rho
    {c u z : ℂ} (hc : c ≠ 0) :
    (‖c + z * u‖ - ‖c‖) ^ 2 =
      ‖c‖ ^ 2 * (FockSPR.rho (z * (u / c))) ^ 2 := by
  have hfactor : c + z * u = c * (1 + z * (u / c)) := by field_simp [hc]
  rw [hfactor, norm_mul]
  unfold FockSPR.rho
  rw [sq_abs]
  ring
private theorem carrierArc_setIntegral_constant_center_lower
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <=
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
  set q : ℂ := u / c
  have h_interval' :
      arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [← intervalIntegral.integral_of_le (le_of_lt (carrierArc_left_lt_right k))]
    exact carrierArc_interval_rho_sq_lower k q
  have hconst :
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          ‖c‖ ^ 2 *
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
        ‖c‖ ^ 2 *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  have hscale :
      ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) =
        arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    dsimp [q]
    rw [norm_div]
    have hc_norm_ne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    field_simp [hc_norm_ne]
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8
        = ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) := hscale.symm
    _ <= ‖c‖ ^ 2 *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 :=
      mul_le_mul_of_nonneg_left h_interval' (sq_nonneg ‖c‖)
    _ = ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
      rw [← hconst]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simpa only [q] using
        (constant_center_defect_eq_norm_sq_rho
          (c := c) (u := u) (z := circleChar N (QuotientAddGroup.mk t : Circle)) hc).symm
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace DimdPolyLEAN
theorem _root_.solution
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
      Crot *
        arcIntegral (carrierArc N k)
          (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2) := by
  let f : Circle -> ℝ := fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2
  have hrewrite :
      arcIntegral (carrierArc N k) f =
        (2 * Real.pi)⁻¹ *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            f (QuotientAddGroup.mk t : Circle) := by
    rw [carrierArc_arcIntegral_eq_mk_image_Ioc k f]
    exact carrierArc_mk_image_Ioc_integral_eq_scaled k f
  rw [hrewrite]
  set J : ℝ :=
    ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
      f (QuotientAddGroup.mk t : Circle)
  have hJ_lower : arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <= J := by
    dsimp [J, f]
    exact carrierArc_setIntegral_constant_center_lower k hc
  have hleft_nonneg :
      0 <= arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      arcLength_nonneg (carrierArc N k)
    have hnorm_nonneg : 0 <= ‖u‖ ^ 2 := sq_nonneg ‖u‖
    nlinarith only [hlen_nonneg]
  have hJ_nonneg : 0 <= J := le_trans hleft_nonneg hJ_lower
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2
        = 8 * (arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8) := by ring
    _ <= 8 * J := by exact mul_le_mul_of_nonneg_left hJ_lower (by norm_num)
    _ <= 32 * J := by linarith only [hJ_lower, hleft_nonneg]
    _ = Crot * ((2 * Real.pi)⁻¹ * J) := by
      unfold Crot
      have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hpi_ne]
      ring
end DimdPolyLEAN
