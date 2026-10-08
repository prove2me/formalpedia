-- Prove2me | solution 1 for CoulombGauss.divergence_electricField_eq_zero_of_not_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T02:05:32.895781+00:00
-- url     : https://prove2.me/submissions/dab73057-f501-4d70-aa48-5c5cc695e713

import Mathlib
import Definitions.Def_CoulombGauss_basic
open MeasureTheory Filter Topology Metric

set_option autoImplicit false

namespace CoulombGauss

/-- Explicit derivative of `y ↦ |y|⁻³ y`. -/
noncomputable def kL_533f (y : Vec3) : Vec3 →L[ℝ] Vec3 :=
  (‖y‖ ^ 3)⁻¹ • ContinuousLinearMap.id ℝ Vec3
    - (3 * ‖y‖ * ((‖y‖ ^ 3) ^ 2)⁻¹) • (innerSL ℝ y).smulRight y

lemma hasFDerivAt_k_533f (y : Vec3) (hy : y ≠ 0) :
    HasFDerivAt (fun z : Vec3 => (‖z‖ ^ 3)⁻¹ • z) (kL_533f y) y := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hN3 : ‖y‖ ^ 3 ≠ 0 := pow_ne_zero 3 hn
  have h1 := hasFDerivAt_norm_rpow y (p := 3) (by norm_num)
  have e : (fun x : Vec3 => ‖x‖ ^ (3:ℝ)) = fun x => ‖x‖ ^ 3 := by
    funext x
    exact_mod_cast Real.rpow_natCast ‖x‖ 3
  rw [e] at h1
  have hg := (hasFDerivAt_inv hN3).comp y h1
  have hs := hg.smul (hasFDerivAt_id y)
  have h32 : ‖y‖ ^ ((3:ℝ) - 2) = ‖y‖ := by norm_num
  refine hs.congr_fderiv ?_
  ext1 h
  simp only [kL_533f, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply, h32, id]
  simp
  module

lemma norm_kL_533f (y : Vec3) (hy : y ≠ 0) : ‖kL_533f y‖ ≤ 4 * (‖y‖ ^ 3)⁻¹ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  unfold kL_533f
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hid : ‖ContinuousLinearMap.id ℝ Vec3‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have a1 : ‖(‖y‖ ^ 3)⁻¹‖ * ‖ContinuousLinearMap.id ℝ Vec3‖ ≤ (‖y‖ ^ 3)⁻¹ := by
    rw [Real.norm_of_nonneg (by positivity)]
    calc (‖y‖ ^ 3)⁻¹ * ‖ContinuousLinearMap.id ℝ Vec3‖ ≤ (‖y‖ ^ 3)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  have a2 : ‖3 * ‖y‖ * ((‖y‖ ^ 3) ^ 2)⁻¹‖ * (‖y‖ * ‖y‖) = 3 * (‖y‖ ^ 3)⁻¹ := by
    rw [Real.norm_of_nonneg (by positivity)]
    field_simp
  linarith

lemma trace_kL_533f (y : Vec3) (hy : y ≠ 0) :
    ∑ i : Fin 3, kL_533f y (EuclideanSpace.single i 1) i = 0 := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  simp only [kL_533f, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, Fin.sum_univ_three]
  simp
  have hs := EuclideanSpace.real_norm_sq_eq y
  rw [Fin.sum_univ_three] at hs
  have e2 : ∀ a b c n : ℝ, n ≠ 0 → n ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 →
      ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (a * a))
        + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (b * b))
        + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (c * c)) = 0 := by
    intro a b c n hn0 hsum
    have : a ^ 2 + b ^ 2 + c ^ 2 = n ^ 2 := hsum.symm
    have h' : ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (a * a))
        + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (b * b))
        + ((n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (c * c))
        = 3 * (n ^ 3)⁻¹ - 3 * n * ((n ^ 3) ^ 2)⁻¹ * (a ^ 2 + b ^ 2 + c ^ 2) := by ring
    rw [h', this]
    field_simp
    ring
  linarith [e2 _ _ _ _ hn hs]

lemma continuousAt_kL_533f (y : Vec3) (hy : y ≠ 0) : ContinuousAt kL_533f y := by
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have hc3 : ContinuousAt (fun z : Vec3 => (‖z‖ ^ 3)⁻¹) y :=
    ((continuous_norm.pow 3).continuousAt).inv₀ (pow_ne_zero 3 hn)
  have hc6 : ContinuousAt (fun z : Vec3 => ((‖z‖ ^ 3) ^ 2)⁻¹) y :=
    (((continuous_norm.pow 3).pow 2).continuousAt).inv₀ (pow_ne_zero 2 (pow_ne_zero 3 hn))
  have hsr : Continuous (fun z : Vec3 => (innerSL ℝ z).smulRight z) := by
    have : (fun z : Vec3 => (innerSL ℝ z).smulRight z)
        = fun z => ContinuousLinearMap.smulRightL ℝ Vec3 Vec3 (innerSL ℝ z) z := rfl
    rw [this]
    fun_prop
  unfold kL_533f
  apply ContinuousAt.sub
  · exact hc3.smul continuousAt_const
  · exact ((continuousAt_const.mul continuous_norm.continuousAt).mul hc6).smul hsr.continuousAt

lemma kernel_bound_533f (y : Vec3) (δ : ℝ) (hδ : 0 < δ) (h : δ ≤ ‖y‖) :
    ‖(‖y‖ ^ 3)⁻¹ • y‖ ≤ (δ ^ 2)⁻¹ := by
  have hn : 0 < ‖y‖ := lt_of_lt_of_le hδ h
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have : (‖y‖ ^ 3)⁻¹ * ‖y‖ = (‖y‖ ^ 2)⁻¹ := by field_simp
  rw [this]
  gcongr

end CoulombGauss

open CoulombGauss MeasureTheory Filter Topology Metric in
theorem solution (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (ρ : Vec3 → ℝ) (S : Set Vec3) (hS : MeasurableSet S) (hρ : IntegrableOn ρ S)
    (r : Vec3) (hr : r ∉ closure S) :
    DifferentiableAt ℝ (electricField ε₀ ρ S) r ∧
      divergence (electricField ε₀ ρ S) r = 0 := by
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl r hr
  set δ := ε / 2 with hδ
  have δpos : 0 < δ := by positivity
  have hfar : ∀ x ∈ ball r δ, ∀ r' ∈ S, δ ≤ ‖x - r'‖ := by
    intro x hx r' hr'
    have h1 : r' ∉ ball r ε := fun h => hball h (subset_closure hr')
    rw [mem_ball, not_lt] at h1
    rw [mem_ball] at hx
    have := dist_triangle r' x r
    rw [← dist_eq_norm, dist_comm]
    linarith
  have hne : ∀ x ∈ ball r δ, ∀ r' ∈ S, x - r' ≠ 0 := by
    intro x hx r' hr' h0
    have := hfar x hx r' hr'
    rw [h0, norm_zero] at this
    linarith
  have hae : ∀ᵐ r' ∂(volume.restrict S), r' ∈ S := ae_restrict_mem hS
  have hρm : AEStronglyMeasurable ρ (volume.restrict S) := hρ.aestronglyMeasurable
  have hKm : ∀ x : Vec3, Measurable (fun r' : Vec3 => coulombKernel x r') := by
    intro x
    unfold coulombKernel
    fun_prop
  have hFm : ∀ x : Vec3,
      AEStronglyMeasurable (fun r' => ρ r' • coulombKernel x r') (volume.restrict S) :=
    fun x => hρm.smul (hKm x).aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (fun r' => ρ r' • kL_533f (r - r')) (volume.restrict S) := by
    refine hρm.smul (ContinuousOn.aestronglyMeasurable ?_ hS)
    intro r' hr'
    apply ContinuousAt.continuousWithinAt
    exact (continuousAt_kL_533f _ (hne r (mem_ball_self δpos) r' hr')).comp
      (continuousAt_const.sub continuousAt_id)
  have hbound : ∀ᵐ r' ∂(volume.restrict S), ∀ x ∈ ball r δ,
      ‖ρ r' • kL_533f (x - r')‖ ≤ ‖ρ r'‖ * (4 * (δ ^ 3)⁻¹) := by
    filter_upwards [hae] with r' hr' x hx
    rw [norm_smul]
    gcongr
    refine (norm_kL_533f _ (hne x hx r' hr')).trans ?_
    have := hfar x hx r' hr'
    gcongr
  have hbint : Integrable (fun r' => ‖ρ r'‖ * (4 * (δ ^ 3)⁻¹)) (volume.restrict S) :=
    hρ.norm.mul_const _
  have hFint : Integrable (fun r' => ρ r' • coulombKernel r r') (volume.restrict S) := by
    refine Integrable.mono' (hρ.norm.mul_const ((δ ^ 2)⁻¹)) (hFm r) ?_
    filter_upwards [hae] with r' hr'
    rw [norm_smul]
    gcongr
    exact kernel_bound_533f _ δ δpos (hfar r (mem_ball_self δpos) r' hr')
  have hdiff : ∀ᵐ r' ∂(volume.restrict S), ∀ x ∈ ball r δ,
      HasFDerivAt (fun x => ρ r' • coulombKernel x r') (ρ r' • kL_533f (x - r')) x := by
    filter_upwards [hae] with r' hr' x hx
    have h := (hasFDerivAt_k_533f _ (hne x hx r' hr')).comp x
      ((hasFDerivAt_id x).sub_const r')
    rw [ContinuousLinearMap.comp_id] at h
    exact h.const_smul (ρ r')
  have hD := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x r' => ρ r' • coulombKernel x r')
    (F' := fun x r' => ρ r' • kL_533f (x - r'))
    (ball_mem_nhds r δpos) (Eventually.of_forall hFm) hFint hF'm hbound hbint hdiff
  have hE : HasFDerivAt (electricField ε₀ ρ S)
      ((1 / (4 * Real.pi * ε₀)) •
        ∫ r', ρ r' • kL_533f (r - r') ∂(volume.restrict S)) r :=
    hD.const_smul (1 / (4 * Real.pi * ε₀))
  refine ⟨hE.differentiableAt, ?_⟩
  have hF'int : Integrable (fun r' => ρ r' • kL_533f (r - r')) (volume.restrict S) := by
    refine Integrable.mono' hbint hF'm ?_
    filter_upwards [hbound] with r' h
    exact h r (mem_ball_self δpos)
  let T : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ := ∑ i : Fin 3,
    (EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i (1:ℝ)))
  have hT : ∀ A : Vec3 →L[ℝ] Vec3, T A = ∑ i : Fin 3, A (EuclideanSpace.single i 1) i := by
    intro A
    simp [T]
  have hdiv : divergence (electricField ε₀ ρ S) r
      = T ((1 / (4 * Real.pi * ε₀)) •
        ∫ r', ρ r' • kL_533f (r - r') ∂(volume.restrict S)) := by
    unfold divergence
    rw [hT]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hc := ((EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ).hasFDerivAt).comp r hE
    rw [show (fun x => (electricField ε₀ ρ S x).ofLp i)
        = ⇑(EuclideanSpace.proj i : Vec3 →L[ℝ] ℝ) ∘ electricField ε₀ ρ S from rfl, hc.fderiv]
    rfl
  rw [hdiv, map_smul, ← T.integral_comp_comm hF'int]
  have h0 : ∫ r', T (ρ r' • kL_533f (r - r')) ∂(volume.restrict S) = 0 := by
    rw [← integral_zero Vec3 ℝ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with r' hr'
    rw [map_smul, hT, trace_kL_533f _ (hne r (mem_ball_self δpos) r' hr')]
    simp
  rw [h0, smul_zero]
