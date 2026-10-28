-- Prove2me | solution 1 for EntropicBarrier.Universal.nuBound_iff_covariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T09:31:20.520005+00:00
-- url     : https://prove2.me/submissions/fa98e5c7-7688-4acc-b5d6-cb65948c120f

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_EntropicBarrier
import Definitions.Def_ConvexOptimization_selfConcordance
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_EntropicBarrier_Universal_ExpFamily

set_option autoImplicit false

open scoped RealInnerProductSpace
open MeasureTheory Filter Topology Metric

namespace EB39

open EntropicBarrier.Universal

/-! ## S1: differentiation of parametric integrals over a compact set -/

theorem cont_slice {n : ℕ} {G : Type*} [TopologicalSpace G]
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → G)
    (hF : Continuous (Function.uncurry F)) (θ : EuclideanSpace ℝ (Fin n)) :
    Continuous (F θ) :=
  hF.comp (continuous_const.prodMk continuous_id)

theorem hasFDerivAt_setIntegral {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → G)
    (F' : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] G))
    (hF : Continuous (Function.uncurry F)) (hF' : Continuous (Function.uncurry F'))
    (hd : ∀ θ x, HasFDerivAt (F · x) (F' θ x) θ) (θ0 : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun θ => ∫ x in K, F θ x) (∫ x in K, F' θ0 x) θ0 := by
  obtain ⟨C, hC⟩ := ((isCompact_closedBall θ0 1).prod hK).bddAbove_image hF'.norm.continuousOn
  have hfin : volume K < ⊤ := hK.measure_lt_top
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (s := closedBall θ0 1) (closedBall_mem_nhds θ0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun θ => (cont_slice F hF θ).aestronglyMeasurable
  · exact (cont_slice F hF θ0).continuousOn.integrableOn_compact hK
  · exact (cont_slice F' hF' θ0).aestronglyMeasurable
  · refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx θ hθ => ?_)
    exact hC (Set.mem_image_of_mem _ (Set.mk_mem_prod hθ hx))
  · exact integrable_const C
  · exact Eventually.of_forall fun x θ _ => hd θ x

theorem continuous_setIntegral {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → G)
    (hF : Continuous (Function.uncurry F)) :
    Continuous (fun θ => ∫ x in K, F θ x) :=
  continuous_parametric_integral_of_continuous hF hK

/-! ## S2: the moments -/

noncomputable def Zf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ x in K, Real.exp ⟪θ, x⟫

noncomputable def Mf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∫ x in K, Real.exp ⟪θ, x⟫ • x

noncomputable def Qf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ∫ x in K, (Real.exp ⟪θ, x⟫ • innerSL ℝ x).smulRight x

theorem hasFDerivAt_expInner {n : ℕ} (x θ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫)
      (Real.exp ⟪θ, x⟫ • innerSL ℝ x) θ := by
  have h2 := ((innerSL ℝ x).hasFDerivAt (x := θ)).exp
  have e1 : (fun θ : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫) =
      fun y => Real.exp (innerSL ℝ x y) := by
    ext y; rw [real_inner_comm]; rfl
  have e2 : Real.exp ⟪θ, x⟫ = Real.exp (innerSL ℝ x θ) := by rw [real_inner_comm]; rfl
  rw [e1, e2]
  exact h2

theorem cont_expInner {n : ℕ} :
    Continuous (Function.uncurry fun (θ x : EuclideanSpace ℝ (Fin n)) => Real.exp ⟪θ, x⟫) := by
  unfold Function.uncurry; fun_prop

theorem cont_expInner_smul {n : ℕ} :
    Continuous (Function.uncurry
      fun (θ x : EuclideanSpace ℝ (Fin n)) => Real.exp ⟪θ, x⟫ • x) := by
  unfold Function.uncurry; fun_prop

theorem cont_expInner_innerSL {n : ℕ} :
    Continuous (Function.uncurry
      fun (θ x : EuclideanSpace ℝ (Fin n)) => Real.exp ⟪θ, x⟫ • innerSL ℝ x) := by
  unfold Function.uncurry; fun_prop

theorem cont_Qint {n : ℕ} :
    Continuous (Function.uncurry
      fun (θ x : EuclideanSpace ℝ (Fin n)) => (Real.exp ⟪θ, x⟫ • innerSL ℝ x).smulRight x) := by
  have h1 := (cont_expInner_innerSL (n := n))
  have h2 : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.2) :=
    continuous_snd
  exact ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))).continuous₂.comp (h1.prodMk h2))

theorem hasFDerivAt_Zf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (Zf K) (innerSL ℝ (Mf K θ)) θ := by
  have h := hasFDerivAt_setIntegral hK _ _ cont_expInner cont_expInner_innerSL
    (fun θ x => hasFDerivAt_expInner x θ) θ
  have hint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫ • x) K :=
    (cont_slice _ cont_expInner_smul θ).continuousOn.integrableOn_compact hK
  have heq : (∫ x in K, Real.exp ⟪θ, x⟫ • innerSL ℝ x) = innerSL ℝ (Mf K θ) := by
    unfold Mf
    rw [← (innerSL ℝ).integral_comp_comm hint]
    congr 1; ext x y; simp only [map_smul]
  rw [heq] at h
  exact h

theorem hasFDerivAt_Mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (Mf K) (Qf K θ) θ :=
  hasFDerivAt_setIntegral hK _ _ cont_expInner_smul cont_Qint
    (fun θ x => (hasFDerivAt_expInner x θ).smul_const x) θ

theorem continuous_Zf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    Continuous (Zf K) := continuous_setIntegral hK _ cont_expInner

theorem continuous_Mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    Continuous (Mf K) := continuous_setIntegral hK _ cont_expInner_smul

theorem continuous_Qf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) :
    Continuous (Qf K) := continuous_setIntegral hK _ cont_Qint

theorem volume_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    0 < volume K :=
  (isOpen_interior.measure_pos volume hK.2.2).trans_le (measure_mono interior_subset)

theorem Zf_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : 0 < Zf K θ := by
  unfold Zf
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    ((cont_slice _ cont_expInner θ).continuousOn.integrableOn_compact hK.1)]
  have : Function.support (fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫) = Set.univ := by
    ext x; simp [(Real.exp_pos _).ne']
  rw [this, Measure.restrict_apply_univ]
  exact volume_pos hK

theorem logPartition_eq {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : logPartition K θ = Real.log (Zf K θ) := rfl

/-- Integrals against the exponential family. -/
theorem integral_expFamily {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → G) :
    ∫ x, g x ∂(expFamily K θ) = (Zf K θ)⁻¹ • ∫ x in K, Real.exp ⟪θ, x⟫ • g x := by
  unfold expFamily
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  rw [← integral_smul]
  congr 1; ext x
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_smul, Real.exp_sub, logPartition_eq,
    Real.exp_log (Zf_pos hK θ), div_eq_inv_mul]

theorem meanMap_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : meanMap K θ = (Zf K θ)⁻¹ • Mf K θ := by
  unfold meanMap; rw [integral_expFamily hK]; rfl

theorem covForm_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k : EuclideanSpace ℝ (Fin n)) :
    covForm K θ k k = (Zf K θ)⁻¹ *
      ∫ x in K, Real.exp ⟪θ, x⟫ * (⟪x - meanMap K θ, k⟫ * ⟪x - meanMap K θ, k⟫) := by
  unfold covForm; rw [integral_expFamily hK]; rfl

/-! ## S3: derivative of the mean map -/

noncomputable def mf {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (Zf K θ)⁻¹ • Mf K θ

noncomputable def Dm {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (Zf K θ)⁻¹ • Qf K θ + (-(Zf K θ ^ 2)⁻¹ • innerSL ℝ (Mf K θ)).smulRight (Mf K θ)

theorem hasFDerivAt_mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : HasFDerivAt (mf K) (Dm K θ) θ := by
  have h := ((hasDerivAt_inv (Zf_pos hK θ).ne').comp_hasFDerivAt θ
    (hasFDerivAt_Zf hK.1 θ)).smul (hasFDerivAt_Mf hK.1 θ)
  exact h

theorem continuous_Dm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    Continuous (Dm K) := by
  have hZ : Continuous (fun θ => (Zf K θ)⁻¹) :=
    (continuous_Zf hK.1).inv₀ fun θ => (Zf_pos hK θ).ne'
  have hZ2 : Continuous (fun θ => (Zf K θ ^ 2)⁻¹) :=
    ((continuous_Zf hK.1).pow 2).inv₀ fun θ => pow_ne_zero 2 (Zf_pos hK θ).ne'
  have hI : Continuous (fun θ => -(Zf K θ ^ 2)⁻¹ • innerSL ℝ (Mf K θ)) :=
    hZ2.neg.smul ((innerSL ℝ).continuous.comp (continuous_Mf hK.1))
  exact (hZ.smul (continuous_Qf hK.1)).add
    ((ContinuousLinearMap.smulRightL ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).continuous₂.comp (hI.prodMk (continuous_Mf hK.1)))

theorem hasStrictFDerivAt_mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : HasStrictFDerivAt (mf K) (Dm K θ) θ :=
  hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (Eventually.of_forall fun y => hasFDerivAt_mf hK y) (continuous_Dm hK).continuousAt

theorem meanMap_eq_mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K) :
    meanMap K = mf K := funext fun θ => meanMap_eq hK θ

theorem intOn {n : ℕ} {G : Type*} [NormedAddCommGroup G]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    {g : EuclideanSpace ℝ (Fin n) → G} (hg : Continuous g) : Integrable g (volume.restrict K) :=
  hg.continuousOn.integrableOn_compact hK

theorem inner_Mf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ k : EuclideanSpace ℝ (Fin n)) :
    ⟪Mf K θ, k⟫ = ∫ x in K, Real.exp ⟪θ, x⟫ * ⟪x, k⟫ := by
  rw [real_inner_comm k (Mf K θ)]
  unfold Mf
  rw [← integral_inner (intOn hK (by fun_prop))]
  congr 1; ext x
  rw [real_inner_smul_right, real_inner_comm x k]

theorem inner_Qf {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K)
    (θ k h : EuclideanSpace ℝ (Fin n)) :
    ⟪Qf K θ k, h⟫ = ∫ x in K, Real.exp ⟪θ, x⟫ * (⟪x, k⟫ * ⟪x, h⟫) := by
  unfold Qf
  rw [ContinuousLinearMap.integral_apply (intOn hK (cont_slice _ cont_Qint θ)) k]
  rw [real_inner_comm h, ← integral_inner (intOn hK ?_)]
  · congr 1; ext x
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, real_inner_smul_right, smul_eq_mul]
    rw [real_inner_comm x h]; ring
  · exact (cont_slice _ cont_Qint θ).clm_apply continuous_const

theorem inner_Dm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k h : EuclideanSpace ℝ (Fin n)) :
    ⟪Dm K θ k, h⟫ = (Zf K θ)⁻¹ * (∫ x in K, Real.exp ⟪θ, x⟫ * (⟪x, k⟫ * ⟪x, h⟫)) -
      ⟪mf K θ, k⟫ * ⟪mf K θ, h⟫ := by
  have hZ := (Zf_pos hK θ).ne'
  unfold Dm mf
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_left,
    real_inner_smul_left, smul_eq_mul]
  rw [inner_Qf hK.1, ← inv_pow]
  ring

theorem Dm_symm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k h : EuclideanSpace ℝ (Fin n)) : ⟪Dm K θ k, h⟫ = ⟪Dm K θ h, k⟫ := by
  rw [inner_Dm hK, inner_Dm hK]
  congr 1
  · congr 2; ext x; ring
  · ring

theorem Zf_eq_integral {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (θ : EuclideanSpace ℝ (Fin n)) : Zf K θ = ∫ x in K, Real.exp ⟪θ, x⟫ := rfl

/-- `⟪Σ k, k⟫` as a centred second moment. -/
theorem inner_Dm_self {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k : EuclideanSpace ℝ (Fin n)) :
    ⟪Dm K θ k, k⟫ = (Zf K θ)⁻¹ *
      ∫ x in K, Real.exp ⟪θ, x⟫ * (⟪x - mf K θ, k⟫ * ⟪x - mf K θ, k⟫) := by
  have hZ := (Zf_pos hK θ).ne'
  set c := ⟪mf K θ, k⟫ with hc
  have hMk : ⟪Mf K θ, k⟫ = Zf K θ * c := by
    rw [hc]; unfold mf; rw [real_inner_smul_left]; field_simp
  have e : (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp ⟪θ, x⟫ * (⟪x - mf K θ, k⟫ * ⟪x - mf K θ, k⟫)) =
      fun x => (Real.exp ⟪θ, x⟫ * (⟪x, k⟫ * ⟪x, k⟫) - (2 * c) * (Real.exp ⟪θ, x⟫ * ⟪x, k⟫))
        + c ^ 2 * Real.exp ⟪θ, x⟫ := by
    ext x; rw [inner_sub_left, ← hc]; ring
  rw [e, integral_add, integral_sub, integral_const_mul, integral_const_mul, ← inner_Mf hK.1,
    ← Zf_eq_integral, hMk, inner_Dm hK]
  · field_simp
    ring
  all_goals first
    | exact intOn hK.1 (by fun_prop)
    | exact (intOn hK.1 (by fun_prop)).const_mul _
    | exact (intOn hK.1 (by fun_prop)).sub ((intOn hK.1 (by fun_prop)).const_mul _)

theorem covForm_eq_Dm {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k : EuclideanSpace ℝ (Fin n)) : covForm K θ k k = ⟪Dm K θ k, k⟫ := by
  rw [covForm_eq hK, inner_Dm_self hK, meanMap_eq_mf hK]

/-! ## S4: positivity and invertibility -/

theorem inner_Dm_pos {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k : EuclideanSpace ℝ (Fin n)) (hk : k ≠ 0) : 0 < ⟪Dm K θ k, k⟫ := by
  rw [inner_Dm_self hK]
  refine mul_pos (inv_pos.2 (Zf_pos hK θ)) ?_
  set m := mf K θ
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp ⟪θ, x⟫ * (⟪x - m, k⟫ * ⟪x - m, k⟫)) := by fun_prop
  rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (Real.exp_pos _).le
    (mul_self_nonneg _)) (intOn hK.1 hcont)]
  set U := interior K ∩ {x | ⟪x - m, k⟫ ≠ 0}
  have hU : IsOpen U := isOpen_interior.inter
    (isOpen_ne_fun (by fun_prop) continuous_const)
  have hUne : U.Nonempty := by
    obtain ⟨y, hy⟩ := hK.2.2
    have ht : Tendsto (fun t : ℝ => y + t • k) (𝓝 0) (𝓝 y) := by
      have : Continuous (fun t : ℝ => y + t • k) := by fun_prop
      simpa using this.tendsto 0
    obtain ⟨t, ht1, ht2⟩ := ((ht.eventually (isOpen_interior.mem_nhds hy)).filter_mono
      nhdsWithin_le_nhds |>.and (self_mem_nhdsWithin (s := ({0}ᶜ : Set ℝ)) (a := 0))).exists
    by_cases h0 : ⟪y - m, k⟫ = 0
    · refine ⟨y + t • k, ht1, ?_⟩
      show ⟪y + t • k - m, k⟫ ≠ 0
      rw [add_sub_right_comm, inner_add_left, h0, real_inner_smul_left, zero_add]
      exact mul_ne_zero ht2 (by rwa [real_inner_self_eq_norm_sq, pow_ne_zero_iff two_ne_zero,
        norm_ne_zero_iff])
    · exact ⟨y, hy, h0⟩
  have hsub : U ⊆ Function.support (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp ⟪θ, x⟫ * (⟪x - m, k⟫ * ⟪x - m, k⟫)) := by
    intro x hx
    exact mul_ne_zero (Real.exp_pos _).ne' (mul_ne_zero hx.2 hx.2)
  calc (0 : ENNReal) < volume U := hU.measure_pos volume hUne
    _ = volume.restrict K U := by
        rw [Measure.restrict_apply hU.measurableSet,
          Set.inter_eq_left.2 (Set.inter_subset_left.trans interior_subset)]
    _ ≤ _ := measure_mono hsub

theorem Dm_injective {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : Function.Injective (Dm K θ) := by
  intro a b hab
  by_contra hne
  have h := inner_Dm_pos hK θ (a - b) (sub_ne_zero.2 hne)
  rw [map_sub, hab, sub_self, inner_zero_left] at h
  exact lt_irrefl _ h

noncomputable def DmEquiv {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (LinearEquiv.ofInjectiveEndo (Dm K θ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Dm_injective hK θ)).toContinuousLinearEquiv

theorem DmEquiv_coe {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    ((DmEquiv hK θ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) = Dm K θ := by
  ext1 v; rfl

/-! ## S5: gradient inequality and the attained supremum -/

theorem gradient_ineq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ θ' : EuclideanSpace ℝ (Fin n)) :
    Real.log (Zf K θ) + ⟪θ' - θ, mf K θ⟫ ≤ Real.log (Zf K θ') := by
  set d := θ' - θ with hd
  set c := ⟪d, mf K θ⟫ with hc
  have hZ := Zf_pos hK θ
  have hMd : ⟪Mf K θ, d⟫ = Zf K θ * c := by
    rw [hc, real_inner_comm]; unfold mf; rw [real_inner_smul_right]; field_simp
  have key : ∫ x in K, Real.exp c * ((1 - c) * Real.exp ⟪θ, x⟫ + Real.exp ⟪θ, x⟫ * ⟪x, d⟫) =
      Real.exp c * Zf K θ := by
    rw [integral_const_mul, integral_add, integral_const_mul, ← inner_Mf hK.1, ← Zf_eq_integral,
      hMd]
    · ring
    · exact (intOn hK.1 (by fun_prop)).const_mul _
    · exact intOn hK.1 (by fun_prop)
  have mono : ∫ x in K, Real.exp c * ((1 - c) * Real.exp ⟪θ, x⟫ + Real.exp ⟪θ, x⟫ * ⟪x, d⟫) ≤
      Zf K θ' := by
    unfold Zf
    refine integral_mono (intOn hK.1 (by fun_prop)) (intOn hK.1 (by fun_prop)) fun x => ?_
    have h1 : ⟪θ', x⟫ = ⟪θ, x⟫ + ⟪x, d⟫ := by
      rw [hd, real_inner_comm, inner_sub_right, real_inner_comm θ' x, real_inner_comm θ x]; ring
    have h2 := Real.add_one_le_exp (⟪x, d⟫ - c)
    have h3 : Real.exp c * Real.exp (⟪x, d⟫ - c) = Real.exp ⟪x, d⟫ := by
      rw [← Real.exp_add]; ring_nf
    show Real.exp c * ((1 - c) * Real.exp ⟪θ, x⟫ + Real.exp ⟪θ, x⟫ * ⟪x, d⟫) ≤ Real.exp ⟪θ', x⟫
    rw [h1, Real.exp_add]
    have h4 : Real.exp c * (⟪x, d⟫ - c + 1) ≤ Real.exp ⟪x, d⟫ := by
      rw [← h3]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos c).le
    nlinarith [Real.exp_pos ⟪θ, x⟫]
  rw [key] at mono
  have := Real.log_le_log (mul_pos (Real.exp_pos c) hZ) mono
  rw [Real.log_mul (Real.exp_pos c).ne' hZ.ne', Real.log_exp] at this
  linarith

theorem sup_le_attained {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ θ' : EuclideanSpace ℝ (Fin n)) :
    ⟪θ', mf K θ⟫ - logPartition K θ' ≤ ⟪θ, mf K θ⟫ - logPartition K θ := by
  have h := gradient_ineq hK θ θ'
  rw [logPartition_eq, logPartition_eq]
  rw [inner_sub_left] at h
  linarith

theorem fstar_eq {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    entropicBarrier K (mf K θ) = ⟪θ, mf K θ⟫ - logPartition K θ := by
  unfold entropicBarrier
  exact le_antisymm (ciSup_le fun θ' => sup_le_attained hK θ θ')
    (le_ciSup (f := fun θ' => ⟪θ', mf K θ⟫ - logPartition K θ')
      ⟨_, Set.forall_mem_range.2 fun θ' => sup_le_attained hK θ θ'⟩ θ)

theorem fstar_ge {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ θ' : EuclideanSpace ℝ (Fin n)) :
    ⟪θ', mf K θ⟫ - logPartition K θ' ≤ entropicBarrier K (mf K θ) := by
  unfold entropicBarrier
  exact le_ciSup (f := fun θ' => ⟪θ', mf K θ⟫ - logPartition K θ')
      ⟨_, Set.forall_mem_range.2 fun θ' => sup_le_attained hK θ θ'⟩ θ'

/-! ## S6: envelope theorem and derivatives of `f*` -/

theorem envelope {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} {y0 : EuclideanSpace ℝ (Fin n)}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ∈ 𝓝 y0) (hg : ContinuousAt g y0)
    (hineq : ∀ y ∈ S, ∀ y' ∈ S, φ y + ⟪g y, y' - y⟫ ≤ φ y') :
    HasFDerivAt φ (innerSL ℝ (g y0)) y0 := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hy0 : y0 ∈ S := mem_of_mem_nhds hS
  have hgc : ∀ᶠ y in 𝓝 y0, ‖g y - g y0‖ ≤ ε := by
    filter_upwards [Metric.tendsto_nhds.1 hg ε hε] with y hy
    rw [dist_eq_norm] at hy; exact hy.le
  filter_upwards [hS, hgc] with y hy hgy
  rw [innerSL_apply_apply, Real.norm_eq_abs, abs_le]
  have l1 := hineq y0 hy0 y hy
  have l2 := hineq y hy y0 hy0
  have e1 : ⟪g y, y0 - y⟫ = -⟪g y, y - y0⟫ := by rw [← inner_neg_right, neg_sub]
  have cs : ⟪g y - g y0, y - y0⟫ ≤ ‖g y - g y0‖ * ‖y - y0‖ := real_inner_le_norm _ _
  have cs2 : ‖g y - g y0‖ * ‖y - y0‖ ≤ ε * ‖y - y0‖ :=
    mul_le_mul_of_nonneg_right hgy (norm_nonneg _)
  rw [inner_sub_left] at cs
  constructor
  · nlinarith [norm_nonneg (y - y0)]
  · linarith

theorem hasStrictFDerivAt_mf' {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    HasStrictFDerivAt (mf K)
      ((DmEquiv hK θ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) θ := by
  rw [DmEquiv_coe]; exact hasStrictFDerivAt_mf hK θ

theorem hasFDerivAt_fstar {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ0 : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (entropicBarrier K) (innerSL ℝ θ0) (mf K θ0) := by
  have hs := hasStrictFDerivAt_mf' hK θ0
  set g := hs.localInverse (mf K) _ θ0
  have hg0 : g (mf K θ0) = θ0 := hs.localInverse_apply_image
  have hS : {y | mf K (g y) = y} ∈ 𝓝 (mf K θ0) := hs.eventually_right_inverse
  have h := envelope (φ := entropicBarrier K) hS hs.localInverse_continuousAt ?_
  · have e := hs.localInverse_apply_image
    rw [e] at h; exact h
  intro y hy y' hy'
  have hy : mf K (g y) = y := hy
  have hy' : mf K (g y') = y' := hy'
  have a1 := fstar_eq hK (g y)
  have a2 := fstar_ge hK (g y') (g y)
  rw [hy] at a1; rw [hy'] at a2
  rw [inner_sub_right]; linarith

theorem fderiv_fstar_eventually {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsConvexBody K) (θ0 : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fderiv ℝ (entropicBarrier K))
      ((innerSL ℝ).comp ((DmEquiv hK θ0).symm :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mf K θ0) := by
  have hs := hasStrictFDerivAt_mf' hK θ0
  set g := hs.localInverse (mf K) _ θ0
  have hS : {y | mf K (g y) = y} ∈ 𝓝 (mf K θ0) := hs.eventually_right_inverse
  have hgd : HasFDerivAt g ((DmEquiv hK θ0).symm :
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (mf K θ0) :=
    hs.to_localInverse.hasFDerivAt
  have h1 : HasFDerivAt (fun y => innerSL ℝ (g y))
      ((innerSL ℝ).comp ((DmEquiv hK θ0).symm :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mf K θ0) :=
    (innerSL ℝ).hasFDerivAt.comp _ hgd
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hS] with y hy
  have hy : mf K (g y) = y := hy
  have := (hasFDerivAt_fstar hK (g y)).fderiv
  rw [hy] at this
  exact this

theorem fderiv_fstar_apply {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (entropicBarrier K) (mf K θ) h = ⟪θ, h⟫ := by
  rw [(hasFDerivAt_fstar hK θ).fderiv, innerSL_apply_apply]

theorem hess_fstar_apply {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ h : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (entropicBarrier K) (mf K θ) (fun _ => h) =
      ⟪(DmEquiv hK θ).symm h, h⟫ := by
  rw [iteratedFDeriv_two_apply, (fderiv_fstar_eventually hK θ).fderiv]
  rfl

/-! ## S7: the mean lies in the interior -/

theorem mf_mem {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : mf K θ ∈ K := by
  by_contra hm
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed hK.2.1 hK.1.isClosed hm
  have hZ := Zf_pos hK θ
  have h1 : f (Mf K θ) = ∫ x in K, Real.exp ⟪θ, x⟫ * f x := by
    unfold Mf
    rw [← f.integral_comp_comm (intOn hK.1 (by fun_prop))]
    congr 1; ext x; simp
  have h2 : u * Zf K θ ≤ ∫ x in K, Real.exp ⟪θ, x⟫ * f x := by
    unfold Zf
    rw [← integral_const_mul]
    refine setIntegral_mono_on (intOn hK.1 (by fun_prop)) (intOn hK.1 (by fun_prop))
      hK.1.measurableSet fun x hx => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hb x hx).le (Real.exp_pos _).le
  have h3 : f (mf K θ) * Zf K θ = f (Mf K θ) := by
    unfold mf; rw [map_smul, smul_eq_mul]; field_simp
  have : u * Zf K θ ≤ f (mf K θ) * Zf K θ := by rw [h3, h1]; exact h2
  have := le_of_mul_le_mul_right this hZ
  linarith

theorem mf_mem_interior {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ : EuclideanSpace ℝ (Fin n)) : mf K θ ∈ interior K := by
  have hs := hasStrictFDerivAt_mf' hK θ
  have hmap := hs.map_nhds_eq_of_equiv
  rw [mem_interior_iff_mem_nhds, ← hmap]
  exact Filter.mem_map.2 (Filter.Eventually.of_forall fun y => mf_mem hK y)

/-! ## S8: the mean map is onto the interior -/

theorem Zf_lower {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    {y : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : ball y r ⊆ K)
    (θ : EuclideanSpace ℝ (Fin n)) :
    volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) *
      Real.exp (⟪θ, y⟫ + r / 2 * ‖θ‖) ≤ Zf K θ := by
  set a := 3 * r / (4 * ‖θ‖) with ha
  set z := y + a • θ with hz
  have hanorm : a * ‖θ‖ ^ 2 = 3 * r / 4 * ‖θ‖ := by
    by_cases h0 : ‖θ‖ = 0
    · rw [h0]; ring
    · rw [ha]; field_simp
  have hzy : ‖a • θ‖ ≤ 3 * r / 4 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases h0 : ‖θ‖ = 0
    · rw [h0, mul_zero]; positivity
    · rw [ha]; field_simp; exact le_refl _
  have hsub : ball z (r / 4) ⊆ K := by
    refine Set.Subset.trans ?_ hball
    intro x hx
    rw [mem_ball] at hx ⊢
    calc dist x y ≤ dist x z + dist z y := dist_triangle _ _ _
      _ < r / 4 + 3 * r / 4 := by
          refine add_lt_add_of_lt_of_le hx ?_
          rw [hz, dist_eq_norm, add_sub_cancel_left]; exact hzy
      _ = r := by ring
  have hlow : ∀ x ∈ ball z (r / 4), ⟪θ, y⟫ + r / 2 * ‖θ‖ ≤ ⟪θ, x⟫ := by
    intro x hx
    rw [mem_ball, dist_eq_norm] at hx
    have e : ⟪θ, x⟫ = ⟪θ, y⟫ + a * ‖θ‖ ^ 2 + ⟪θ, x - z⟫ := by
      rw [hz, inner_sub_right, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    have cs : -(‖θ‖ * ‖x - z‖) ≤ ⟪θ, x - z⟫ := by
      have := abs_real_inner_le_norm θ (x - z)
      linarith [neg_abs_le ⟪θ, x - z⟫]
    have : ‖θ‖ * ‖x - z‖ ≤ ‖θ‖ * (r / 4) := mul_le_mul_of_nonneg_left hx.le (norm_nonneg _)
    rw [e, hanorm]; nlinarith [norm_nonneg θ]
  have hcz : volume.real (ball z (r / 4)) = volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) := by
    simp only [Measure.real, Measure.addHaar_ball_center]
  calc volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) *
        Real.exp (⟪θ, y⟫ + r / 2 * ‖θ‖)
      = ∫ x in ball z (r / 4), Real.exp (⟪θ, y⟫ + r / 2 * ‖θ‖) := by
        rw [setIntegral_const, hcz, smul_eq_mul]
    _ ≤ ∫ x in ball z (r / 4), Real.exp ⟪θ, x⟫ := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_ball fun x hx =>
          Real.exp_le_exp.2 (hlow x hx)
        · exact integrableOn_const (measure_ball_lt_top.ne)
        · exact IntegrableOn.mono_set (intOn (isCompact_closedBall z (r / 4))
            (g := fun x : EuclideanSpace ℝ (Fin n) => Real.exp ⟪θ, x⟫) (by fun_prop))
            ball_subset_closedBall
    _ ≤ Zf K θ := by
        unfold Zf
        refine setIntegral_mono_set (intOn hK.1 (by fun_prop))
          (Eventually.of_forall fun x => (Real.exp_pos _).le) (Eventually.of_forall hsub)

theorem mf_surj {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ interior K) : ∃ θ, mf K θ = y := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isOpen_interior y hy
  have hball' : ball y r ⊆ K := hball.trans interior_subset
  set c0 := volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) with hc0
  have hc0pos : 0 < c0 := ENNReal.toReal_pos (measure_ball_pos volume _ (by positivity)).ne'
    measure_ball_lt_top.ne
  set φ : EuclideanSpace ℝ (Fin n) → ℝ := fun θ => ⟪θ, y⟫ - Real.log (Zf K θ) with hφ
  have hbound : ∀ θ, φ θ ≤ -Real.log c0 - r / 2 * ‖θ‖ := by
    intro θ
    have h := Zf_lower hK hr hball' θ
    have h2 := Real.log_le_log (by positivity) h
    rw [Real.log_mul hc0pos.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    simp only [hφ]; linarith
  have hφc : Continuous φ := by
    have : Continuous (fun θ : EuclideanSpace ℝ (Fin n) => Real.log (Zf K θ)) :=
      (continuous_Zf hK.1).log fun θ => (Zf_pos hK θ).ne'
    exact (continuous_id.inner continuous_const).sub this
  set R := |2 / r * (-Real.log c0 - φ 0)| with hR
  have hR0 : 0 ≤ R := abs_nonneg _
  obtain ⟨θs, -, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_isMaxOn
    ⟨0, mem_closedBall_self hR0⟩ hφc.continuousOn
  have hglob : ∀ θ, φ θ ≤ φ θs := by
    intro θ
    by_cases hθ : ‖θ‖ ≤ R
    · exact hmax (mem_closedBall_zero_iff.2 hθ)
    · replace hθ := not_le.1 hθ
      have h0 : φ 0 ≤ φ θs := hmax (mem_closedBall_self hR0)
      have h1 := hbound θ
      have h2 : 2 / r * (-Real.log c0 - φ 0) ≤ R := le_abs_self _
      have h3 : -Real.log c0 - φ 0 ≤ r / 2 * R := by
        have := mul_le_mul_of_nonneg_left h2 (le_of_lt (half_pos hr))
        rwa [← mul_assoc, show r / 2 * (2 / r) = 1 by field_simp, one_mul] at this
      have h4 : r / 2 * R < r / 2 * ‖θ‖ := mul_lt_mul_of_pos_left hθ (half_pos hr)
      linarith
  have hloc : IsLocalMax φ θs := Eventually.of_forall hglob
  have hd1 : HasFDerivAt (fun θ : EuclideanSpace ℝ (Fin n) => ⟪θ, y⟫) (innerSL ℝ y) θs := by
    have e : (fun θ : EuclideanSpace ℝ (Fin n) => ⟪θ, y⟫) = fun θ => innerSL ℝ y θ := by
      ext θ; rw [real_inner_comm]; rfl
    rw [e]; exact (innerSL ℝ y).hasFDerivAt
  have hd2 := (hasFDerivAt_Zf hK.1 θs).log (Zf_pos hK θs).ne'
  have hzero := hloc.hasFDerivAt_eq_zero (hd1.sub hd2)
  refine ⟨θs, ?_⟩
  have h0 := congrArg (fun L => L (y - mf K θs)) hzero
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    ContinuousLinearMap.zero_apply, smul_eq_mul] at h0
  have h1 : (Zf K θs)⁻¹ * ⟪Mf K θs, y - mf K θs⟫ = ⟪mf K θs, y - mf K θs⟫ := by
    unfold mf; rw [real_inner_smul_left]
  rw [h1, ← inner_sub_left] at h0
  have := inner_self_eq_zero.1 h0
  exact (sub_eq_zero.1 this).symm

/-! ## S9: assembly -/

theorem Dm_self_nonneg {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ k : EuclideanSpace ℝ (Fin n)) : 0 ≤ ⟪Dm K θ k, k⟫ := by
  by_cases hk : k = 0
  · rw [hk, inner_zero_right]
  · exact (inner_Dm_pos hK θ k hk).le

theorem Dm_cs {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsConvexBody K)
    (θ u v : EuclideanSpace ℝ (Fin n)) :
    ⟪Dm K θ u, v⟫ ^ 2 ≤ ⟪Dm K θ u, u⟫ * ⟪Dm K θ v, v⟫ := by
  have hq : ∀ t : ℝ, 0 ≤ ⟪Dm K θ u, u⟫ * (t * t) + (-2 * ⟪Dm K θ u, v⟫) * t +
      ⟪Dm K θ v, v⟫ := by
    intro t
    have h := Dm_self_nonneg hK θ (t • u - v)
    rw [map_sub, map_smul] at h
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right] at h
    rw [Dm_symm hK θ v u] at h
    nlinarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

end EB39

open EntropicBarrier.Universal in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsConvexBody K) (ν : ℝ) (hν : 0 ≤ ν) :
    SatisfiesNuBound K (entropicBarrier K) ν ↔
      ∀ θ : EuclideanSpace ℝ (Fin n), covForm K θ θ θ ≤ ν := by
  constructor
  · intro H θ
    have hy := EB39.mf_mem_interior hK θ
    have h := H _ hy (EB39.DmEquiv hK θ θ)
    rw [EB39.fderiv_fstar_apply hK, EB39.hess_fstar_apply hK,
      ContinuousLinearEquiv.symm_apply_apply] at h
    have hq : ⟪θ, EB39.DmEquiv hK θ θ⟫ = covForm K θ θ θ := by
      rw [EB39.covForm_eq_Dm hK, real_inner_comm]; rfl
    rw [hq] at h
    have h0 : 0 ≤ covForm K θ θ θ := by
      rw [EB39.covForm_eq_Dm hK]; exact EB39.Dm_self_nonneg hK θ θ
    have h2 := (Real.le_sqrt h0 (mul_nonneg hν h0)).1 h
    by_cases hz : covForm K θ θ θ = 0
    · rw [hz]; exact hν
    · have hp : 0 < covForm K θ θ θ := lt_of_le_of_ne h0 (Ne.symm hz)
      nlinarith
  · intro H y hy h
    obtain ⟨θ, rfl⟩ := EB39.mf_surj hK hy
    rw [EB39.fderiv_fstar_apply hK, EB39.hess_fstar_apply hK]
    set k := (EB39.DmEquiv hK θ).symm h with hk
    have hh : h = EB39.Dm K θ k := by
      rw [hk, ← EB39.DmEquiv_coe hK θ]; simp
    have hθ := H θ
    rw [EB39.covForm_eq_Dm hK] at hθ
    have hcs := EB39.Dm_cs hK θ θ k
    have hkk := EB39.Dm_self_nonneg hK θ k
    have e1 : ⟪θ, h⟫ = ⟪EB39.Dm K θ θ, k⟫ := by
      rw [hh, real_inner_comm, EB39.Dm_symm hK]
    have e2 : ⟪k, h⟫ = ⟪EB39.Dm K θ k, k⟫ := by rw [hh, real_inner_comm]
    rw [e1, e2]
    refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
    calc ⟪EB39.Dm K θ θ, k⟫ ^ 2 ≤ ⟪EB39.Dm K θ θ, θ⟫ * ⟪EB39.Dm K θ k, k⟫ := hcs
      _ ≤ ν * ⟪EB39.Dm K θ k, k⟫ := mul_le_mul_of_nonneg_right hθ hkk
