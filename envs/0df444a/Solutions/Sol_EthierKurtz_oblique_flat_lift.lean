-- Prove2me | solution 1 for EthierKurtz.oblique_flat_lift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:35:32.296212+00:00
-- url     : https://prove2.me/submissions/6ecee29e-a87b-477d-afaa-e56cba36d996

import Mathlib

set_option autoImplicit false



/-! Instance shortcuts: the default search for `ContinuousSMul ℝ (E × ℝ)` first tries a slow failing
`ProperSMul` path (3-5 s per query); these cached instances make it immediate. -/
instance (priority := high) instCSMulEuc (n : ℕ) : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n)) :=
  inferInstance
instance (priority := high) instCSMulEucR (n : ℕ) : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × ℝ) :=
  inferInstance
instance (priority := high) instCSMulREuc (n : ℕ) : ContinuousSMul ℝ (ℝ × EuclideanSpace ℝ (Fin n)) :=
  inferInstance
instance (priority := high) instT2EucR (n : ℕ) : T2Space (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ) :=
  inferInstance
instance (priority := high) instCplEucR (n : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ) :=
  inferInstance
instance (priority := high) instT2Euc (n : ℕ) : T2Space (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  inferInstance
instance (priority := high) instCplEuc (n : ℕ) : CompleteSpace (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  inferInstance
instance (priority := high) instSCEither (n : ℕ) {Z : Type*} [TopologicalSpace Z] :
    SecondCountableTopologyEither (EuclideanSpace ℝ (Fin n)) Z := inferInstance
instance (priority := high) instTFEucR (n : ℕ) :
    Module.IsTorsionFree ℝ (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ) := inferInstance
noncomputable instance (priority := high) instNEucRREuc (n : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n)) := inferInstance
noncomputable instance (priority := high) instNSEucRREuc (n : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n)) := inferInstance
noncomputable instance (priority := high) instN2EucRREuc (n : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ]
      EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ × EuclideanSpace ℝ (Fin n)) := inferInstance
noncomputable instance (priority := high) instN2EucR (n : ℕ) :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ) :=
  inferInstance
noncomputable instance (priority := high) instNS2EucR (n : ℕ) :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] ℝ) :=
  inferInstance
instance (priority := high) instCplREuc (n : ℕ) : CompleteSpace (ℝ × EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  inferInstance

namespace Pd67abb68C2a

/-- Hoelder dichotomy on the open half-space `{p | 0 < p.2}`: a function bounded by
`A t^μ` whose derivative is bounded by `A t^(μ-1)` is `μ`-Hoelder there. -/
lemma holder_of_deriv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : E × ℝ → F) (μ A : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hA : 0 ≤ A)
    (hdiff : ∀ p : E × ℝ, 0 < p.2 → DifferentiableAt ℝ G p)
    (hG : ∀ p : E × ℝ, 0 < p.2 → ‖G p‖ ≤ A * p.2 ^ μ)
    (hdG : ∀ p : E × ℝ, 0 < p.2 → ‖fderiv ℝ G p‖ ≤ A * p.2 ^ (μ - 1)) :
    ∀ p p' : E × ℝ, 0 < p.2 → 0 < p'.2 → ‖G p - G p'‖ ≤ 5 * A * ‖p - p'‖ ^ μ := by
  intro p p' hp hp'
  wlog hle : p.2 ≤ p'.2 generalizing p p'
  · rw [norm_sub_rev (G p), norm_sub_rev p]
    exact this p' p hp' hp (le_of_not_ge hle)
  set h := ‖p - p'‖ with hh
  have hh0 : 0 ≤ h := norm_nonneg _
  have ht : |p.2 - p'.2| ≤ h := by
    have : ‖(p - p').2‖ ≤ ‖p - p'‖ := norm_snd_le _
    simpa [Real.norm_eq_abs] using this
  rcases eq_or_lt_of_le hh0 with h0 | hpos
  · have : p = p' := by
      have := norm_eq_zero.mp h0.symm
      exact sub_eq_zero.mp this
    subst this; simp only [sub_self, norm_zero]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hh0 _)
  by_cases hcase : p.2 / 2 ≤ h
  · -- both values are small
    have h1 : ‖G p‖ ≤ A * (2 * h) ^ μ := by
      refine (hG p hp).trans (mul_le_mul_of_nonneg_left ?_ hA)
      exact Real.rpow_le_rpow hp.le (by linarith) hμ.le
    have h2 : ‖G p'‖ ≤ A * (3 * h) ^ μ := by
      refine (hG p' hp').trans (mul_le_mul_of_nonneg_left ?_ hA)
      refine Real.rpow_le_rpow hp'.le ?_ hμ.le
      have := (abs_le.mp ht).1
      linarith
    have e2 : (2 * h) ^ μ ≤ 2 * h ^ μ := by
      rw [Real.mul_rpow (by norm_num) hh0]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hh0 _)
      calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
        _ = 2 := Real.rpow_one 2
    have e3 : (3 * h) ^ μ ≤ 3 * h ^ μ := by
      rw [Real.mul_rpow (by norm_num) hh0]
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hh0 _)
      calc (3 : ℝ) ^ μ ≤ 3 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
        _ = 3 := Real.rpow_one 3
    have hhμ : 0 ≤ h ^ μ := Real.rpow_nonneg hh0 _
    calc ‖G p - G p'‖ ≤ ‖G p‖ + ‖G p'‖ := norm_sub_le _ _
      _ ≤ A * (2 * h) ^ μ + A * (3 * h) ^ μ := add_le_add h1 h2
      _ ≤ A * (2 * h ^ μ) + A * (3 * h ^ μ) :=
          add_le_add (mul_le_mul_of_nonneg_left e2 hA) (mul_le_mul_of_nonneg_left e3 hA)
      _ = 5 * A * h ^ μ := by ring
  · -- close points: mean value inequality on the half-space `t > p.2 / 2`
    rw [not_le] at hcase
    have hp2 : 0 < p.2 / 2 := by linarith
    set S : Set (E × ℝ) := (LinearMap.snd ℝ E ℝ) ⁻¹' Set.Ioi (p.2 / 2) with hS
    have hSc : Convex ℝ S := (convex_Ioi _).linear_preimage _
    have hpS : p ∈ S := by show p.2 / 2 < p.2; linarith
    have hp'S : p' ∈ S := by show p.2 / 2 < p'.2; linarith
    have hbound : ∀ x ∈ S, ‖fderiv ℝ G x‖ ≤ A * (p.2 / 2) ^ (μ - 1) := by
      intro x hx
      have hx' : p.2 / 2 < x.2 := hx
      refine (hdG x (by linarith)).trans (mul_le_mul_of_nonneg_left ?_ hA)
      exact Real.rpow_le_rpow_of_nonpos hp2 hx'.le (by linarith)
    have hmvt := hSc.norm_image_sub_le_of_norm_fderiv_le
      (fun x hx => hdiff x (by have : p.2 / 2 < x.2 := hx; linarith)) hbound hp'S hpS
    have hk : (p.2 / 2) ^ (μ - 1) ≤ h ^ (μ - 1) :=
      Real.rpow_le_rpow_of_nonpos hpos hcase.le (by linarith)
    have hhμ : h ^ (μ - 1) * h = h ^ μ := by
      rw [Real.rpow_sub_one hpos.ne']; field_simp
    have hhμ0 : 0 ≤ h ^ μ := Real.rpow_nonneg hh0 _
    calc ‖G p - G p'‖ ≤ A * (p.2 / 2) ^ (μ - 1) * ‖p - p'‖ := hmvt
      _ ≤ A * h ^ (μ - 1) * h := by
          rw [← hh]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA) hh0
      _ = A * h ^ μ := by rw [mul_assoc, hhμ]
      _ ≤ 5 * A * h ^ μ := by
          have := mul_nonneg hA hhμ0
          linarith only [this]

open MeasureTheory in
/-- A set integral over a compact set of a jointly `C^1` integrand is `C^1` in the parameter,
with derivative the integral of the partial derivative. -/
lemma hasFDerivAt_setIntegral_param {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsLocallyFiniteMeasure μ]
    (f : H → Y → ℝ) (hf : ContDiff ℝ 1 (fun p : H × Y => f p.1 p.2)) {s : Set Y}
    (hs : IsCompact s) (x₀ : H) :
    HasFDerivAt (fun x => ∫ y in s, f x y ∂μ)
      (∫ y in s, (fderiv ℝ (fun p : H × Y => f p.1 p.2) (x₀, y)).comp
        (ContinuousLinearMap.inl ℝ H Y) ∂μ) x₀ := by
  set g : H × Y → ℝ := fun p => f p.1 p.2 with hg
  set F' : H → Y → H →L[ℝ] ℝ := fun x y =>
    (fderiv ℝ g (x, y)).comp (ContinuousLinearMap.inl ℝ H Y) with hF'
  have hgd : Differentiable ℝ g := hf.differentiable one_ne_zero
  have hcont' : Continuous (fun p : H × Y => F' p.1 p.2) := by
    have h1 : Continuous (fderiv ℝ g) := hf.continuous_fderiv one_ne_zero
    exact (ContinuousLinearMap.compL ℝ H (H × Y) ℝ |>.flip
      (ContinuousLinearMap.inl ℝ H Y)).continuous.comp h1
  have hderiv : ∀ x y, HasFDerivAt (fun x => f x y) (F' x y) x := by
    intro x y
    exact (hgd (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Metric.closedBall x₀ 1 ×ˢ s, ‖F' p.1 p.2‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod hs).bddAbove_image
      hcont'.norm.continuousOn
    exact ⟨C, fun p hp => hC ⟨p, hp, rfl⟩⟩
  have hμs : μ s ≠ ⊤ := hs.measure_lt_top.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ.restrict s)
    (F' := F') (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact (hf.continuous.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · have hc : Continuous (fun y => f x₀ y) :=
      hf.continuous.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hc.continuousOn.integrableOn_compact hs)
  · exact (hcont'.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' hs.measurableSet]
    exact Filter.Eventually.of_forall (fun y hy x hx =>
      hC (x, y) ⟨Metric.ball_subset_closedBall hx, hy⟩)
  · exact integrableOn_const hμs
  · exact Filter.Eventually.of_forall (fun y x _ => hderiv x y)

open MeasureTheory in
lemma contDiff_setIntegral_param {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsLocallyFiniteMeasure μ]
    (f : H → Y → ℝ) (hf : ContDiff ℝ 1 (fun p : H × Y => f p.1 p.2)) {s : Set Y}
    (hs : IsCompact s) :
    ContDiff ℝ 1 (fun x => ∫ y in s, f x y ∂μ) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun x => (hasFDerivAt_setIntegral_param (μ := μ) f hf hs x).differentiableAt, ?_⟩
  have heq : fderiv ℝ (fun x => ∫ y in s, f x y ∂μ) = fun x => ∫ y in s,
      (fderiv ℝ (fun p : H × Y => f p.1 p.2) (x, y)).comp
        (ContinuousLinearMap.inl ℝ H Y) ∂μ :=
    funext fun x => (hasFDerivAt_setIntegral_param (μ := μ) f hf hs x).fderiv
  rw [heq]
  have h1 : Continuous (fderiv ℝ (fun p : H × Y => f p.1 p.2)) := hf.continuous_fderiv one_ne_zero
  have hcont' : Continuous (fun p : H × Y =>
      (fderiv ℝ (fun p : H × Y => f p.1 p.2) (p.1, p.2)).comp
        (ContinuousLinearMap.inl ℝ H Y)) :=
    (ContinuousLinearMap.compL ℝ H (H × Y) ℝ |>.flip
      (ContinuousLinearMap.inl ℝ H Y)).continuous.comp h1
  exact continuous_parametric_integral_of_continuous
    (f := fun x y => (fderiv ℝ (fun p : H × Y => f p.1 p.2) (x, y)).comp
      (ContinuousLinearMap.inl ℝ H Y)) hcont' hs

open MeasureTheory in
/-- The variable-radius average `v (z, t) = ∫ q (z - t y) η y dy` of a `C^1` function. -/
noncomputable def vavg {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ :=
  ∫ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, q (p.1 - p.2 • y) * η y

lemma vavg_contDiff {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 1 η) : ContDiff ℝ 1 (vavg q η) := by
  unfold vavg
  refine contDiff_setIntegral_param
    (fun (p : EuclideanSpace ℝ (Fin n) × ℝ) (y : EuclideanSpace ℝ (Fin n)) =>
      q (p.1 - p.2 • y) * η y) ?_ (isCompact_closedBall _ _)
  refine (hq.comp ?_).mul (hη.comp contDiff_snd)
  exact (contDiff_fst.comp contDiff_fst).sub ((contDiff_snd.comp contDiff_fst).smul contDiff_snd)

open MeasureTheory in
lemma vavg_zero {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ)
    (hη : Function.support η ⊆ Metric.closedBall 0 1) (hη1 : ∫ y, η y = 1)
    (z : EuclideanSpace ℝ (Fin n)) : vavg q η (z, 0) = q z := by
  unfold vavg
  simp only [zero_smul, sub_zero]
  rw [integral_const_mul, setIntegral_eq_integral_of_forall_compl_eq_zero, hη1, mul_one]
  intro y hy
  by_contra h
  exact hy (hη h)

open MeasureTheory in
/-- Differentiation under a compact set integral with a given jointly continuous derivative. -/
lemma hasFDerivAt_setIntegral_param' {H Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] {μ : Measure Y} [IsLocallyFiniteMeasure μ]
    (f : H → Y → ℝ) (F' : H → Y → H →L[ℝ] ℝ) (hfc : Continuous (fun p : H × Y => f p.1 p.2))
    (hF'c : Continuous (fun p : H × Y => F' p.1 p.2))
    (hderiv : ∀ x y, HasFDerivAt (fun x => f x y) (F' x y) x) {s : Set Y}
    (hs : IsCompact s) (x₀ : H) :
    HasFDerivAt (fun x => ∫ y in s, f x y ∂μ) (∫ y in s, F' x₀ y ∂μ) x₀ := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Metric.closedBall x₀ 1 ×ˢ s, ‖F' p.1 p.2‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ 1).prod hs).bddAbove_image
      hF'c.norm.continuousOn
    exact ⟨C, fun p hp => hC ⟨p, hp, rfl⟩⟩
  have hμs : μ s ≠ ⊤ := hs.measure_lt_top.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ.restrict s)
    (F' := F') (bound := fun _ => C) (Metric.ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact (hfc.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · have hc : Continuous (fun y => f x₀ y) :=
      hfc.comp (Continuous.prodMk continuous_const continuous_id)
    exact (hc.continuousOn.integrableOn_compact hs)
  · exact (hF'c.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' hs.measurableSet]
    exact Filter.Eventually.of_forall (fun y hy x hx =>
      hC (x, y) ⟨Metric.ball_subset_closedBall hx, hy⟩)
  · exact integrableOn_const hμs
  · exact Filter.Eventually.of_forall (fun y x _ => hderiv x y)

/-- The linear map `(h, s) ↦ h - s • y`. -/
noncomputable def Lmap {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.fst ℝ _ ℝ - (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ).smulRight y

lemma Lmap_norm_le {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) : ‖Lmap y‖ ≤ 1 + ‖y‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  simp only [Lmap, ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd']
  calc ‖v.1 - v.2 • y‖ ≤ ‖v.1‖ + ‖v.2 • y‖ := norm_sub_le _ _
    _ = ‖v.1‖ + ‖v.2‖ * ‖y‖ := by rw [norm_smul]
    _ ≤ ‖v‖ + ‖v‖ * ‖y‖ := by
        gcongr
        · exact norm_fst_le v
        · exact norm_snd_le v
    _ = (1 + ‖y‖) * ‖v‖ := by ring

open MeasureTheory in
lemma vavg_hasFDerivAt {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : Continuous η) (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    HasFDerivAt (vavg q η) (∫ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      η y • (fderiv ℝ q (p.1 - p.2 • y)).comp (Lmap y)) p := by
  have hqd : Differentiable ℝ q := hq.differentiable one_ne_zero
  have hqc : Continuous (fderiv ℝ q) := hq.continuous_fderiv one_ne_zero
  unfold vavg
  refine hasFDerivAt_setIntegral_param'
    (fun (p : EuclideanSpace ℝ (Fin n) × ℝ) (y : EuclideanSpace ℝ (Fin n)) =>
      q (p.1 - p.2 • y) * η y)
    (fun p y => η y • (fderiv ℝ q (p.1 - p.2 • y)).comp (Lmap y)) ?_ ?_ ?_
    (isCompact_closedBall _ _) p
  · exact (hq.continuous.comp ((continuous_fst.comp continuous_fst).sub
      ((continuous_snd.comp continuous_fst).smul continuous_snd))).mul (hη.comp continuous_snd)
  · have hL : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Lmap y) := by
      unfold Lmap
      exact continuous_const.sub
        ((ContinuousLinearMap.smulRightL ℝ _ _
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)).continuous)
    refine (hη.comp continuous_snd).smul ?_
    refine Continuous.clm_comp (hqc.comp ((continuous_fst.comp continuous_fst).sub
      ((continuous_snd.comp continuous_fst).smul continuous_snd))) (hL.comp continuous_snd)
  · intro x y
    have hin : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) × ℝ => x.1 - x.2 • y) (Lmap y) x :=
      (Lmap y).hasFDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun v => by
        simp [Lmap]))
    exact ((hqd _).hasFDerivAt.comp x hin).mul_const (η y)

lemma Lmap_apply {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n) × ℝ) :
    Lmap y v = v.1 - v.2 • y := by simp [Lmap]

lemma vavg_F'_cont {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : Continuous η) :
    Continuous (fun py : (EuclideanSpace ℝ (Fin n) × ℝ) × EuclideanSpace ℝ (Fin n) =>
      η py.2 • (fderiv ℝ q (py.1.1 - py.1.2 • py.2)).comp (Lmap py.2)) := by
  have hqc : Continuous (fderiv ℝ q) := hq.continuous_fderiv one_ne_zero
  have hL : Continuous (fun y : EuclideanSpace ℝ (Fin n) => Lmap y) := by
    unfold Lmap
    exact continuous_const.sub
      ((ContinuousLinearMap.smulRightL ℝ _ _
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)).continuous)
  refine (hη.comp continuous_snd).smul ?_
  exact Continuous.clm_comp (hqc.comp ((continuous_fst.comp continuous_fst).sub
    ((continuous_snd.comp continuous_fst).smul continuous_snd))) (hL.comp continuous_snd)

open MeasureTheory in
/-- `Dv` is globally `μ`-Hoelder when `Dq` is. -/
lemma vavg_fderiv_holder {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : Continuous η) (μ M : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hM : 0 ≤ M)
    (hqH : ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) :
    ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ,
      ‖fderiv ℝ (vavg q η) p - fderiv ℝ (vavg q η) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  set B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hB
  obtain ⟨Cη, hCη⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).bddAbove_image
    hη.norm.continuousOn
  set C := max Cη 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hηb : ∀ y ∈ B, ‖η y‖ ≤ C := fun y hy => (hCη ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  set vol := volume.real B with hvol
  have hvol0 : 0 ≤ vol := measureReal_nonneg
  refine ⟨C * (M * 2) * 2 * vol, fun p p' => ?_⟩
  set F' := fun (p : EuclideanSpace ℝ (Fin n) × ℝ) (y : EuclideanSpace ℝ (Fin n)) =>
    η y • (fderiv ℝ q (p.1 - p.2 • y)).comp (Lmap y) with hF'
  have hcont := vavg_F'_cont q η hq hη
  have hint : ∀ p, IntegrableOn (F' p) B := fun p =>
    ((hcont.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  rw [(vavg_hasFDerivAt q η hq hη p).fderiv, (vavg_hasFDerivAt q η hq hη p').fderiv,
    ← integral_sub (hint p) (hint p')]
  set h := ‖p - p'‖ with hh
  have hh0 : 0 ≤ h := norm_nonneg _
  have e2 : (2 * h) ^ μ ≤ 2 * h ^ μ := by
    rw [Real.mul_rpow (by norm_num) hh0]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hh0 _)
    calc (2 : ℝ) ^ μ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hμ1
      _ = 2 := Real.rpow_one 2
  have hpt : ∀ y ∈ B, ‖F' p y - F' p' y‖ ≤ C * (M * 2) * 2 * h ^ μ := by
    intro y hy
    have hy1 : ‖y‖ ≤ 1 := by simpa [hB] using hy
    have hLy : ‖Lmap y‖ ≤ 2 := (Lmap_norm_le y).trans (by linarith)
    have ha : ‖(p.1 - p.2 • y) - (p'.1 - p'.2 • y)‖ ≤ 2 * h := by
      have : (p.1 - p.2 • y) - (p'.1 - p'.2 • y) = Lmap y (p - p') := by
        rw [Lmap_apply]; simp only [Prod.fst_sub, Prod.snd_sub, sub_smul]; abel
      rw [this]
      exact ((Lmap y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hLy hh0)
    have hDq : ‖fderiv ℝ q (p.1 - p.2 • y) - fderiv ℝ q (p'.1 - p'.2 • y)‖ ≤ M * (2 * h ^ μ) :=
      (hqH _ _).trans (mul_le_mul_of_nonneg_left
        ((Real.rpow_le_rpow (norm_nonneg _) ha hμ.le).trans e2) hM)
    have : F' p y - F' p' y = η y • ((fderiv ℝ q (p.1 - p.2 • y) -
        fderiv ℝ q (p'.1 - p'.2 • y)).comp (Lmap y)) := by
      simp only [hF', ContinuousLinearMap.sub_comp, smul_sub]
    rw [this, norm_smul]
    calc ‖η y‖ * ‖(fderiv ℝ q (p.1 - p.2 • y) - fderiv ℝ q (p'.1 - p'.2 • y)).comp (Lmap y)‖
        ≤ C * (M * (2 * h ^ μ) * 2) := by
          refine mul_le_mul (hηb y hy) ?_ (norm_nonneg _) hC0
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          exact mul_le_mul hDq hLy (norm_nonneg _) (by positivity)
      _ = C * (M * 2) * 2 * h ^ μ := by ring
  calc ‖∫ y in B, (F' p y - F' p' y)‖ ≤ C * (M * 2) * 2 * h ^ μ * vol :=
        norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top hpt
    _ = C * (M * 2) * 2 * vol * h ^ μ := by ring

end Pd67abb68C2a


namespace Pd67abb68C2k

open MeasureTheory

/-- Rescaled kernel `Φ (x, t) = t^{-n} Θ (x / t)`. -/
noncomputable def Phi {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (p : EuclideanSpace ℝ (Fin n) × ℝ) : X :=
  (p.2 ^ n)⁻¹ • Θ (p.2⁻¹ • p.1)

lemma isOpen_upper {E : Type*} [NormedAddCommGroup E] : IsOpen {p : E × ℝ | 0 < p.2} :=
  isOpen_lt continuous_const continuous_snd

lemma Phi_contDiffOn {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (hΘ : ContDiff ℝ 2 Θ) :
    ContDiffOn ℝ 2 (Phi Θ) {p | 0 < p.2} := by
  intro p hp
  have hp' : p.2 ≠ 0 := ne_of_gt hp
  apply ContDiffAt.contDiffWithinAt
  unfold Phi
  have h1 : ContDiffAt ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.2⁻¹) p :=
    (contDiffAt_inv ℝ hp').comp p contDiffAt_snd
  have h2 : ContDiffAt ℝ 2 (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.2 ^ n)⁻¹) p :=
    (contDiffAt_inv ℝ (pow_ne_zero n hp')).comp p (contDiffAt_snd.pow n)
  exact h2.smul (hΘ.contDiffAt.comp p (h1.smul contDiffAt_fst))

lemma Phi_eq_zero {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (hsupp : ∀ y, 1 < ‖y‖ → Θ y = 0)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) (h : p.2 < ‖p.1‖) : Phi Θ p = 0 := by
  unfold Phi
  rw [hsupp _ ?_, smul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hp, lt_inv_mul_iff₀ hp, mul_one]
  exact h

lemma Phi_smul {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (c : ℝ) (hc : 0 < c)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) :
    Phi Θ (c • p) = (c ^ n)⁻¹ • Phi Θ p := by
  unfold Phi
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have : (c * p.2)⁻¹ • (c • p.1) = p.2⁻¹ • p.1 := by
    rw [smul_smul]; congr 1; field_simp
  rw [this, mul_pow, mul_inv, mul_smul]

/-- Derivative of a homogeneous function. -/
lemma fderiv_homog {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : F → X) (U : Set F) (hU : IsOpen U) (c a : ℝ) (hc : 0 < c)
    (hf : ∀ p ∈ U, f (c • p) = a • f p)
    (p : F) (hp : p ∈ U) (hd : DifferentiableAt ℝ f (c • p)) (hdp : DifferentiableAt ℝ f p) :
    fderiv ℝ f (c • p) = (c⁻¹ * a) • fderiv ℝ f p := by
  have h1 : (fun x => f (c • x)) =ᶠ[nhds p] fun x => a • f x :=
    Filter.eventually_of_mem (hU.mem_nhds hp) (fun x hx => hf x hx)
  have h2' : HasFDerivAt (fun x => f (c • x))
      ((fderiv ℝ f (c • p)).comp (c • ContinuousLinearMap.id ℝ F)) p :=
    hd.hasFDerivAt.comp p ((hasFDerivAt_id p).const_smul c)
  have h2 : fderiv ℝ (fun x => f (c • x)) p = c • fderiv ℝ f (c • p) := by
    rw [h2'.fderiv]; ext v; simp
  have h3 : fderiv ℝ (fun x => a • f x) p = a • fderiv ℝ f p := fderiv_const_smul hdp a
  have key : c • fderiv ℝ f (c • p) = a • fderiv ℝ f p := by rw [← h2, h1.fderiv_eq, h3]
  calc fderiv ℝ f (c • p) = c⁻¹ • (c • fderiv ℝ f (c • p)) := by
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    _ = (c⁻¹ * a) • fderiv ℝ f p := by rw [key, smul_smul]

/-- A function homogeneous of degree `-k` on the upper half-space, vanishing outside the cone
`‖x‖ ≤ t`, is bounded by `C t^{-k}`. -/
lemma bound_of_homog {n k : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (g : EuclideanSpace ℝ (Fin n) × ℝ → Y) (hg : ContinuousOn g {p | 0 < p.2})
    (hz : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → g p = 0)
    (hh : ∀ c : ℝ, 0 < c → ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      g (c • p) = (c ^ k)⁻¹ • g p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → ‖g p‖ ≤ C * (p.2 ^ k)⁻¹ := by
  have hc1 : ContinuousOn (fun y : EuclideanSpace ℝ (Fin n) => g (y, 1))
      (Metric.closedBall 0 1) := by
    refine hg.comp (Continuous.prodMk continuous_id continuous_const).continuousOn ?_
    intro y _; show (0 : ℝ) < 1; norm_num
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_bound_of_continuousOn hc1
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  set t := p.2 with ht
  set y := t⁻¹ • p.1 with hy
  have hpe : p = t • (y, (1 : ℝ)) := by
    ext
    · simp only [Prod.smul_fst, hy, smul_smul, mul_inv_cancel₀ hp.ne', one_smul]
    · simp [ht]
  have hgy : ‖g (y, 1)‖ ≤ max C 0 := by
    by_cases hy1 : ‖y‖ ≤ 1
    · exact (hC y (by simpa using hy1)).trans (le_max_left _ _)
    · rw [hz (y, 1) (by norm_num) (lt_of_not_ge hy1)]; simp
  rw [hpe, hh t hp (y, 1) (by norm_num), norm_smul, norm_inv, norm_pow, Real.norm_eq_abs,
    abs_of_pos hp, mul_comm]
  exact mul_le_mul_of_nonneg_right hgy (by positivity)

lemma fderiv_eq_zero_of_eventually {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (f : F → X) (V : Set F) (hV : IsOpen V)
    (hf : ∀ p ∈ V, f p = 0) (p : F) (hp : p ∈ V) : fderiv ℝ f p = 0 := by
  have : f =ᶠ[nhds p] fun _ => 0 := Filter.eventually_of_mem (hV.mem_nhds hp) hf
  rw [this.fderiv_eq]; simp

lemma isOpen_cone {n : ℕ} :
    IsOpen {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2 ∧ p.2 < ‖p.1‖} :=
  (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd (continuous_norm.comp continuous_fst))

/-- Bounds on `DΦ` and `D²Φ`. -/
lemma Phi_deriv_bounds {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (hΘ : ContDiff ℝ 2 Θ)
    (hsupp : ∀ y, 1 < ‖y‖ → Θ y = 0) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      ‖fderiv ℝ (Phi Θ) p‖ ≤ C * (p.2 ^ (n + 1))⁻¹) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      ‖fderiv ℝ (fderiv ℝ (Phi Θ)) p‖ ≤ C * (p.2 ^ (n + 2))⁻¹) := by
  set U : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | 0 < p.2} with hU
  have hUo : IsOpen U := isOpen_upper
  have h2 := Phi_contDiffOn Θ hΘ
  have hD1 : ContDiffOn ℝ 1 (fun p => fderiv ℝ (Phi Θ) p) U :=
    h2.fderiv_of_isOpen hUo (by norm_num)
  have hc1 : ContinuousOn (fderiv ℝ (Phi Θ)) U := hD1.continuousOn
  have hc2 : ContinuousOn (fderiv ℝ (fderiv ℝ (Phi Θ))) U :=
    hD1.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hdiff0 : ∀ p ∈ U, DifferentiableAt ℝ (Phi Θ) p := fun p hp =>
    ((h2.differentiableOn (by norm_num)) p hp).differentiableAt (hUo.mem_nhds hp)
  have hdiff1 : ∀ p ∈ U, DifferentiableAt ℝ (fderiv ℝ (Phi Θ)) p := fun p hp =>
    ((hD1.differentiableOn one_ne_zero) p hp).differentiableAt (hUo.mem_nhds hp)
  have hsmU : ∀ c : ℝ, 0 < c → ∀ p ∈ U, c • p ∈ U := fun c hc p hp => by
    show 0 < c * p.2; exact mul_pos hc hp
  have hz0 : ∀ p ∈ {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2 ∧ p.2 < ‖p.1‖},
      Phi Θ p = 0 := fun p hp => Phi_eq_zero Θ hsupp p hp.1 hp.2
  have hz1 : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ →
      fderiv ℝ (Phi Θ) p = 0 := fun p hp h =>
    fderiv_eq_zero_of_eventually _ _ isOpen_cone hz0 p ⟨hp, h⟩
  have hz2 : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ →
      fderiv ℝ (fderiv ℝ (Phi Θ)) p = 0 := fun p hp h =>
    fderiv_eq_zero_of_eventually _ _ isOpen_cone (fun p hp => hz1 p hp.1 hp.2) p ⟨hp, h⟩
  have hh1 : ∀ c : ℝ, 0 < c → ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      fderiv ℝ (Phi Θ) (c • p) = (c ^ (n + 1))⁻¹ • fderiv ℝ (Phi Θ) p := by
    intro c hc p hp
    rw [fderiv_homog (Phi Θ) U hUo c ((c ^ n)⁻¹) hc (fun p hp => Phi_smul Θ c hc p hp) p hp
      (hdiff0 _ (hsmU c hc p hp)) (hdiff0 p hp), pow_succ, mul_inv, mul_comm]
  have hh2 : ∀ c : ℝ, 0 < c → ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      fderiv ℝ (fderiv ℝ (Phi Θ)) (c • p) =
        (c ^ (n + 2))⁻¹ • fderiv ℝ (fderiv ℝ (Phi Θ)) p := by
    intro c hc p hp
    rw [fderiv_homog (fderiv ℝ (Phi Θ)) U hUo c ((c ^ (n + 1))⁻¹) hc
      (fun p hp => hh1 c hc p hp) p hp (hdiff1 _ (hsmU c hc p hp)) (hdiff1 p hp),
      pow_succ c (n + 1), mul_inv, mul_comm]
  exact ⟨bound_of_homog (k := n + 1) (fderiv ℝ (Phi Θ)) hc1 hz1 hh1, bound_of_homog (k := n + 2) (fderiv ℝ (fderiv ℝ (Phi Θ))) hc2 hz2 hh2⟩

/-- The kernel has the same total integral at every scale. -/
lemma integral_Phi {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (Θ : EuclideanSpace ℝ (Fin n) → X) (t : ℝ) (ht : 0 < t) :
    ∫ x, Phi Θ (x, t) = ∫ y, Θ y := by
  unfold Phi
  simp only
  rw [integral_smul, Measure.integral_comp_smul, finrank_euclideanSpace_fin, smul_smul,
    inv_pow, inv_inv, abs_of_pos (pow_pos ht n), inv_mul_cancel₀ (pow_pos ht n).ne', one_smul]

lemma sub_pair {n : ℕ} (p : EuclideanSpace ℝ (Fin n) × ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    p - (w, 0) = (p.1 - w, p.2) := by ext <;> simp

/-- Differentiation of a translated-kernel integral in the upper half-space. -/
lemma hasFDerivAt_shift_integral {n : ℕ} {Y X Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [CompleteSpace Z]
    (L : Y →L[ℝ] X →L[ℝ] Z) (f : EuclideanSpace ℝ (Fin n) → Y) (hf : Continuous f)
    (Ψ : EuclideanSpace ℝ (Fin n) × ℝ → X) (hΨ : ContDiffOn ℝ 1 Ψ {p | 0 < p.2})
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
    (p₀ : EuclideanSpace ℝ (Fin n) × ℝ) (hp₀ : 0 < p₀.2) :
    HasFDerivAt (fun p => ∫ w in S, L (f w) (Ψ (p - (w, 0))))
      (∫ w in S, (L (f w)).comp (fderiv ℝ Ψ (p₀ - (w, 0)))) p₀ := by
  set U : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | 0 < p.2} with hU
  have hUo : IsOpen U := isOpen_upper
  have hΨc : ContinuousOn Ψ U := hΨ.continuousOn
  have hDc : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hΨd : ∀ p ∈ U, HasFDerivAt Ψ (fderiv ℝ Ψ p) p := fun p hp =>
    (((hΨ.differentiableOn one_ne_zero) p hp).differentiableAt (hUo.mem_nhds hp)).hasFDerivAt
  set r := p₀.2 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hmem : ∀ p ∈ Metric.closedBall p₀ r, ∀ w : EuclideanSpace ℝ (Fin n), p - (w, 0) ∈ U := by
    intro p hp w
    show 0 < (p - (w, 0)).2
    have h1 : ‖(p - p₀).2‖ ≤ ‖p - p₀‖ := norm_snd_le _
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    have h2 : |p.2 - p₀.2| ≤ r := by simpa [Real.norm_eq_abs] using h1.trans hp
    simp only [Prod.snd_sub, sub_zero]
    have := (abs_le.mp h2).1
    linarith
  set F' : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] Z) :=
    fun p w => (L (f w)).comp (fderiv ℝ Ψ (p - (w, 0))) with hF'
  have hF'c : ContinuousOn
      (fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × EuclideanSpace ℝ (Fin n) => F' pw.1 pw.2)
      (Metric.closedBall p₀ r ×ˢ S) := by
    have hg : ContinuousOn
        (fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × EuclideanSpace ℝ (Fin n) =>
          fderiv ℝ Ψ (pw.1 - (pw.2, 0))) (Metric.closedBall p₀ r ×ˢ S) :=
      hDc.comp (Continuous.continuousOn (by fun_prop)) (fun pw hpw => hmem pw.1 hpw.1 pw.2)
    exact ((L.continuous.comp (hf.comp continuous_snd)).continuousOn).clm_comp hg
  obtain ⟨C, hC⟩ := ((isCompact_closedBall p₀ r).prod hS).exists_bound_of_continuousOn hF'c
  have hcontw : ∀ p ∈ Metric.closedBall p₀ r,
      Continuous (fun w => L (f w) (Ψ (p - (w, 0)))) := by
    intro p hp
    have hΨw : Continuous (fun w : EuclideanSpace ℝ (Fin n) => Ψ (p - (w, 0))) :=
      hΨc.comp_continuous (by fun_prop) (fun w => hmem p hp w)
    exact (L.continuous.comp hf).clm_apply hΨw
  have hp₀m : p₀ ∈ Metric.closedBall p₀ r := Metric.mem_closedBall_self hr0.le
  have hμs : volume S ≠ ⊤ := hS.measure_lt_top.ne
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict S)
    (F' := F') (bound := fun _ => C) (Metric.ball_mem_nhds p₀ hr0) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.eventually_of_mem (Metric.ball_mem_nhds p₀ hr0) (fun p hp =>
      (hcontw p (Metric.ball_subset_closedBall hp)).aestronglyMeasurable)
  · exact (hcontw p₀ hp₀m).continuousOn.integrableOn_compact hS
  · have : Continuous (fun w => F' p₀ w) :=
      (L.continuous.comp hf).clm_comp (hDc.comp_continuous (by fun_prop) (fun w => hmem p₀ hp₀m w))
    exact this.aestronglyMeasurable
  · rw [ae_restrict_iff' hS.measurableSet]
    exact Filter.Eventually.of_forall (fun w hw p hp =>
      hC (p, w) ⟨Metric.ball_subset_closedBall hp, hw⟩)
  · exact integrableOn_const hμs
  · refine Filter.Eventually.of_forall (fun w p hp => ?_)
    have h1 := (L (f w)).hasFDerivAt.comp p ((hΨd _ (hmem p (Metric.ball_subset_closedBall hp) w)).comp p
      ((hasFDerivAt_id p).sub_const (w, 0)))
    exact h1.congr_fderiv (by simp only [ContinuousLinearMap.comp_id, hF'])

lemma shift_integral_eq {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X]
    (Ψ : EuclideanSpace ℝ (Fin n) × ℝ → X)
    (hz : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → Ψ p = 0)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) (R : ℝ) (hR : ‖p.1‖ + p.2 ≤ R) :
    ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, Ψ (p - (w, 0)) =
      ∫ x, Ψ (x, p.2) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [sub_pair]
    exact integral_sub_left_eq_self (fun x => Ψ (x, p.2)) volume p.1
  · intro w hw
    rw [sub_pair]
    refine hz _ hp ?_
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hw
    have := norm_sub_norm_le w p.1
    rw [norm_sub_rev w p.1] at this
    show p.2 < ‖p.1 - w‖
    linarith

/-- Cancellation: integrating the kernel derivative against a constant gives zero. -/
lemma shift_integral_const_deriv {n : ℕ} {Y X Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z]
    (L : Y →L[ℝ] X →L[ℝ] Z) (c : Y)
    (Ψ : EuclideanSpace ℝ (Fin n) × ℝ → X) (hΨ : ContDiffOn ℝ 1 Ψ {p | 0 < p.2})
    (hz : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → Ψ p = 0)
    (A : X) (hA : ∀ t : ℝ, 0 < t → ∫ x, Ψ (x, t) = A)
    (p₀ : EuclideanSpace ℝ (Fin n) × ℝ) (hp₀ : 0 < p₀.2) (R : ℝ) (hR : ‖p₀.1‖ + p₀.2 + 1 ≤ R) :
    ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      (L c).comp (fderiv ℝ Ψ (p₀ - (w, 0))) = 0 := by
  have hd := hasFDerivAt_shift_integral L (fun _ => c) continuous_const Ψ hΨ
    (Metric.closedBall 0 R) (isCompact_closedBall _ _) p₀ hp₀
  have hU : IsOpen {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2 ∧ ‖p.1‖ + p.2 < ‖p₀.1‖ + p₀.2 + 1} :=
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt ((continuous_norm.comp continuous_fst).add continuous_snd) continuous_const)
  have hp₀U : p₀ ∈ {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2 ∧ ‖p.1‖ + p.2 < ‖p₀.1‖ + p₀.2 + 1} :=
    ⟨hp₀, by linarith⟩
  have hev : (fun p => ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      L c (Ψ (p - (w, 0)))) =ᶠ[nhds p₀] fun _ => L c A := by
    refine Filter.eventually_of_mem (hU.mem_nhds hp₀U) (fun p hp => ?_)
    have hcont : Continuous (fun w : EuclideanSpace ℝ (Fin n) => Ψ (p - (w, 0))) :=
      hΨ.continuousOn.comp_continuous (by fun_prop) (fun w => by
        show 0 < (p - (w, 0)).2; simpa using hp.1)
    show ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, L c (Ψ (p - (w, 0))) = L c A
    rw [ContinuousLinearMap.integral_comp_comm _
      (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _)),
      shift_integral_eq Ψ hz p hp.1 R (by linarith [hp.2]), hA p.2 hp.1]
  have h0 := hd.fderiv
  rw [hev.fderiv_eq] at h0
  rw [← h0]; simp

lemma vol_closedBall {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) (t : ℝ) (ht : 0 ≤ t) :
    volume.real (Metric.closedBall z t) =
      t ^ n * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [measureReal_def, measureReal_def, Measure.addHaar_closedBall' volume z ht,
    finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht n)]

/-- The singular-integral bound: against a `μ`-Hoelder density, the kernel derivative of
order `k` integrates to `O(t^(μ + n - k))`. -/
lemma shift_integral_bound {n : ℕ} {Y X Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z]
    (L : Y →L[ℝ] X →L[ℝ] Z) (g : EuclideanSpace ℝ (Fin n) → Y) (hg : Continuous g)
    (μ M : ℝ) (hμ : 0 < μ) (hM : 0 ≤ M) (hgH : ∀ x y, ‖g x - g y‖ ≤ M * ‖x - y‖ ^ μ)
    (Rg : ℝ) (hgs : ∀ w, Rg < ‖w‖ → g w = 0)
    (Ψ : EuclideanSpace ℝ (Fin n) × ℝ → X) (hΨ : ContDiffOn ℝ 1 Ψ {p | 0 < p.2})
    (hz : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → Ψ p = 0)
    (A : X) (hA : ∀ t : ℝ, 0 < t → ∫ x, Ψ (x, t) = A)
    (C : ℝ) (k : ℕ) (hC0 : 0 ≤ C)
    (hC : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → ‖fderiv ℝ Ψ p‖ ≤ C * (p.2 ^ k)⁻¹)
    (p₀ : EuclideanSpace ℝ (Fin n) × ℝ) (hp₀ : 0 < p₀.2) :
    ‖∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rg,
        (L (g w)).comp (fderiv ℝ Ψ (p₀ - (w, 0)))‖ ≤
      ‖L‖ * M * C * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) *
        p₀.2 ^ μ * p₀.2 ^ n * (p₀.2 ^ k)⁻¹ := by
  set z := p₀.1 with hzdef
  set t := p₀.2 with htdef
  set R := max Rg (‖z‖ + t + 1) with hR
  set U : Set (EuclideanSpace ℝ (Fin n) × ℝ) := {p | 0 < p.2} with hU
  have hUo : IsOpen U := isOpen_upper
  have hDc : ContinuousOn (fderiv ℝ Ψ) U := hΨ.continuousOn_fderiv_of_isOpen hUo le_rfl
  have hDz : ∀ w : EuclideanSpace ℝ (Fin n), t < ‖z - w‖ → fderiv ℝ Ψ (p₀ - (w, 0)) = 0 := by
    intro w hw
    refine fderiv_eq_zero_of_eventually Ψ _ isOpen_cone (fun p hp => hz p hp.1 hp.2) _ ?_
    rw [sub_pair]; exact ⟨hp₀, hw⟩
  have hDcw : Continuous (fun w : EuclideanSpace ℝ (Fin n) => fderiv ℝ Ψ (p₀ - (w, 0))) :=
    hDc.comp_continuous (by fun_prop) (fun w => by
      show 0 < (p₀ - (w, 0)).2; simpa using hp₀)
  set F := fun w => (L (g w)).comp (fderiv ℝ Ψ (p₀ - (w, 0))) with hF
  set G := fun w => (L (g z)).comp (fderiv ℝ Ψ (p₀ - (w, 0))) with hG
  have hFc : Continuous F := (L.continuous.comp hg).clm_comp hDcw
  have hGc : Continuous G := continuous_const.clm_comp hDcw
  have hG0 : ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, G w = 0 :=
    shift_integral_const_deriv L (g z) Ψ hΨ hz A hA p₀ hp₀ R (le_max_right _ _)
  have hsub1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rg ⊆ Metric.closedBall 0 R :=
    Metric.closedBall_subset_closedBall (le_max_left _ _)
  have h1 : ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rg, F w =
      ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, F w := by
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isClosed_closedBall.measurableSet
      hsub1 (fun w hw => ?_)).symm
    have : Rg < ‖w‖ := by
      have := hw.2; simpa [Metric.mem_closedBall, dist_zero_right, not_le] using this
    simp [hF, hgs w this]
  have hBR : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := isCompact_closedBall _ _
  have h2 : ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, F w =
      ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (F w - G w) := by
    rw [integral_sub (hFc.continuousOn.integrableOn_compact hBR)
      (hGc.continuousOn.integrableOn_compact hBR), hG0, sub_zero]
  have hsub2 : Metric.closedBall z t ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have := norm_le_insert' w z
    have h4 : ‖z‖ + t + 1 ≤ R := le_max_right _ _
    linarith
  have h3 : ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R, (F w - G w) =
      ∫ w in Metric.closedBall z t, (F w - G w) := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero Metric.isClosed_closedBall.measurableSet
      hsub2 (fun w hw => ?_)
    have : t < ‖z - w‖ := by
      have := hw.2
      rw [Metric.mem_closedBall, dist_eq_norm, not_le, norm_sub_rev] at this
      exact this
    simp [hF, hG, hDz w this]
  rw [h1, h2, h3]
  have hbd : ∀ w ∈ Metric.closedBall z t, ‖F w - G w‖ ≤ ‖L‖ * (M * t ^ μ) * (C * (t ^ k)⁻¹) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have e : F w - G w = (L (g w - g z)).comp (fderiv ℝ Ψ (p₀ - (w, 0))) := by
      simp only [hF, hG, map_sub, ContinuousLinearMap.sub_comp]
    rw [e]
    have hgw : ‖g w - g z‖ ≤ M * t ^ μ :=
      (hgH w z).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hw hμ.le) hM)
    have hD : ‖fderiv ℝ Ψ (p₀ - (w, 0))‖ ≤ C * (t ^ k)⁻¹ := by
      have := hC (p₀ - (w, 0)) (by simpa using hp₀); simpa using this
    calc ‖(L (g w - g z)).comp (fderiv ℝ Ψ (p₀ - (w, 0)))‖
        ≤ ‖L (g w - g z)‖ * ‖fderiv ℝ Ψ (p₀ - (w, 0))‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖L‖ * ‖g w - g z‖) * ‖fderiv ℝ Ψ (p₀ - (w, 0))‖ :=
          mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)
      _ ≤ (‖L‖ * (M * t ^ μ)) * (C * (t ^ k)⁻¹) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hgw (norm_nonneg L)) hD (norm_nonneg _)
            (mul_nonneg (norm_nonneg L) (mul_nonneg hM (Real.rpow_nonneg hp₀.le _)))
  calc ‖∫ w in Metric.closedBall z t, (F w - G w)‖
      ≤ ‖L‖ * (M * t ^ μ) * (C * (t ^ k)⁻¹) * volume.real (Metric.closedBall z t) :=
        norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top hbd
    _ = _ := by rw [vol_closedBall z t hp₀.le]; ring

lemma shift_integral_bound' {n : ℕ} {Y X Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [CompleteSpace Z]
    (L : Y →L[ℝ] X →L[ℝ] Z) (g : EuclideanSpace ℝ (Fin n) → Y) (hg : Continuous g)
    (μ M : ℝ) (hμ : 0 < μ) (hM : 0 ≤ M) (hgH : ∀ x y, ‖g x - g y‖ ≤ M * ‖x - y‖ ^ μ)
    (Rg : ℝ) (hgs : ∀ w, Rg < ‖w‖ → g w = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ψ : EuclideanSpace ℝ (Fin n) × ℝ → X), ContDiffOn ℝ 1 Ψ {p | 0 < p.2} →
      (∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → Ψ p = 0) →
      ∀ (A : X), (∀ t : ℝ, 0 < t → ∫ x, Ψ (x, t) = A) →
      ∀ (C : ℝ) (k : ℕ), 0 ≤ C →
      (∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → ‖fderiv ℝ Ψ p‖ ≤ C * (p.2 ^ k)⁻¹) →
      ∀ p₀ : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p₀.2 →
      ‖∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rg,
        (L (g w)).comp (fderiv ℝ Ψ (p₀ - (w, 0)))‖ ≤ K * C * p₀.2 ^ μ * p₀.2 ^ n * (p₀.2 ^ k)⁻¹ :=
  ⟨‖L‖ * M * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
    by positivity, fun Ψ hΨ hz A hA C k hC0 hC p₀ hp₀ => by
      have := shift_integral_bound L g hg μ M hμ hM hgH Rg hgs Ψ hΨ hz A hA C k hC0 hC p₀ hp₀
      calc _ ≤ _ := this
        _ = _ := by ring⟩

lemma fderiv_Phi_zero {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Θ : EuclideanSpace ℝ (Fin n) → X) (hsupp : ∀ y, 1 < ‖y‖ → Θ y = 0) :
    ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → fderiv ℝ (Phi Θ) p = 0 :=
  fun p hp h => fderiv_eq_zero_of_eventually _ _ isOpen_cone
    (fun p hp => Phi_eq_zero Θ hsupp p hp.1 hp.2) p ⟨hp, h⟩

/-- The kernel derivative has zero total integral. -/
lemma integral_fderiv_Phi {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (Θ : EuclideanSpace ℝ (Fin n) → X) (hΘ : ContDiff ℝ 2 Θ)
    (hsupp : ∀ y, 1 < ‖y‖ → Θ y = 0) (t : ℝ) (ht : 0 < t) :
    ∫ x, fderiv ℝ (Phi Θ) (x, t) = 0 := by
  set p₀ : EuclideanSpace ℝ (Fin n) × ℝ := (0, t) with hp₀
  have h1 := shift_integral_const_deriv (ContinuousLinearMap.lsmul ℝ ℝ) (1 : ℝ) (Phi Θ)
    ((Phi_contDiffOn Θ hΘ).of_le (by norm_num)) (fun p hp h => Phi_eq_zero Θ hsupp p hp h)
    (∫ y, Θ y) (fun t ht => integral_Phi _ t ht) p₀ ht (‖p₀.1‖ + p₀.2 + 1) le_rfl
  have e : ∀ T : EuclideanSpace ℝ (Fin n) × ℝ →L[ℝ] X,
      ((ContinuousLinearMap.lsmul ℝ ℝ) (1 : ℝ)).comp T = T := by
    intro T; ext <;> simp
  simp only [e] at h1
  rw [shift_integral_eq (fun p => fderiv ℝ (Phi Θ) p) (fderiv_Phi_zero Θ hsupp) p₀ ht
    _ (by linarith)] at h1
  exact h1

lemma setIntegral_clm_apply {n : ℕ} {A Z : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (F : EuclideanSpace ℝ (Fin n) → A →L[ℝ] Z) (hF : Continuous F)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) (u : A) :
    (∫ w in S, F w) u = ∫ w in S, F w u :=
  ContinuousLinearMap.integral_apply (hF.continuousOn.integrableOn_compact hS) u

end Pd67abb68C2k


namespace Pd67abb68C2v

open MeasureTheory Pd67abb68C2a Pd67abb68C2k

/-- The kernel profile `Θ y = (η y, η y • y)` (values in `ℝ × E` keep derivative types shallow). -/
noncomputable def Th {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ℝ × EuclideanSpace ℝ (Fin n) :=
  (η y, η y • y)

lemma Th_contDiff {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η) :
    ContDiff ℝ 2 (Th η) := hη.prodMk (hη.smul contDiff_id)

lemma Th_supp {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) :
    ∀ y, 1 < ‖y‖ → Th η y = 0 := fun y hy => by simp [Th, hsupp y hy]

/-- `Mb a x = x.1 • (a ∘ fst) - (a x.2) • snd`. -/
noncomputable def Mb (n : ℕ) : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ]
    (ℝ × EuclideanSpace ℝ (Fin n)) →L[ℝ] ((EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] ℝ) :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (x : ℝ × EuclideanSpace ℝ (Fin n)) =>
        x.1 • a.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) -
          a x.2 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ)
      (fun a a' x => by
        refine ContinuousLinearMap.ext fun u => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul]
        ring)
      (fun c a x => by
        refine ContinuousLinearMap.ext fun u => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul]
        ring)
      (fun a x x' => by
        refine ContinuousLinearMap.ext fun u => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul]
        ring)
      (fun c a x => by
        refine ContinuousLinearMap.ext fun u => ?_
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
          ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, map_add, map_smul, smul_eq_mul]
        ring))
    2 (fun a x => by
      simp only [LinearMap.mk₂_apply]
      have h1 : ‖a.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)‖ ≤ ‖a‖ :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_fst_le _ _ _))
      have h2 : ‖ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ‖ ≤ 1 :=
        ContinuousLinearMap.norm_snd_le _ _ _
      have h3 : ‖x.1‖ ≤ ‖x‖ := norm_fst_le x
      have h4 : ‖x.2‖ ≤ ‖x‖ := norm_snd_le x
      have h5 : ‖a x.2‖ ≤ ‖a‖ * ‖x.2‖ := a.le_opNorm _
      calc ‖x.1 • a.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ) -
            a x.2 • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ‖
          ≤ ‖x.1‖ * ‖a.comp (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) ℝ)‖ +
            ‖a x.2‖ * ‖ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_smul, norm_smul]
        _ ≤ ‖x‖ * ‖a‖ + (‖a‖ * ‖x‖) * 1 := by
            gcongr
            exact h5.trans (mul_le_mul_of_nonneg_left h4 (norm_nonneg _))
        _ = 2 * ‖a‖ * ‖x‖ := by ring)

lemma Mb_apply {n : ℕ} (a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (x : ℝ × EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n) × ℝ) : Mb n a x u = x.1 * a u.1 - a x.2 * u.2 := by
  simp [Mb]

/-- Kernel representation of `Dv` in the upper half-space. -/
lemma fderiv_vavg_rep {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : Continuous η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) :
    fderiv ℝ (vavg q η) p = ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rq,
      Mb n (fderiv ℝ q w) (Phi (Th η) (p - (w, 0))) := by
  rw [(vavg_hasFDerivAt q η hq hη p).fderiv]
  set z := p.1 with hz
  set t := p.2 with ht
  have e1 : ∀ y, η y • (fderiv ℝ q (z - t • y)).comp (Lmap y) =
      Mb n (fderiv ℝ q (z - t • y)) (Th η y) := by
    intro y; ext u <;> simp [Mb_apply, Th, Lmap_apply] <;> ring
  have hA : ∫ y in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      η y • (fderiv ℝ q (z - t • y)).comp (Lmap y) =
      ∫ y, Mb n (fderiv ℝ q (z - t • y)) (Th η y) := by
    simp_rw [e1]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have : 1 < ‖y‖ := by simpa using hy
    simp [Th_supp η hsupp y this]
  set h : EuclideanSpace ℝ (Fin n) → _ := fun w =>
    Mb n (fderiv ℝ q w) ((t ^ n)⁻¹ • Th η (t⁻¹ • (z - w))) with hh
  set f : EuclideanSpace ℝ (Fin n) → _ := fun w =>
    Mb n (fderiv ℝ q (z - w)) ((t ^ n)⁻¹ • Th η (t⁻¹ • w)) with hf
  have hb1 : ∫ w, h w = ∫ w, f w := by
    rw [← integral_sub_left_eq_self h volume z]; congr 1; funext w; simp [hh, hf]
  have hb2 : ∫ y, f (t • y) = (t ^ n)⁻¹ • ∫ y, Mb n (fderiv ℝ q (z - t • y)) (Th η y) := by
    rw [← integral_smul]; congr 1; funext y
    simp [hf, smul_smul, inv_mul_cancel₀ hp.ne', map_smul]
  have hb3 : ∫ y, f (t • y) = (t ^ n)⁻¹ • ∫ w, f w := by
    rw [Measure.integral_comp_smul, finrank_euclideanSpace_fin,
      abs_of_pos (inv_pos.mpr (pow_pos hp n))]
  have hb : ∫ w, f w = ∫ y, Mb n (fderiv ℝ q (z - t • y)) (Th η y) :=
    smul_right_injective _ (inv_ne_zero (pow_ne_zero n hp.ne')) (hb3.symm.trans hb2)
  have hc : ∫ w, h w = ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rq,
      Mb n (fderiv ℝ q w) (Phi (Th η) (p - (w, 0))) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1; funext w; simp [hh, Phi, sub_pair, ← hz, ← ht]
    · intro w hw
      have : Rq < ‖w‖ := by simpa using hw
      simp [hqs w this]
  rw [hA, ← hb, ← hb1, hc]

lemma Phi_Th_contDiffOn {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η) :
    ContDiffOn ℝ 2 (Phi (Th η)) {p | 0 < p.2} := Phi_contDiffOn _ (Th_contDiff η hη)

/-- Second derivative of `v` in the upper half-space. -/
lemma hasFDerivAt_fderiv_vavg {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0)
    (p₀ : EuclideanSpace ℝ (Fin n) × ℝ) (hp₀ : 0 < p₀.2) :
    HasFDerivAt (fderiv ℝ (vavg q η))
      (∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rq,
        (Mb n (fderiv ℝ q w)).comp (fderiv ℝ (Phi (Th η)) (p₀ - (w, 0)))) p₀ := by
  have hd := hasFDerivAt_shift_integral (Mb n) (fderiv ℝ q) (hq.continuous_fderiv one_ne_zero)
    (Phi (Th η)) ((Phi_Th_contDiffOn η hη).of_le (by norm_num))
    (Metric.closedBall 0 Rq) (isCompact_closedBall _ _) p₀ hp₀
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (isOpen_upper.mem_nhds hp₀) (fun p hp =>
    fderiv_vavg_rep q η hq hη.continuous hsupp Rq hqs p hp)

/-- `|D²v| ≤ K t^μ t^n t^{-(n+1)}` in the upper half-space. -/
lemma fderiv2_vavg_bound {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0) (μ M : ℝ) (hμ : 0 < μ) (hM : 0 ≤ M)
    (hqH : ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      ‖fderiv ℝ (fderiv ℝ (vavg q η)) p‖ ≤ K * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 1))⁻¹ := by
  obtain ⟨C1, hC10, hC1⟩ := (Phi_deriv_bounds (Th η) (Th_contDiff η hη) (Th_supp η hsupp)).1
  obtain ⟨K, hK0, hK⟩ := shift_integral_bound' (Mb n) (fderiv ℝ q)
    (hq.continuous_fderiv one_ne_zero) μ M hμ hM hqH Rq hqs
  refine ⟨K * C1, mul_nonneg hK0 hC10, fun p hp => ?_⟩
  rw [(hasFDerivAt_fderiv_vavg q η hq hη hsupp Rq hqs p hp).fderiv]
  exact hK (Phi (Th η)) ((Phi_Th_contDiffOn η hη).of_le (by norm_num))
    (fun p hp h => Phi_eq_zero _ (Th_supp η hsupp) p hp h) (∫ y, Th η y)
    (fun t ht => integral_Phi _ t ht) C1 (n + 1) hC10 hC1 p hp

/-- Directional kernel `Ψ_u p = DΦ(p) u`. -/
noncomputable def Psu {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (u : EuclideanSpace ℝ (Fin n) × ℝ)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) : ℝ × EuclideanSpace ℝ (Fin n) :=
  fderiv ℝ (Phi (Th η)) p u

lemma DPhi_contDiffOn {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η) :
    ContDiffOn ℝ 1 (fun p => fderiv ℝ (Phi (Th η)) p) {p | 0 < p.2} :=
  (Phi_Th_contDiffOn η hη).fderiv_of_isOpen isOpen_upper (by norm_num)

lemma Psu_eq {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (u : EuclideanSpace ℝ (Fin n) × ℝ) :
    Psu η u = (ContinuousLinearMap.apply ℝ (ℝ × EuclideanSpace ℝ (Fin n)) u) ∘
      fderiv ℝ (Phi (Th η)) := by
  funext p; simp [Psu]

lemma Psu_contDiffOn {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η)
    (u : EuclideanSpace ℝ (Fin n) × ℝ) : ContDiffOn ℝ 1 (Psu η u) {p | 0 < p.2} := by
  rw [Psu_eq]
  exact (ContinuousLinearMap.apply ℝ (ℝ × EuclideanSpace ℝ (Fin n)) u).contDiff.comp_contDiffOn
    (DPhi_contDiffOn η hη)

lemma Psu_zero {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0)
    (u : EuclideanSpace ℝ (Fin n) × ℝ) :
    ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → p.2 < ‖p.1‖ → Psu η u p = 0 := by
  intro p hp h
  simp [Psu, fderiv_Phi_zero _ (Th_supp η hsupp) p hp h]

lemma norm_fderiv_Psu {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η)
    (u : EuclideanSpace ℝ (Fin n) × ℝ) (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) :
    ‖fderiv ℝ (Psu η u) p‖ ≤ ‖fderiv ℝ (fderiv ℝ (Phi (Th η))) p‖ * ‖u‖ := by
  have hd : DifferentiableAt ℝ (fderiv ℝ (Phi (Th η))) p :=
    (((DPhi_contDiffOn η hη).differentiableOn one_ne_zero) p hp).differentiableAt
      (isOpen_upper.mem_nhds hp)
  have h := (ContinuousLinearMap.apply ℝ (ℝ × EuclideanSpace ℝ (Fin n)) u).hasFDerivAt.comp p
    hd.hasFDerivAt
  rw [Psu_eq, h.fderiv]
  set T := fderiv ℝ (fderiv ℝ (Phi (Th η))) p
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  calc ‖T v u‖ ≤ ‖T v‖ * ‖u‖ := (T v).le_opNorm u
    _ ≤ ‖T‖ * ‖v‖ * ‖u‖ := mul_le_mul_of_nonneg_right (T.le_opNorm v) (norm_nonneg _)
    _ = ‖T‖ * ‖u‖ * ‖v‖ := by ring

lemma integral_Psu {n : ℕ} (η : EuclideanSpace ℝ (Fin n) → ℝ) (hη : ContDiff ℝ 2 η)
    (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (u : EuclideanSpace ℝ (Fin n) × ℝ) (t : ℝ) (ht : 0 < t) :
    ∫ x, Psu η u (x, t) = 0 := by
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ (Phi (Th η)) (x, t)) :=
    (DPhi_contDiffOn η hη).continuousOn.comp_continuous
      (Continuous.prodMk continuous_id continuous_const) (fun x => ht)
  have hcs : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ (Phi (Th η)) (x, t)) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) t) (fun x hx => by
      have : t < ‖x‖ := by simpa using hx
      exact fderiv_Phi_zero _ (Th_supp η hsupp) (x, t) ht this)
  simp only [Psu]
  rw [← ContinuousLinearMap.integral_apply (hcont.integrable_of_hasCompactSupport hcs) u,
    integral_fderiv_Phi (Th η) (Th_contDiff η hη) (Th_supp η hsupp) t ht]
  simp

/-- Directional second derivative `g_u p = D²v(p) u` as a kernel integral. -/
lemma gu_rep {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0) (u : EuclideanSpace ℝ (Fin n) × ℝ)
    (p : EuclideanSpace ℝ (Fin n) × ℝ) (hp : 0 < p.2) :
    fderiv ℝ (fderiv ℝ (vavg q η)) p u =
      ∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rq,
        Mb n (fderiv ℝ q w) (Psu η u (p - (w, 0))) := by
  have hc : Continuous (fun w : EuclideanSpace ℝ (Fin n) =>
      (Mb n (fderiv ℝ q w)).comp (fderiv ℝ (Phi (Th η)) (p - (w, 0)))) :=
    ((Mb n).continuous.comp (hq.continuous_fderiv one_ne_zero)).clm_comp
      ((DPhi_contDiffOn η hη).continuousOn.comp_continuous (by fun_prop)
        (fun w => by show 0 < (p - (w, 0)).2; simpa using hp))
  rw [(hasFDerivAt_fderiv_vavg q η hq hη hsupp Rq hqs p hp).fderiv,
    setIntegral_clm_apply _ hc _ (isCompact_closedBall 0 Rq) u]
  simp only [ContinuousLinearMap.comp_apply, Psu]

lemma hasFDerivAt_gu {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0) (u : EuclideanSpace ℝ (Fin n) × ℝ)
    (p₀ : EuclideanSpace ℝ (Fin n) × ℝ) (hp₀ : 0 < p₀.2) :
    HasFDerivAt (fun p => fderiv ℝ (fderiv ℝ (vavg q η)) p u)
      (∫ w in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) Rq,
        (Mb n (fderiv ℝ q w)).comp (fderiv ℝ (Psu η u) (p₀ - (w, 0)))) p₀ := by
  have hd := hasFDerivAt_shift_integral (Mb n) (fderiv ℝ q) (hq.continuous_fderiv one_ne_zero)
    (Psu η u) (Psu_contDiffOn η hη u) (Metric.closedBall 0 Rq) (isCompact_closedBall _ _) p₀ hp₀
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem (isOpen_upper.mem_nhds hp₀) (fun p hp =>
    gu_rep q η hq hη hsupp Rq hqs u p hp)

/-- `|D g_u| ≤ K |u| t^μ t^n t^{-(n+2)}` in the upper half-space. -/
lemma gu_deriv_bound {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0) (μ M : ℝ) (hμ : 0 < μ) (hM : 0 ≤ M)
    (hqH : ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u p : EuclideanSpace ℝ (Fin n) × ℝ), 0 < p.2 →
      ‖fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ (vavg q η)) p u) p‖ ≤
        K * ‖u‖ * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 2))⁻¹ := by
  obtain ⟨C2, hC20, hC2⟩ := (Phi_deriv_bounds (Th η) (Th_contDiff η hη) (Th_supp η hsupp)).2
  obtain ⟨K, hK0, hK⟩ := shift_integral_bound' (Mb n) (fderiv ℝ q)
    (hq.continuous_fderiv one_ne_zero) μ M hμ hM hqH Rq hqs
  refine ⟨K * C2, mul_nonneg hK0 hC20, fun u p hp => ?_⟩
  rw [(hasFDerivAt_gu q η hq hη hsupp Rq hqs u p hp).fderiv]
  have := hK (Psu η u) (Psu_contDiffOn η hη u) (Psu_zero η hsupp u) 0
    (fun t ht => integral_Psu η hη hsupp u t ht) (C2 * ‖u‖) (n + 2) (by positivity)
    (fun p hp => (norm_fderiv_Psu η hη u p hp).trans (by
      calc ‖fderiv ℝ (fderiv ℝ (Phi (Th η))) p‖ * ‖u‖ ≤ C2 * (p.2 ^ (n + 2))⁻¹ * ‖u‖ :=
            mul_le_mul_of_nonneg_right (hC2 p hp) (norm_nonneg _)
        _ = C2 * ‖u‖ * (p.2 ^ (n + 2))⁻¹ := by ring)) p hp
  calc _ ≤ _ := this
    _ = K * C2 * ‖u‖ * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 2))⁻¹ := by ring

end Pd67abb68C2v


namespace Pd67abb68C2w

open MeasureTheory Pd67abb68C2a Pd67abb68C2k Pd67abb68C2v

/-- Bounded and globally `μ`-Hoelder. -/
def HB {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] (μ : ℝ) (f : X → F) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ (∀ p, ‖f p‖ ≤ B) ∧ ∀ p p', ‖f p - f p'‖ ≤ K * ‖p - p'‖ ^ μ

lemma HB.of_lip {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] {μ : ℝ}
    (hμ : 0 < μ) (hμ1 : μ ≤ 1) (f : X → F) (B L : ℝ) (hB : ∀ p, ‖f p‖ ≤ B)
    (hL : ∀ p p', ‖f p - f p'‖ ≤ L * ‖p - p'‖) : HB μ f := by
  refine ⟨max B 0, max L 0 + 2 * max B 0, le_max_right _ _, by positivity,
    fun p => (hB p).trans (le_max_left _ _), fun p p' => ?_⟩
  have hB0 := le_max_right B 0
  have hL0 := le_max_right L 0
  have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
  rcases le_or_gt ‖p - p'‖ 1 with h | h
  · have h1 : ‖p - p'‖ ≤ ‖p - p'‖ ^ μ := Real.self_le_rpow_of_le_one (norm_nonneg _) h hμ1
    calc ‖f p - f p'‖ ≤ L * ‖p - p'‖ := hL p p'
      _ ≤ max L 0 * ‖p - p'‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max L 0 * ‖p - p'‖ ^ μ := mul_le_mul_of_nonneg_left h1 hL0
      _ ≤ _ := by nlinarith
  · have h1 : 1 ≤ ‖p - p'‖ ^ μ := Real.one_le_rpow h.le hμ.le
    calc ‖f p - f p'‖ ≤ ‖f p‖ + ‖f p'‖ := norm_sub_le _ _
      _ ≤ 2 * max B 0 := by linarith [hB p, hB p', le_max_left B 0]
      _ ≤ _ := by nlinarith

lemma HB.const {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] {μ : ℝ} (c : F) :
    HB μ (fun _ : X => c) :=
  ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ => le_rfl, fun p p' => by simp⟩

lemma HB.add {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] {μ : ℝ}
    {f g : X → F} (hf : HB μ f) (hg : HB μ g) : HB μ (fun p => f p + g p) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hf
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := hg
  refine ⟨B1 + B2, K1 + K2, by positivity, by positivity, fun p => ?_, fun p p' => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (hf1 p) (hg1 p))
  · calc ‖f p + g p - (f p' + g p')‖ = ‖(f p - f p') + (g p - g p')‖ := by congr 1; abel
      _ ≤ ‖f p - f p'‖ + ‖g p - g p'‖ := norm_add_le _ _
      _ ≤ K1 * ‖p - p'‖ ^ μ + K2 * ‖p - p'‖ ^ μ := add_le_add (hf2 p p') (hg2 p p')
      _ = _ := by ring

lemma HB.smul {X F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : ℝ} {c : X → ℝ} {g : X → F} (hc : HB μ c) (hg : HB μ g) :
    HB μ (fun p => c p • g p) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hc
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := hg
  refine ⟨B1 * B2, K1 * B2 + B1 * K2, by positivity, by positivity, fun p => ?_, fun p p' => ?_⟩
  · rw [norm_smul]; exact mul_le_mul (hf1 p) (hg1 p) (norm_nonneg _) hB1
  · have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
    calc ‖c p • g p - c p' • g p'‖ = ‖(c p - c p') • g p + c p' • (g p - g p')‖ := by
          congr 1; rw [sub_smul, smul_sub]; abel
      _ ≤ ‖c p - c p'‖ * ‖g p‖ + ‖c p'‖ * ‖g p - g p'‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
      _ ≤ (K1 * ‖p - p'‖ ^ μ) * B2 + B1 * (K2 * ‖p - p'‖ ^ μ) :=
          add_le_add (mul_le_mul (hf2 p p') (hg1 p) (norm_nonneg _) (by positivity))
            (mul_le_mul (hf1 p') (hg2 p p') (norm_nonneg _) hB1)
      _ = _ := by ring

lemma HB.smulRight {X Y F : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : ℝ} {c : X → (Y →L[ℝ] ℝ)} {g : X → F} (hc : HB μ c) (hg : HB μ g) :
    HB μ (fun p => (c p).smulRight (g p)) := by
  obtain ⟨B1, K1, hB1, hK1, hf1, hf2⟩ := hc
  obtain ⟨B2, K2, hB2, hK2, hg1, hg2⟩ := hg
  refine ⟨B1 * B2, K1 * B2 + B1 * K2, by positivity, by positivity, fun p => ?_, fun p p' => ?_⟩
  · rw [ContinuousLinearMap.norm_smulRight_apply]; exact mul_le_mul (hf1 p) (hg1 p) (norm_nonneg _) hB1
  · have hr : 0 ≤ ‖p - p'‖ ^ μ := Real.rpow_nonneg (norm_nonneg _) μ
    have he : (c p).smulRight (g p) - (c p').smulRight (g p') =
        (c p - c p').smulRight (g p) + (c p').smulRight (g p - g p') := by
      ext x; simp [sub_smul, smul_sub]
    calc ‖(c p).smulRight (g p) - (c p').smulRight (g p')‖
        = ‖(c p - c p').smulRight (g p) + (c p').smulRight (g p - g p')‖ := by rw [he]
      _ ≤ ‖c p - c p'‖ * ‖g p‖ + ‖c p'‖ * ‖g p - g p'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ (K1 * ‖p - p'‖ ^ μ) * B2 + B1 * (K2 * ‖p - p'‖ ^ μ) :=
          add_le_add (mul_le_mul (hf2 p p') (hg1 p) (norm_nonneg _) (by positivity))
            (mul_le_mul (hf1 p') (hg2 p p') (norm_nonneg _) hB1)
      _ = _ := by ring

/-- A smooth compactly supported function of the last coordinate is bounded Hoelder. -/
lemma HB.snd_of_contDiff {E : Type*} [NormedAddCommGroup E] {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a) (has : HasCompactSupport a) :
    HB μ (fun p : E × ℝ => a p.2) := by
  obtain ⟨B, hB⟩ := has.exists_bound_of_continuous ha.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport has ha one_ne_zero
  refine HB.of_lip hμ hμ1 _ B L (fun p => hB p.2) (fun p p' => ?_)
  have h1 := hL.dist_le_mul p.2 p'.2
  rw [dist_eq_norm, dist_eq_norm] at h1
  calc ‖a p.2 - a p'.2‖ ≤ L * ‖p.2 - p'.2‖ := h1
    _ ≤ L * ‖p - p'‖ := mul_le_mul_of_nonneg_left (by
        rw [← Prod.snd_sub]; exact norm_snd_le _) L.2

/-! ### the cutoff `ψ t = t χ(t)` -/

lemma exists_psi (ε : ℝ) (hε : 0 < ε) : ∃ ψ : ℝ → ℝ, ContDiff ℝ 3 ψ ∧ HasCompactSupport ψ ∧
    ψ 0 = 0 ∧ deriv ψ 0 = 1 ∧ (∀ t, |ψ t| ≤ |t|) ∧ (∀ t, |ψ t| ≤ ε) ∧
    (∀ t, ε ≤ |t| → ψ t = 0) := by
  let χ : ContDiffBump (0 : ℝ) := ⟨ε / 2, ε, by positivity, by linarith⟩
  refine ⟨fun t => t * χ t, contDiff_id.mul (χ.contDiff (n := 3)), ?_, by simp, ?_, fun t => ?_, fun t => ?_,
    fun t ht => ?_⟩
  · exact (χ.hasCompactSupport).mul_left
  · have h1 : HasDerivAt (fun t => t * χ t) (1 * χ 0 + 0 * deriv χ 0) 0 :=
      (hasDerivAt_id 0).mul ((χ.contDiff (n := 1)).differentiable one_ne_zero 0).hasDerivAt
    rw [h1.deriv, χ.one_of_mem_closedBall (by simp; positivity)]; ring
  · rw [abs_mul]
    have h0 := χ.nonneg (x := t)
    have h1 := χ.le_one (x := t)
    rw [abs_of_nonneg h0]; nlinarith [abs_nonneg t]
  · rw [abs_mul]
    have h0 := χ.nonneg (x := t)
    have h1 := χ.le_one (x := t)
    rw [abs_of_nonneg h0]
    by_cases ht : |t| < ε
    · nlinarith [abs_nonneg t]
    · have : χ t = 0 := by
        by_contra hne
        have : t ∈ Function.support χ := hne
        rw [χ.support_eq] at this
        simp at this
        exact ht this
      rw [this]; simp; linarith
  · have : χ t = 0 := by
      by_contra hne
      have : t ∈ Function.support χ := hne
      rw [χ.support_eq] at this
      simp at this
      linarith
    simp [this]

end Pd67abb68C2w


namespace Pd67abb68C2w

open MeasureTheory Pd67abb68C2a Pd67abb68C2k Pd67abb68C2v

lemma exists_radius {X F : Type*} [NormedAddCommGroup X] [Zero F] [TopologicalSpace F]
    {f : X → F} (hf : HasCompactSupport f) : ∃ R : ℝ, ∀ w, R < ‖w‖ → f w = 0 := by
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun w hw => image_eq_zero_of_notMem_tsupport (fun h => ?_)⟩
  have := hR h
  simp at this
  linarith

lemma vavg_eq_zero {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ)
    (hqR : ∀ w, R < ‖w‖ → q w = 0) (p : EuclideanSpace ℝ (Fin n) × ℝ)
    (hp : R + |p.2| < ‖p.1‖) : vavg q η p = 0 := by
  unfold vavg
  rw [setIntegral_congr_fun measurableSet_closedBall (g := fun _ => (0 : ℝ)) ?_]
  · simp
  intro y hy
  have hy1 : ‖y‖ ≤ 1 := by simpa using hy
  have h1 : ‖p.2 • y‖ ≤ |p.2| := by
    rw [norm_smul, Real.norm_eq_abs]; nlinarith [abs_nonneg p.2, norm_nonneg y]
  have h2 := norm_sub_norm_le p.1 (p.2 • y)
  show q (p.1 - p.2 • y) * η y = 0
  rw [hqR _ (by linarith), zero_mul]

lemma vavg_bdd {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (hη : Continuous η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖vavg q η p‖ ≤ B := by
  obtain ⟨Bq, hBq⟩ := hqs.exists_bound_of_continuous hq
  obtain ⟨Cη, hCη⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_bound_of_continuousOn
    hη.continuousOn
  refine ⟨max (Bq * Cη) 0 * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
    by positivity, fun p => ?_⟩
  unfold vavg
  refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top (fun y hy => ?_)
  rw [norm_mul]
  exact (mul_le_mul (hBq _) (hCη y hy) (norm_nonneg _) ((norm_nonneg _).trans (hBq 0))).trans
    (le_max_left _ _)

lemma vavg_fderiv_bdd {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hqs : HasCompactSupport q) (hη : Continuous η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖fderiv ℝ (vavg q η) p‖ ≤ B := by
  obtain ⟨Bq, hBq⟩ := (hqs.fderiv ℝ).exists_bound_of_continuous (hq.continuous_fderiv one_ne_zero)
  obtain ⟨Cη, hCη⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_bound_of_continuousOn
    hη.continuousOn
  refine ⟨max (Cη * (Bq * 2)) 0 * volume.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
    by positivity, fun p => ?_⟩
  rw [(vavg_hasFDerivAt q η hq hη p).fderiv]
  refine norm_setIntegral_le_of_norm_le_const measure_closedBall_lt_top (fun y hy => ?_)
  have hy1 : ‖y‖ ≤ 1 := by simpa using hy
  rw [norm_smul]
  have h1 := ContinuousLinearMap.opNorm_comp_le (fderiv ℝ q (p.1 - p.2 • y)) (Lmap y)
  have h2 := Lmap_norm_le y
  have hBq0 : 0 ≤ Bq := (norm_nonneg _).trans (hBq 0)
  refine le_trans ?_ (le_max_left _ _)
  exact mul_le_mul (hCη y hy) (h1.trans (mul_le_mul (hBq _) (by linarith) (norm_nonneg _) hBq0))
    (norm_nonneg _) ((norm_nonneg _).trans (hCη y hy))

lemma vavg_HB {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hqs : HasCompactSupport q) (hη : Continuous η) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1) :
    HB μ (vavg q η) := by
  obtain ⟨B, -, hB⟩ := vavg_bdd q η hq.continuous hqs hη
  obtain ⟨B', -, hB'⟩ := vavg_fderiv_bdd q η hq hqs hη
  refine HB.of_lip hμ hμ1 _ B B' hB (fun p p' => ?_)
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (vavg_hasFDerivAt q η hq hη x).differentiableAt) (fun x _ => hB' x)
    (Set.mem_univ p') (Set.mem_univ p)

lemma vavg_fderiv_HB {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hqs : HasCompactSupport q) (hη : Continuous η) {μ M : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hM : 0 ≤ M) (hqH : ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) :
    HB μ (fderiv ℝ (vavg q η)) := by
  obtain ⟨B, hB0, hB⟩ := vavg_fderiv_bdd q η hq hqs hη
  obtain ⟨K, hK⟩ := vavg_fderiv_holder q η hq hη μ M hμ hμ1 hM hqH
  exact ⟨B, max K 0, hB0, le_max_right _ _, hB, fun p p' => (hK p p').trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) _))⟩

lemma vavg_contDiffOn_two {n : ℕ} (q η : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 2 η) (hsupp : ∀ y, 1 < ‖y‖ → η y = 0) (Rq : ℝ)
    (hqs : ∀ w, Rq < ‖w‖ → fderiv ℝ q w = 0) :
    ContDiffOn ℝ 2 (vavg q η) {p | 0 < p.2} := by
  have hU : IsOpen {p : EuclideanSpace ℝ (Fin n) × ℝ | 0 < p.2} := isOpen_upper
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun p _ => (vavg_hasFDerivAt q η hq hη.continuous p).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun p hp => (hasFDerivAt_fderiv_vavg q η hq hη hsupp Rq hqs p
    hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
  rw [contDiffOn_zero, continuousOn_clm_apply]
  intro u p hp
  exact (hasFDerivAt_gu q η hq hη hsupp Rq hqs u p hp).continuousAt.continuousWithinAt

lemma pow_inv_succ (t : ℝ) (ht : 0 < t) (n : ℕ) : t ^ n * (t ^ (n + 1))⁻¹ = t⁻¹ := by
  rw [pow_succ]; field_simp

lemma pow_inv_succ_succ (t : ℝ) (ht : 0 < t) (n : ℕ) : t ^ n * (t ^ (n + 2))⁻¹ = t⁻¹ * t⁻¹ := by
  rw [pow_add]; field_simp

end Pd67abb68C2w


namespace Pd67abb68C2w

open MeasureTheory Pd67abb68C2a Pd67abb68C2k Pd67abb68C2v

lemma norm_add_sub_add_le {F : Type*} [NormedAddCommGroup F] (a b c d : F) :
    ‖a + b - (c + d)‖ ≤ ‖a - c‖ + ‖b - d‖ := by
  rw [add_sub_add_comm]; exact norm_add_le _ _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- One-sided flat oblique lift: `W = ψ(t) v(z,t)`, `v` the variable-radius average of `q`. -/
theorem oblique_flat_lift1 (n : ℕ) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q) (hqs : HasCompactSupport q)
    (hqH : ∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
      ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
      ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
      (∀ z, W (z, 0) = 0) ∧
      (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
      (∀ p, |W p| ≤ δ) ∧
      ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  obtain ⟨hμ0, hμ1⟩ := hμ
  obtain ⟨M0, hM0⟩ := hqH
  set M := max M0 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hqH' : ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ := fun x y =>
    (hM0 x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  set η : EuclideanSpace ℝ (Fin n) → ℝ := b.normed volume with hηdef
  have hη2 : ContDiff ℝ 2 η := b.contDiff_normed
  have hηc : Continuous η := hη2.continuous
  have hηsupp' : Function.support η ⊆ Metric.closedBall 0 1 := by
    rw [hηdef, b.support_normed_eq]; exact Metric.ball_subset_closedBall
  have hηsupp : ∀ y, 1 < ‖y‖ → η y = 0 := fun y hy => by
    by_contra h
    have := hηsupp' h
    simp at this; linarith
  have hη1 : ∫ y, η y = 1 := b.integral_normed
  obtain ⟨R, hR⟩ := exists_radius hqs
  obtain ⟨Rq, hRq⟩ := exists_radius (hqs.fderiv ℝ)
  set v := vavg q η with hvdef
  obtain ⟨Bv, hBv0, hBv⟩ := vavg_bdd q η hq.continuous hqs hηc
  set ε := δ / (Bv + 1) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨ψ, hψ3, hψcs, hψ0, hψ'0, hψt, hψε, hψz⟩ := exists_psi ε hε
  have hψ'2 : ContDiff ℝ 2 (deriv ψ) :=
    (contDiff_succ_iff_deriv.1 (hψ3.of_le (by norm_num) : ContDiff ℝ (2 + 1) ψ)).2.2
  have hψ''1 : ContDiff ℝ 1 (deriv (deriv ψ)) :=
    (contDiff_succ_iff_deriv.1 (hψ'2.of_le (by norm_num) : ContDiff ℝ (1 + 1) (deriv ψ))).2.2
  have hψd : ∀ t, HasDerivAt ψ (deriv ψ t) t := fun t =>
    ((hψ3.differentiable (by norm_num)) t).hasDerivAt
  have hψ'd : ∀ t, HasDerivAt (deriv ψ) (deriv (deriv ψ) t) t := fun t =>
    ((hψ'2.differentiable (by norm_num)) t).hasDerivAt
  set sn := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ with hsn
  have hψs : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
      HasFDerivAt (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ψ p.2) (deriv ψ p.2 • sn) p :=
    fun p => (hψd p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hψ's : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ,
      HasFDerivAt (fun p : EuclideanSpace ℝ (Fin n) × ℝ => deriv ψ p.2)
        (deriv (deriv ψ) p.2 • sn) p :=
    fun p => (hψ'd p.2).comp_hasFDerivAt p hasFDerivAt_snd
  have hv : ∀ p, HasFDerivAt v (fderiv ℝ v p) p := fun p =>
    (vavg_hasFDerivAt q η hq hηc p).differentiableAt.hasFDerivAt
  have hv2 : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) p) p := fun p hp =>
    (hasFDerivAt_fderiv_vavg q η hq hη2 hηsupp Rq hRq p hp).differentiableAt.hasFDerivAt
  set W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun p => ψ p.2 * v p with hWdef
  set c : EuclideanSpace ℝ (Fin n) × ℝ → ℝ := fun p => v p * deriv ψ p.2 with hcdef
  have hDW : ∀ p, HasFDerivAt W (ψ p.2 • fderiv ℝ v p + c p • sn) p := by
    intro p
    have h := (hψs p).mul (hv p)
    rw [smul_smul] at h
    exact h
  have hDWf : fderiv ℝ W = fun p => ψ p.2 • fderiv ℝ v p + c p • sn :=
    funext fun p => (hDW p).fderiv
  have hc : ∀ p, HasFDerivAt c (v p • (deriv (deriv ψ) p.2 • sn) + deriv ψ p.2 • fderiv ℝ v p) p :=
    fun p => (hv p).mul (hψ's p)
  have hD2 : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
      fderiv ℝ (fderiv ℝ W) p = ψ p.2 • fderiv ℝ (fderiv ℝ v) p +
        ((deriv ψ p.2 • sn).smulRight (fderiv ℝ v p) +
          (v p • (deriv (deriv ψ) p.2 • sn) + deriv ψ p.2 • fderiv ℝ v p).smulRight sn) := by
    intro p hp
    have h : HasFDerivAt (fun p => ψ p.2 • fderiv ℝ v p + c p • sn)
        (ψ p.2 • fderiv ℝ (fderiv ℝ v) p + (deriv ψ p.2 • sn).smulRight (fderiv ℝ v p) +
          (v p • (deriv (deriv ψ) p.2 • sn) +
            deriv ψ p.2 • fderiv ℝ v p).smulRight sn) p :=
      ((hψs p).smul (hv2 p hp)).add ((hc p).smul_const sn)
    rw [hDWf, h.fderiv, add_assoc]
  -- the lower-order part `E` is bounded Hoelder
  have hψ'HB : HB μ (fun p : EuclideanSpace ℝ (Fin n) × ℝ => deriv ψ p.2) :=
    HB.snd_of_contDiff hμ0 hμ1 _ (hψ'2.of_le (by norm_num)) hψcs.deriv
  have hψ''HB : HB μ (fun p : EuclideanSpace ℝ (Fin n) × ℝ => deriv (deriv ψ) p.2) :=
    HB.snd_of_contDiff hμ0 hμ1 _ hψ''1 hψcs.deriv.deriv
  have hvHB : HB μ v := vavg_HB q η hq hqs hηc hμ0 hμ1
  have hDvHB : HB μ (fderiv ℝ v) := vavg_fderiv_HB q η hq hqs hηc hμ0 hμ1 hM hqH'
  have hE : HB μ (fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (deriv ψ p.2 • sn).smulRight (fderiv ℝ v p) +
        (v p • (deriv (deriv ψ) p.2 • sn) + deriv ψ p.2 • fderiv ℝ v p).smulRight sn) :=
    HB.add (HB.smulRight (HB.smul hψ'HB (HB.const sn)) hDvHB)
      (HB.smulRight (HB.add (HB.smul hvHB (HB.smul hψ''HB (HB.const sn)))
        (HB.smul hψ'HB hDvHB)) (HB.const sn))
  obtain ⟨-, KE, -, hKE0, -, hKE⟩ := hE
  -- the main part `ψ D²v` is Hoelder on the upper half-space
  obtain ⟨K1, hK10, hK1⟩ := fderiv2_vavg_bound q η hq hη2 hηsupp Rq hRq μ M hμ0 hM hqH'
  obtain ⟨K2, hK20, hK2⟩ := gu_deriv_bound q η hq hη2 hηsupp Rq hRq μ M hμ0 hM hqH'
  obtain ⟨B1, hB1⟩ := hψcs.deriv.exists_bound_of_continuous hψ'2.continuous
  set B1' := max B1 0 with hB1'
  have hB1'0 : 0 ≤ B1' := le_max_right _ _
  set A := K1 + K2 + B1' * K1 with hA
  have hA0 : 0 ≤ A := by positivity
  have hGu : ∀ u : EuclideanSpace ℝ (Fin n) × ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ,
      0 < p.2 → 0 < p'.2 →
      ‖ψ p.2 • fderiv ℝ (fderiv ℝ v) p u - ψ p'.2 • fderiv ℝ (fderiv ℝ v) p' u‖ ≤
        5 * (A * ‖u‖) * ‖p - p'‖ ^ μ := by
    intro u
    have hgu : ∀ p : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 →
        HasFDerivAt (fun p => fderiv ℝ (fderiv ℝ v) p u)
          (fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ v) p u) p) p := fun p hp =>
      (hasFDerivAt_gu q η hq hη2 hηsupp Rq hRq u p hp).differentiableAt.hasFDerivAt
    refine holder_of_deriv_bound (fun p => ψ p.2 • fderiv ℝ (fderiv ℝ v) p u) μ (A * ‖u‖)
      hμ0 hμ1 (by positivity) (fun p hp => ((hψs p).smul (hgu p hp)).differentiableAt)
      (fun p hp => ?_) (fun p hp => ?_)
    · show ‖ψ p.2 • fderiv ℝ (fderiv ℝ v) p u‖ ≤ A * ‖u‖ * p.2 ^ μ
      rw [norm_smul, Real.norm_eq_abs]
      have h1 : ‖fderiv ℝ (fderiv ℝ v) p u‖ ≤ ‖fderiv ℝ (fderiv ℝ v) p‖ * ‖u‖ :=
        (fderiv ℝ (fderiv ℝ v) p).le_opNorm u
      have h2 := hK1 p hp
      have h3 := hψt p.2
      rw [abs_of_pos hp] at h3
      have e : p.2 * (K1 * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 1))⁻¹) = K1 * p.2 ^ μ := by
        have := pow_inv_succ p.2 hp n
        calc _ = K1 * p.2 ^ μ * (p.2 * (p.2 ^ n * (p.2 ^ (n + 1))⁻¹)) := by ring
          _ = _ := by rw [this, mul_inv_cancel₀ hp.ne', mul_one]
      have hr := Real.rpow_nonneg hp.le μ
      have hKA : K1 ≤ A := by
        rw [hA]; exact (le_add_of_nonneg_right hK20).trans (le_add_of_nonneg_right (mul_nonneg hB1'0 hK10))
      calc |ψ p.2| * ‖fderiv ℝ (fderiv ℝ v) p u‖
          ≤ p.2 * ((K1 * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 1))⁻¹) * ‖u‖) :=
            mul_le_mul h3 (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
              (norm_nonneg _) hp.le
        _ = (p.2 * (K1 * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 1))⁻¹)) * ‖u‖ := by ring
        _ = K1 * p.2 ^ μ * ‖u‖ := by rw [e]
        _ ≤ A * ‖u‖ * p.2 ^ μ := by
            have := mul_le_mul_of_nonneg_right hKA (mul_nonneg hr (norm_nonneg u))
            linarith only [this]
    · have hfd : fderiv ℝ (fun p => ψ p.2 • fderiv ℝ (fderiv ℝ v) p u) p =
          ψ p.2 • fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ v) p u) p +
            (deriv ψ p.2 • sn).smulRight (fderiv ℝ (fderiv ℝ v) p u) :=
        ((hψs p).smul (hgu p hp)).fderiv
      rw [hfd]
      have h1 := hK2 u p hp
      have h2 := hK1 p hp
      have h3 := hψt p.2
      rw [abs_of_pos hp] at h3
      have h4 : ‖deriv ψ p.2 • sn‖ ≤ B1' := by
        rw [norm_smul]
        calc ‖deriv ψ p.2‖ * ‖sn‖ ≤ B1' * 1 :=
              mul_le_mul ((hB1 p.2).trans (le_max_left _ _))
                (ContinuousLinearMap.norm_snd_le ℝ (EuclideanSpace ℝ (Fin n)) ℝ) (norm_nonneg _) hB1'0
          _ = B1' := mul_one _
      have h5 : ‖fderiv ℝ (fderiv ℝ v) p u‖ ≤ ‖fderiv ℝ (fderiv ℝ v) p‖ * ‖u‖ :=
        (fderiv ℝ (fderiv ℝ v) p).le_opNorm u
      have e1 := pow_inv_succ p.2 hp n
      have e2 := pow_inv_succ_succ p.2 hp n
      have e3 : p.2 ^ (μ - 1) = p.2 ^ μ * p.2⁻¹ := by
        rw [Real.rpow_sub_one hp.ne', div_eq_mul_inv]
      rw [e3]
      have hr := Real.rpow_nonneg hp.le μ
      have hti : 0 < p.2⁻¹ := inv_pos.2 hp
      have t1 : ‖ψ p.2 • fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ v) p u) p‖ ≤
          K2 * ‖u‖ * (p.2 ^ μ * p.2⁻¹) := by
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        rw [Real.norm_eq_abs]
        calc |ψ p.2| * ‖fderiv ℝ (fun p => fderiv ℝ (fderiv ℝ v) p u) p‖
            ≤ p.2 * (K2 * ‖u‖ * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 2))⁻¹) :=
              mul_le_mul h3 h1 (ContinuousLinearMap.opNorm_nonneg _) hp.le
          _ = K2 * ‖u‖ * p.2 ^ μ * (p.2 * (p.2 ^ n * (p.2 ^ (n + 2))⁻¹)) := by ring
          _ = K2 * ‖u‖ * p.2 ^ μ * ((p.2 * p.2⁻¹) * p.2⁻¹) := by rw [e2]; ring
          _ = K2 * ‖u‖ * (p.2 ^ μ * p.2⁻¹) := by rw [mul_inv_cancel₀ hp.ne', one_mul]; ring
      have t2 : ‖(deriv ψ p.2 • sn).smulRight (fderiv ℝ (fderiv ℝ v) p u)‖ ≤
          B1' * K1 * ‖u‖ * (p.2 ^ μ * p.2⁻¹) := by
        rw [ContinuousLinearMap.norm_smulRight_apply]
        calc ‖deriv ψ p.2 • sn‖ * ‖fderiv ℝ (fderiv ℝ v) p u‖
            ≤ B1' * (K1 * p.2 ^ μ * p.2 ^ n * (p.2 ^ (n + 1))⁻¹ * ‖u‖) :=
              mul_le_mul h4 (h5.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
                (norm_nonneg _) hB1'0
          _ = B1' * K1 * ‖u‖ * (p.2 ^ μ * (p.2 ^ n * (p.2 ^ (n + 1))⁻¹)) := by ring
          _ = _ := by rw [e1]
      have hx : 0 ≤ ‖u‖ * (p.2 ^ μ * p.2⁻¹) := by positivity
      calc _ ≤ _ := norm_add_le _ _
        _ ≤ K2 * ‖u‖ * (p.2 ^ μ * p.2⁻¹) + B1' * K1 * ‖u‖ * (p.2 ^ μ * p.2⁻¹) := add_le_add t1 t2
        _ ≤ A * ‖u‖ * (p.2 ^ μ * p.2⁻¹) := by
          have := mul_nonneg hK10 hx
          rw [hA]; linarith only [this]
  have hG : ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
      ‖ψ p.2 • fderiv ℝ (fderiv ℝ v) p - ψ p'.2 • fderiv ℝ (fderiv ℝ v) p'‖ ≤
        5 * A * ‖p - p'‖ ^ μ := by
    intro p p' hp hp'
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun u => ?_)
    have := hGu u p p' hp hp'
    calc ‖(ψ p.2 • fderiv ℝ (fderiv ℝ v) p - ψ p'.2 • fderiv ℝ (fderiv ℝ v) p') u‖
        = ‖ψ p.2 • fderiv ℝ (fderiv ℝ v) p u - ψ p'.2 • fderiv ℝ (fderiv ℝ v) p' u‖ := by
          simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
      _ ≤ 5 * (A * ‖u‖) * ‖p - p'‖ ^ μ := this
      _ = 5 * A * ‖p - p'‖ ^ μ * ‖u‖ := by ring
  refine ⟨W, ?_, ?_, ?_, ?_, ?_, ?_, ⟨5 * A + KE, fun p p' hp hp' => ?_⟩⟩
  · exact ((hψ3.of_le (by norm_num)).comp contDiff_snd).mul
      (vavg_contDiff q η hq (hη2.of_le (by norm_num)))
  · refine HasCompactSupport.intro
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n) × ℝ) (|R| + ε + 1)) (fun p hp => ?_)
    have hp' : |R| + ε + 1 < ‖p‖ := by simpa using hp
    show ψ p.2 * v p = 0
    by_cases ht : ε ≤ |p.2|
    · rw [hψz p.2 ht, zero_mul]
    · push_neg at ht
      have h1 : ‖p‖ = max ‖p.1‖ ‖p.2‖ := Prod.norm_def p
      rw [Real.norm_eq_abs] at h1
      have h2 : |R| + ε + 1 < ‖p.1‖ := by
        rcases le_total ‖p.1‖ |p.2| with h | h
        · rw [max_eq_right h] at h1; linarith [abs_nonneg R]
        · rw [max_eq_left h] at h1; linarith
      rw [show v p = 0 from vavg_eq_zero q η R hR p (by linarith [le_abs_self R]), mul_zero]
  · exact ((hψ3.of_le (by norm_num)).comp contDiff_snd).contDiffOn.mul
      (vavg_contDiffOn_two q η hq hη2 hηsupp Rq hRq)
  · intro z
    show ψ (z, (0 : ℝ)).2 * v (z, 0) = 0
    rw [show (z, (0 : ℝ)).2 = 0 from rfl, hψ0, zero_mul]
  · intro z
    rw [(hDW (z, 0)).fderiv]
    have hv0 : v (z, 0) = q z := vavg_zero q η hηsupp' hη1 z
    show ψ (z, (0 : ℝ)).2 • fderiv ℝ v (z, 0) + (v (z, 0) * deriv ψ (z, (0 : ℝ)).2) • sn = q z • sn
    rw [show (z, (0 : ℝ)).2 = 0 from rfl, hψ0, hψ'0, hv0, zero_smul, zero_add, mul_one]
  · intro p
    show |ψ p.2 * v p| ≤ δ
    rw [abs_mul]
    have h1 := hψε p.2
    have h2 : |v p| ≤ Bv := by have := hBv p; rwa [Real.norm_eq_abs] at this
    have h3 : ε * Bv ≤ δ := by
      rw [hεdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (by linarith only [hBv0]) hδ.le
    calc |ψ p.2| * |v p| ≤ ε * Bv := mul_le_mul h1 h2 (abs_nonneg _) hε.le
      _ ≤ δ := h3
  · rw [hD2 p hp, hD2 p' hp']
    calc _ ≤ _ := norm_add_sub_add_le _ _ _ _
      _ ≤ 5 * A * ‖p - p'‖ ^ μ + KE * ‖p - p'‖ ^ μ := add_le_add (hG p p' hp hp') (hKE p p')
      _ = (5 * A + KE) * ‖p - p'‖ ^ μ := by ring

end Pd67abb68C2w

theorem solution (n : ℕ) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (q : EuclideanSpace ℝ (Fin n) → ℝ) (hq : ContDiff ℝ 1 q) (hqs : HasCompactSupport q)
    (hqH : ∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
      ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
      ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
      (∀ z, W (z, 0) = 0) ∧
      (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
      (∀ p, |W p| ≤ δ) ∧
      ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
        ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ := by
  exact Pd67abb68C2w.oblique_flat_lift1 n μ hμ q hq hqs hqH δ hδ
