-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/9eb83f0c-753c-5c7b-b7c0-b514d57cffc1

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace

set_option autoImplicit false

namespace P2GProbe
namespace C4aK

noncomputable section

open IsDedekindDomain
open NumberField
open NumberField.AdelicBox
open NumberField.StandardAddChar
open NumberField.AdelicHaar
open NumberField.AdelicLevel
open NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.AutomorphicForm"
open FLT.SmoothVectors
open MeasureTheory
open scoped Pointwise
open scoped Classical
open scoped nonZeroDivisors

section Abstract

private theorem isSmoothVector_mk_mul_right {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Subgroup G) [hK : K.Normal] {M : Type*} {φ : G → M}
    (hφ : IsSmoothVector K (RightTranslationFn.mk φ)) (g₀ : G) :
    IsSmoothVector K (RightTranslationFn.mk fun h => φ (h * g₀)) := by
  let c : K →* K :=
    { toFun := fun k => ⟨g₀⁻¹ * k * g₀, by
        simpa using hK.conj_mem (k : G) k.2 g₀⁻¹⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hc : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  unfold IsSmoothVector at hφ ⊢
  have hle : (MulAction.stabilizer K (RightTranslationFn.mk φ)).comap c
      ≤ MulAction.stabilizer K (RightTranslationFn.mk fun h => φ (h * g₀)) := by
    intro k hk
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hk
    rw [MulAction.mem_stabilizer_iff]
    rw [Subgroup.smul_def] at hk ⊢
    refine RightTranslationFn.ext fun x => ?_
    have hx := congrArg (fun F => RightTranslationFn.toFun F (x * g₀)) hk
    simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at hx ⊢
    have hck : ((c k : K) : G) = g₀⁻¹ * k * g₀ := rfl
    rw [hck] at hx
    have hrew : x * g₀ * (g₀⁻¹ * (k : G) * g₀) = x * (k : G) * g₀ := by group
    rw [hrew] at hx
    exact hx
  refine Subgroup.isOpen_mono hle ?_
  rw [Subgroup.coe_comap]
  exact hφ.preimage hc

private theorem integrable_cond_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) {B C : Set X} (hC : IsCompact C) (hBC : B ⊆ C)
    (hBm : MeasurableSet B) (hB0 : μ B ≠ 0) (hBtop : μ B ≠ ⊤) {f : X → ℂ} (hf : Continuous f) :
    Integrable f (ProbabilityTheory.cond μ B) := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  haveI : IsFiniteMeasure (μ.restrict B) := isFiniteMeasure_restrict.2 hBtop
  have hInt : Integrable f (μ.restrict B) := by
    refine (integrable_const M).mono' hf.aestronglyMeasurable ?_
    exact (ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun x hx => hM x (hBC hx))
  show Integrable f ((μ B)⁻¹ • μ.restrict B)
  exact hInt.smul_measure (ENNReal.inv_ne_top.2 hB0)

private theorem setIntegral_add_right_of_periodic {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : AddSubgroup X) [Countable H] {B : Set X}
    (hBm : MeasurableSet B) (hB : IsAddFundamentalDomain H B μ) {f : X → ℂ}
    (hf : ∀ h ∈ H, ∀ x, f (x + h) = f x) (y : X) :
    ∫ x in B, f (x + y) ∂μ = ∫ x in B, f x ∂μ := by
  have hper : ∀ (h : H) (x : X), f (h +ᵥ x) = f x := fun h x => by
    rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    exact hf h h.2 x
  have hB' : IsAddFundamentalDomain H (y +ᵥ B) μ := hB.vadd_of_comm y
  have hiff : ∀ x, y + x ∈ y +ᵥ B ↔ x ∈ B := fun x => by
    rw [← vadd_eq_add]
    exact Set.vadd_mem_vadd_set_iff
  have hind : ∀ x, (y +ᵥ B).indicator f (y + x) = B.indicator (fun z => f (z + y)) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem ((hiff x).2 hx), add_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx ((hiff x).1 h))]
  calc ∫ x in B, f (x + y) ∂μ
      = ∫ x, B.indicator (fun z => f (z + y)) x ∂μ := (integral_indicator hBm).symm
    _ = ∫ x, (y +ᵥ B).indicator f (y + x) ∂μ := by
        congr 1
        funext x
        exact (hind x).symm
    _ = ∫ x, (y +ᵥ B).indicator f x ∂μ := integral_add_left_eq_self _ y
    _ = ∫ x in y +ᵥ B, f x ∂μ := integral_indicator (hBm.const_vadd y)
    _ = ∫ x in B, f x ∂μ := hB'.setIntegral_eq hB hper

private theorem integral_cond_add_right_of_periodic {X : Type*} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddLeftInvariant] (H : AddSubgroup X) [Countable H] {B : Set X}
    (hBm : MeasurableSet B) (hB : IsAddFundamentalDomain H B μ) {f : X → ℂ}
    (hf : ∀ h ∈ H, ∀ x, f (x + h) = f x) (y : X) :
    ∫ x, f (x + y) ∂(ProbabilityTheory.cond μ B) = ∫ x, f x ∂(ProbabilityTheory.cond μ B) := by
  show ∫ x, f (x + y) ∂((μ B)⁻¹ • μ.restrict B) = ∫ x, f x ∂((μ B)⁻¹ • μ.restrict B)
  rw [integral_smul_measure, integral_smul_measure,
    setIntegral_add_right_of_periodic μ H hBm hB hf y]

private theorem eq_one_of_integral_mul_ne_zero {X : Type*} [MeasurableSpace X] [AddCommGroup X]
    (ν : Measure X) {s e : X → ℂ} {y : X} {ω : ℂ} (hs : ∀ x, s (x + y) = s x)
    (he : ∀ x, e (x + y) = e x * ω)
    (hT : ∫ x, s (x + y) * e (x + y) ∂ν = ∫ x, s x * e x ∂ν)
    (hW : ∫ x, s x * e x ∂ν ≠ 0) : ω = 1 := by
  have hfun : (fun x => s (x + y) * e (x + y)) = fun x => ω * (s x * e x) := by
    funext x
    rw [hs, he]; ring
  have hcm : ∫ x, ω * (s x * e x) ∂ν = ω * ∫ x, s x * e x ∂ν := integral_const_mul ω _
  rw [hfun, hcm] at hT
  exact (mul_eq_right₀ hW).mp hT

private theorem continuous_of_invariant_of_arch {A B W : Type*} [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] [TopologicalSpace B] [TopologicalSpace W] {Y : Type*}
    [TopologicalSpace Y] (f : A → Y) {V : Set B} (hVo : IsOpen V)
    (Lr : W → A) (Lf : B → A) (pA : A → W) (pB : A → B) (hpA : Continuous pA) (hpB : Continuous pB)
    (hpB0 : pB 0 ∈ V) (hdec : ∀ z : A, z = Lr (pA z) + Lf (pB z))
    (hV : ∀ x : A, ∀ v ∈ V, f (x + Lf v) = f x)
    (hs : ∀ x : A, Continuous fun u : W => f (x + Lr u)) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hF : Continuous fun x : A => f (x₀ + Lr (pA (x - x₀))) :=
    (hs x₀).comp (hpA.comp (continuous_id.sub continuous_const))
  refine hF.continuousAt.congr ?_
  have hmem : ∀ᶠ x : A in nhds x₀, pB (x - x₀) ∈ V := by
    have hc : Continuous fun x : A => pB (x - x₀) := hpB.comp (continuous_id.sub continuous_const)
    have h0 : (fun x : A => pB (x - x₀)) x₀ ∈ V := by simpa using hpB0
    exact hc.continuousAt.preimage_mem_nhds (hVo.mem_nhds h0)
  filter_upwards [hmem] with x hx
  have hxeq : x₀ + Lr (pA (x - x₀)) + Lf (pB (x - x₀)) = x := by
    rw [add_assoc, ← hdec (x - x₀)]; abel
  show f (x₀ + Lr (pA (x - x₀))) = f x
  rw [← hV (x₀ + Lr (pA (x - x₀))) _ hx, hxeq]

private theorem exists_bound_of_continuous_of_forall_exists_mem {X : Type*} [TopologicalSpace X]
    {Y : Type*} [SeminormedAddCommGroup Y] {f : X → Y} (hf : Continuous f) {C : Set X}
    (hC : IsCompact C) (hcov : ∀ x, ∃ c ∈ C, f x = f c) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨c, hc, hxc⟩ := hcov x
  rw [hxc]
  exact hM c hc

private theorem norm_fwdDiff_iter_le {F : ℝ → ℂ} {s : ℕ} (hF : ContDiff ℝ s F) {M : ℝ}
    (hM : ∀ u, ‖iteratedDeriv s F u‖ ≤ M) (h u : ℝ) :
    ‖((fwdDiff h)^[s] F) u‖ ≤ M * |h| ^ s := by
  induction s generalizing F M u with
  | zero => simpa using hM u
  | succ s ih =>
    rw [Function.iterate_succ_apply]
    have hF1 : ContDiff ℝ ((s : WithTop ℕ∞) + 1) F := by exact_mod_cast hF
    have hF' : ContDiff ℝ s F := hF1.of_le le_self_add
    have hsh : ContDiff ℝ s (fun v : ℝ => F (v + h)) := hF'.comp (contDiff_id.add contDiff_const)
    have hG : ContDiff ℝ s (fwdDiff h F) := by
      show ContDiff ℝ s (fun v => F (v + h) - F v)
      exact hsh.sub hF'
    have hGd : ∀ v, iteratedDeriv s (fwdDiff h F) v = iteratedDeriv s F (v + h) - iteratedDeriv s F v := by
      intro v
      have h1 : iteratedDeriv s ((fun w : ℝ => F (w + h)) - F) v
          = iteratedDeriv s (fun w : ℝ => F (w + h)) v - iteratedDeriv s F v :=
        iteratedDeriv_sub hsh.contDiffAt hF'.contDiffAt
      have h2 : iteratedDeriv s (fun w : ℝ => F (w + h)) v = iteratedDeriv s F (v + h) := by
        rw [iteratedDeriv_comp_add_const]
      rw [← h2, ← h1]
      rfl
    have hdiff : Differentiable ℝ (iteratedDeriv s F) := hF1.differentiable_iteratedDeriv' s
    have hMd : ∀ v, ‖iteratedDeriv s (fwdDiff h F) v‖ ≤ M * |h| := by
      intro v
      rw [hGd]
      have key := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hdiff x)
        (fun x _ => by rw [← iteratedDeriv_succ]; exact hM x) (Set.mem_univ v) (Set.mem_univ (v + h))
      simpa [Real.norm_eq_abs] using key
    calc ‖((fwdDiff h)^[s] (fwdDiff h F)) u‖ ≤ M * |h| * |h| ^ s := ih hG hMd u
      _ = M * |h| ^ (s + 1) := by ring

private theorem norm_iteratedDeriv_line_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {s : ℕ} (hf : ContDiff ℝ s f) (h : E) (u : ℝ) :
    ‖iteratedDeriv s (fun t : ℝ => f (t • h)) u‖ ≤ ‖iteratedFDeriv ℝ s f (u • h)‖ * ‖h‖ ^ s := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ h
  have hcomp : (fun t : ℝ => f (t • h)) = f ∘ L := by
    funext t
    simp [L, ContinuousLinearMap.toSpanSingleton_apply]
  rw [iteratedDeriv_eq_iteratedFDeriv, hcomp, L.iteratedFDeriv_comp_right hf u le_rfl,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL : ∀ t : ℝ, L t = t • h := fun t => ContinuousLinearMap.toSpanSingleton_apply ℝ h t
  have hprod : ∏ _i : Fin s, ‖L 1‖ = ‖h‖ ^ s := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hL, one_smul]
  calc ‖iteratedFDeriv ℝ s f (L u) (fun _ => L 1)‖
        ≤ ‖iteratedFDeriv ℝ s f (L u)‖ * ∏ _i : Fin s, ‖L 1‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ s f (u • h)‖ * ‖h‖ ^ s := by rw [hprod, hL]

private theorem integral_fwdDiff_iter_mul_eq {X : Type*} [MeasurableSpace X] [AddCommGroup X]
    (ν : Measure X) (e : X → ℂ) (y : X) {ω : ℂ} (hω : ω ≠ 0) (he : ∀ x, e (x + y) = e x * ω)
    (Per : (X → ℂ) → Prop)
    (hshift : ∀ F : X → ℂ, Per F → Per (fun x => F (x + y)))
    (hsub : ∀ F G : X → ℂ, Per F → Per G → Per (fun x => F x - G x))
    (hint : ∀ F : X → ℂ, Per F → Integrable (fun x => F x * e x) ν)
    (hT : ∀ F : X → ℂ, Per F → ∫ x, F (x + y) * e (x + y) ∂ν = ∫ x, F x * e x ∂ν)
    (s : ℕ) {F : X → ℂ} (hF : Per F) :
    ∫ x, ((fwdDiff y)^[s] F) x * e x ∂ν = (ω⁻¹ - 1) ^ s * ∫ x, F x * e x ∂ν := by
  induction s generalizing F with
  | zero => simp
  | succ s ih =>
    rw [Function.iterate_succ_apply]
    have hG : Per (fwdDiff y F) := hsub _ _ (hshift F hF) hF
    rw [ih hG, pow_succ, mul_assoc]
    congr 1
    have h1 : ∫ x, F (x + y) * e x ∂ν = ω⁻¹ * ∫ x, F x * e x ∂ν := by
      have hfun : (fun x => F (x + y) * e x) = fun x => ω⁻¹ * (F (x + y) * e (x + y)) := by
        funext x
        rw [he]
        field_simp
      have hcm : ∫ x, ω⁻¹ * (F (x + y) * e (x + y)) ∂ν = ω⁻¹ * ∫ x, F (x + y) * e (x + y) ∂ν :=
        integral_const_mul ω⁻¹ _
      rw [hfun, hcm, hT F hF]
    have hsplit : (fun x => (fwdDiff y F) x * e x) = fun x => F (x + y) * e x - F x * e x := by
      funext x
      show (F (x + y) - F x) * e x = _
      ring
    rw [hsplit, integral_sub (hint _ (hshift F hF)) (hint F hF), h1]
    ring

private theorem norm_integral_mul_le_of_fwdDiff_iter {X : Type*} [MeasurableSpace X] [AddCommGroup X]
    (ν : Measure X) [IsProbabilityMeasure ν] (e : X → ℂ) (y : X) {ω : ℂ} (hω : ω ≠ 0)
    (he : ∀ x, e (x + y) = e x * ω) (hen : ∀ x, ‖e x‖ = 1)
    (Per : (X → ℂ) → Prop)
    (hshift : ∀ F : X → ℂ, Per F → Per (fun x => F (x + y)))
    (hsub : ∀ F G : X → ℂ, Per F → Per G → Per (fun x => F x - G x))
    (hint : ∀ F : X → ℂ, Per F → Integrable (fun x => F x * e x) ν)
    (hT : ∀ F : X → ℂ, Per F → ∫ x, F (x + y) * e (x + y) ∂ν = ∫ x, F x * e x ∂ν)
    (s : ℕ) {F : X → ℂ} (hF : Per F) {D : ℝ} (hD : ∀ x, ‖((fwdDiff y)^[s] F) x‖ ≤ D) :
    ‖∫ x, F x * e x ∂ν‖ * ‖ω⁻¹ - 1‖ ^ s ≤ D := by
  have hid := integral_fwdDiff_iter_mul_eq ν e y hω he Per hshift hsub hint hT s hF
  have hnorm : ‖∫ x, ((fwdDiff y)^[s] F) x * e x ∂ν‖ ≤ D := by
    have := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun x => ((fwdDiff y)^[s] F) x * e x) (C := D)
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, hen, mul_one]; exact hD x)
    simpa using this
  rw [hid, norm_mul, norm_pow] at hnorm
  linarith [hnorm]

end Abstract

section Arch

variable (K : Type) [Field K]

private theorem ringEquiv_mixedSpace_symm_apply_of_isReal (x : mixedEmbedding.mixedSpace K)
    {v : InfinitePlace K} (hv : IsReal v) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v = (ringEquivRealOfIsReal hv).symm (x.1 ⟨v, hv⟩) := by
  have h := congrArg (fun z : mixedEmbedding.mixedSpace K => z.1 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  rw [← h]
  exact ((ringEquivRealOfIsReal hv).symm_apply_apply _).symm

private theorem ringEquiv_mixedSpace_symm_apply_of_isComplex (x : mixedEmbedding.mixedSpace K)
    {v : InfinitePlace K} (hv : IsComplex v) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x v
      = (ringEquivComplexOfIsComplex hv).symm (x.2 ⟨v, hv⟩) := by
  have h := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨v, hv⟩)
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply x)
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
  rw [← h]
  exact ((ringEquivComplexOfIsComplex hv).symm_apply_apply _).symm

private theorem continuous_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  show Continuous fun x => InfiniteAdeleRing.ringEquiv_mixedSpace K x
  simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

private theorem ringEquiv_mixedSpace_symm_mixedEmbedding (x : K) :
    (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K x)
      = algebraMap K (InfiniteAdeleRing K) x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, RingEquiv.symm_apply_apply]

private theorem extensionEmbedding_eq_coe {w : InfinitePlace K} (hw : IsReal w) (y : w.Completion) :
    extensionEmbedding w y = ((extensionEmbeddingOfIsReal hw y : ℝ) : ℂ) := by
  induction y using NumberField.InfinitePlace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (isometry_extensionEmbedding w).continuous
      (Complex.continuous_ofReal.comp (isometry_extensionEmbeddingOfIsReal hw).continuous)
  | ih a =>
    rw [extensionEmbedding_coe, extensionEmbeddingOfIsReal_coe, embedding_of_isReal_apply]

variable [NumberField K]

private theorem exists_normAtPlace_eq_norm (x : mixedEmbedding.mixedSpace K) :
    ∃ w : InfinitePlace K, mixedEmbedding.normAtPlace w x = ‖x‖ := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun w => mixedEmbedding.normAtPlace w x)
  exact ⟨w, hw.symm⟩

private theorem infTraceSum_symm (x : mixedEmbedding.mixedSpace K) :
    infTraceSum K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)
      = ∑ w : {w : InfinitePlace K // IsReal w}, x.1 w
        + ∑ w : {w : InfinitePlace K // IsComplex w}, 2 * (x.2 w).re := by
  unfold infTraceSum
  conv_lhs => rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace K => IsReal w)]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [ringEquiv_mixedSpace_symm_apply_of_isReal K x w.2, extensionEmbedding_eq_coe K w.2,
      Complex.ofReal_re, ← ringEquivRealOfIsReal_apply, RingEquiv.apply_symm_apply, mult_isReal,
      Nat.cast_one, one_mul]
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => not_isReal_iff_isComplex) _ _
      fun w => ?_
    have hw : IsComplex w.1 := not_isReal_iff_isComplex.1 w.2
    rw [ringEquiv_mixedSpace_symm_apply_of_isComplex K x hw, ← ringEquivComplexOfIsComplex_apply hw,
      RingEquiv.apply_symm_apply, mult_isComplex ⟨w.1, hw⟩, Nat.cast_ofNat]
    rfl

end Arch

section Glue

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox

local notation "nuBox" K:max => ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)

private abbrev BallInvariance (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ {φ : AdelicGL2 (𝓞 K) K → ℂ}, IsKfSmooth K φ → ∃ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ ∧
    ∀ (g x : AdelicGL2 (𝓞 K) K),
      NumberField.AdelicLevel.glFin (𝓞 K) K x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 K) K →
      ∀ (t : AdeleRing (𝓞 K) K), NumberField.AdelicLevel.adeleArch (𝓞 K) K t = 0 →
        NumberField.AdelicLevel.adeleFin (𝓞 K) K t ∈ NumberField.AdelicLevel.idealBall (𝓞 K) K 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g

private abbrev CharRescaling (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ}, IsGlobalAddChar K ψ → ∃ a : K, a ≠ 0 ∧
    ∀ x : AdeleRing (𝓞 K) K,
      ψ x = NumberField.StandardAddChar.stdAddChar K (algebraMap K (AdeleRing (𝓞 K) K) a * x)

private abbrev CharUnitNorm (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ}, IsGlobalAddChar K ψ → ∀ x : AdeleRing (𝓞 K) K, ‖ψ x‖ = 1

variable {K : Type} [Field K] [NumberField K]

private abbrev Harch (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 K) K,
    ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
      φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))

private def sl (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (x : AdeleRing (𝓞 K) K) : ℂ :=
  φ (unipotentGL2 x * g)

private def ch (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (α : K) (x : AdeleRing (𝓞 K) K) : ℂ :=
  ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))

private def archPt (h : mixedEmbedding.mixedSpace K) : AdeleRing (𝓞 K) K :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm h, 0)

private def archPtHom : mixedEmbedding.mixedSpace K →+ AdeleRing (𝓞 K) K where
  toFun := archPt
  map_zero' := Prod.ext (map_zero _) rfl
  map_add' a b := Prod.ext (map_add _ a b) (zero_add (0 : FiniteAdeleRing (𝓞 K) K)).symm

private theorem archPt_add (a b : mixedEmbedding.mixedSpace K) : archPt (a + b) = archPt a + archPt b :=
  map_add archPtHom a b

private theorem archPt_nsmul (n : ℕ) (a : mixedEmbedding.mixedSpace K) : archPt (n • a) = n • archPt a :=
  map_nsmul archPtHom n a

private def finPt (v : FiniteAdeleRing (𝓞 K) K) : AdeleRing (𝓞 K) K := (0, v)

private theorem alg_mul_archPt (a : K) (h : mixedEmbedding.mixedSpace K) :
    algebraMap K (AdeleRing (𝓞 K) K) a * archPt h = archPt (mixedEmbedding K a * h) := by
  refine Prod.ext ?_ ?_
  · show algebraMap K (InfiniteAdeleRing K) a * (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm h
      = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K a * h)
    rw [map_mul, ringEquiv_mixedSpace_symm_mixedEmbedding]
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) a * 0 = 0
    exact mul_zero _

private theorem algebraMap_eq_archPt_add (w : K) :
    algebraMap K (AdeleRing (𝓞 K) K) w
      = archPt (mixedEmbedding K w) + finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) w) := by
  refine Prod.ext ?_ ?_
  · show algebraMap K (InfiniteAdeleRing K) w
        = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K w) + 0
    rw [add_zero, ringEquiv_mixedSpace_symm_mixedEmbedding]
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) w = 0 + algebraMap K (FiniteAdeleRing (𝓞 K) K) w
    rw [zero_add]

private theorem alg_mul_finPt (a q : K) :
    algebraMap K (AdeleRing (𝓞 K) K) a * finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) q)
      = finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) (a * q)) := by
  refine Prod.ext ?_ ?_
  · show algebraMap K (InfiniteAdeleRing K) a * 0 = 0
    exact mul_zero _
  · show algebraMap K (FiniteAdeleRing (𝓞 K) K) a * algebraMap K (FiniteAdeleRing (𝓞 K) K) q
        = algebraMap K (FiniteAdeleRing (𝓞 K) K) (a * q)
    rw [map_mul]

private def archProj (z : AdeleRing (𝓞 K) K) : mixedEmbedding.mixedSpace K :=
  InfiniteAdeleRing.ringEquiv_mixedSpace K z.1

private theorem continuous_archProj : Continuous (archProj (K := K)) :=
  (continuous_ringEquiv_mixedSpace K).comp continuous_fst

private theorem continuous_snd_adele : Continuous fun z : AdeleRing (𝓞 K) K => z.2 :=
  continuous_snd

private theorem adele_decomp (z : AdeleRing (𝓞 K) K) : z = archPt (archProj z) + finPt z.2 := by
  refine Prod.ext ?_ ?_
  · show z.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace K z.1) + 0
    rw [RingEquiv.symm_apply_apply, add_zero]
  · show z.2 = 0 + z.2
    rw [zero_add]

private theorem algebraMap_mem_idealBall_of_mem {N : Ideal (𝓞 K)} (hN : N ≠ ⊥) {r : 𝓞 K} (hr : r ∈ N) :
    algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K r) ∈ idealBall (𝓞 K) K N := by
  classical
  intro v
  have hmem : r ∈ ⨅ w : HeightOneSpectrum (𝓞 K), w.maxPowDividing N := by
    rw [Ideal.iInf_maxPowDividing_eq hN]
    exact hr
  have hv := Ideal.mem_iInf.1 hmem v
  rw [show algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K r) v
        = algebraMap K (v.adicCompletion K) (algebraMap (𝓞 K) K r) from rfl,
    valued_algebraMap, idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact hv

private theorem exists_ideal_sl (hB : BallInvariance K) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hsm : IsKfSmooth K φ)
    (g : AdelicGL2 (𝓞 K) K) :
    ∃ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ ∧ ∀ (x : AdeleRing (𝓞 K) K), ∀ v ∈ idealBall (𝓞 K) K 𝔫,
      sl φ g (x + finPt v) = sl φ g x := by
  have hsm' : IsKfSmooth K (fun h => φ (h * g)) := by
    haveI : (finiteAdelicGL2Subgroup K).Normal :=
      MonoidHom.normal_ker (NumberField.AdelicLevel.glArch (𝓞 K) K)
    exact isSmoothVector_mk_mul_right (finiteAdelicGL2Subgroup K) hsm g
  obtain ⟨𝔫, h𝔫, hinv⟩ := hB hsm'
  refine ⟨𝔫, h𝔫, fun x v hv => ?_⟩
  have h1 : glFin (𝓞 K) K (1 : AdelicGL2 (𝓞 K) K) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_one]
    exact Subgroup.one_mem _
  have h2 := hinv (unipotentGL2 x) 1 h1 (finPt v) rfl hv
  simp only [inv_one, one_mul, mul_one] at h2
  unfold sl
  rw [unipotentGL2_add]
  exact h2

private theorem sl_add_algebraMap {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (g : AdelicGL2 (𝓞 K) K) (k : K) (x : AdeleRing (𝓞 K) K) :
    sl φ g (x + algebraMap K (AdeleRing (𝓞 K) K) k) = sl φ g x := by
  unfold sl
  rw [add_comm, unipotentGL2_add, mul_assoc, hleft]

private theorem sl_add_archPt_eq (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (x : AdeleRing (𝓞 K) K) :
    (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h))
      = fun h => φ (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm h, 0) * (unipotentGL2 x * g)) := by
  funext h
  unfold sl archPt
  rw [add_comm, unipotentGL2_add, mul_assoc]

private theorem contDiff_slice {φ : AdelicGL2 (𝓞 K) K → ℂ} (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K)
    (x : AdeleRing (𝓞 K) K) :
    ContDiff ℝ ((Module.finrank ℚ K + 1 : ℕ) : WithTop ℕ∞)
      (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h)) := by
  rw [sl_add_archPt_eq]
  exact_mod_cast harch (unipotentGL2 x * g)

private theorem continuous_sl (hB : BallInvariance K) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hsm : IsKfSmooth K φ)
    (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K) : Continuous (sl φ g) := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  exact continuous_of_invariant_of_arch (sl φ g) (isOpen_idealBall (𝓞 K) K h𝔫) archPt finPt
    archProj (fun z => z.2) continuous_archProj continuous_snd_adele
    (zero_mem_idealBall 𝔫) adele_decomp hinv (fun x => (contDiff_slice harch g x).continuous)

private theorem ch_add (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (α : K) (x y : AdeleRing (𝓞 K) K) :
    ch ψ α (x + y) = ch ψ α x * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * y)) := by
  unfold ch
  rw [mul_add, neg_add, AddChar.map_add_eq_mul]

private theorem ch_add_algebraMap {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ) (α : K)
    (k : K) (x : AdeleRing (𝓞 K) K) : ch ψ α (x + algebraMap K (AdeleRing (𝓞 K) K) k) = ch ψ α x := by
  rw [ch_add, ← map_mul, ← map_neg, hψ.principalInvariant, mul_one]

private theorem norm_ch (hN : CharUnitNorm K) {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ)
    (α : K) (x : AdeleRing (𝓞 K) K) : ‖ch ψ α x‖ = 1 :=
  hN hψ _

private theorem continuous_ch {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ) (α : K) :
    Continuous (ch ψ α) := by
  show Continuous fun x : AdeleRing (𝓞 K) K => ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * x))
  exact hψ.continuous.comp ((continuous_const.mul continuous_id).neg)

private scoped instance instCountableOfNumberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 K) K) :=
  (Set.countable_range (algebraMap K (AdeleRing (𝓞 K) K))).to_subtype

private theorem integrable_nuBox_of_continuous {f : AdeleRing (𝓞 K) K → ℂ} (hf : Continuous f) :
    Integrable f (nuBox K) := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset K
  exact integrable_cond_of_continuous (adelicAddHaar (𝓞 K) K) hC hBC (measurableSet_adelicBox K)
    (adelicAddHaar_adelicBox_pos K).ne' (adelicAddHaar_adelicBox_lt_top K).ne hf

private theorem integral_nuBox_add_right {f : AdeleRing (𝓞 K) K → ℂ}
    (hf : ∀ (k : K) (x : AdeleRing (𝓞 K) K), f (x + algebraMap K (AdeleRing (𝓞 K) K) k) = f x)
    (y : AdeleRing (𝓞 K) K) : ∫ x, f (x + y) ∂(nuBox K) = ∫ x, f x ∂(nuBox K) := by
  haveI := countable_principalSubgroup (K := K)
  exact integral_cond_add_right_of_periodic (adelicAddHaar (𝓞 K) K)
    (AdeleRing.principalSubgroup (𝓞 K) K) (measurableSet_adelicBox K)
    (isAddFundamentalDomain_adelicBox K _) (by rintro _ ⟨k, rfl⟩ x; exact hf k x) y

private theorem prod_periodic₀ {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ) (g : AdelicGL2 (𝓞 K) K) (α : K)
    (k : K) (x : AdeleRing (𝓞 K) K) :
    sl φ g (x + algebraMap K (AdeleRing (𝓞 K) K) k) * ch ψ α (x + algebraMap K (AdeleRing (𝓞 K) K) k)
      = sl φ g x * ch ψ α x := by
  rw [sl_add_algebraMap hleft, ch_add_algebraMap hψ]

private theorem psiArch_ratArchLine (t : ℝ) :
    psiArch (ratArchLine t) = Complex.exp (2 * Real.pi * Complex.I * t) := by
  rw [psiArch_apply, finprod_unique, psiArchPlace_apply]
  have h : extensionEmbeddingOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (ratArchLine t default) = t := by
    rw [ratArchLine_apply]
    exact (ringEquivRealOfIsReal _).apply_symm_apply t
  rw [h]

private theorem stdAddChar_archPt (h : mixedEmbedding.mixedSpace K) :
    stdAddChar K (archPt h) = Complex.exp (2 * Real.pi * Complex.I
      * (infTraceSum K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm h) : ℂ)) := by
  show (adelicTraceData K).psiK (archPt h) = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  unfold archPt
  dsimp only
  rw [map_zero, AddChar.map_zero_eq_one, mul_one]
  show psiArch (traceInfHom K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm h)) = _
  rw [traceInfHom_apply, psiArch_ratArchLine]

private theorem trace_mem_of_stdAddChar_archPt_eq_one {a q : K}
    (h : stdAddChar K (archPt (mixedEmbedding K (a * q))) = 1) :
    ∃ m : ℤ, (Algebra.trace ℚ K (a * q) : ℚ) = m := by
  rw [stdAddChar_archPt, ringEquiv_mixedSpace_symm_mixedEmbedding, infTraceSum_algebraMap,
    Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [mul_comm (m : ℂ)] at hm
  have hc : (((Algebra.trace ℚ K (a * q) : ℚ) : ℝ) : ℂ) = (m : ℂ) := mul_left_cancel₀ h2 hm
  exact_mod_cast hc

private def stepR (w : {w : InfinitePlace K // IsReal w}) (r : ℝ) : mixedEmbedding.mixedSpace K :=
  (Pi.single w r, 0)

private def stepC (w : {w : InfinitePlace K // IsComplex w}) (c : ℂ) : mixedEmbedding.mixedSpace K :=
  (0, Pi.single w c)

omit [NumberField K] in
private theorem mul_stepR (x : mixedEmbedding.mixedSpace K) (w : {w : InfinitePlace K // IsReal w})
    (r : ℝ) : x * stepR w r = stepR w (x.1 w * r) := by
  refine Prod.ext ?_ ?_
  · funext v
    show x.1 v * (Pi.single w r : {w : InfinitePlace K // IsReal w} → ℝ) v
      = (Pi.single w (x.1 w * r) : {w : InfinitePlace K // IsReal w} → ℝ) v
    by_cases hv : v = w
    · subst hv
      simp
    · simp [Pi.single_eq_of_ne hv]
  · show x.2 * 0 = 0
    exact mul_zero _

omit [NumberField K] in
private theorem mul_stepC (x : mixedEmbedding.mixedSpace K) (w : {w : InfinitePlace K // IsComplex w})
    (c : ℂ) : x * stepC w c = stepC w (x.2 w * c) := by
  refine Prod.ext ?_ ?_
  · show x.1 * 0 = 0
    exact mul_zero _
  · funext v
    show x.2 v * (Pi.single w c : {w : InfinitePlace K // IsComplex w} → ℂ) v
      = (Pi.single w (x.2 w * c) : {w : InfinitePlace K // IsComplex w} → ℂ) v
    by_cases hv : v = w
    · subst hv
      simp
    · simp [Pi.single_eq_of_ne hv]

private theorem norm_stepR (w : {w : InfinitePlace K // IsReal w}) (r : ℝ) :
    ‖(stepR w r : mixedEmbedding.mixedSpace K)‖ = |r| := by
  unfold stepR
  rw [Prod.norm_def]
  dsimp only
  rw [Pi.norm_single, norm_zero, Real.norm_eq_abs]
  exact max_eq_left (abs_nonneg r)

private theorem norm_stepC (w : {w : InfinitePlace K // IsComplex w}) (c : ℂ) :
    ‖(stepC w c : mixedEmbedding.mixedSpace K)‖ = ‖c‖ := by
  unfold stepC
  rw [Prod.norm_def]
  dsimp only
  rw [Pi.norm_single, norm_zero]
  exact max_eq_right (norm_nonneg c)

private theorem infTraceSum_stepR (w : {w : InfinitePlace K // IsReal w}) (r : ℝ) :
    infTraceSum K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (stepR w r)) = r := by
  rw [infTraceSum_symm]
  unfold stepR
  dsimp only
  rw [Finset.sum_pi_single', if_pos (Finset.mem_univ w)]
  simp

private theorem infTraceSum_stepC (w : {w : InfinitePlace K // IsComplex w}) (c : ℂ) :
    infTraceSum K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (stepC w c)) = 2 * c.re := by
  rw [infTraceSum_symm]
  unfold stepC
  dsimp only
  have h2 : ∑ x : {w : InfinitePlace K // IsComplex w},
      2 * ((Pi.single w c : {w : InfinitePlace K // IsComplex w} → ℂ) x).re = 2 * c.re := by
    have : (fun x : {w : InfinitePlace K // IsComplex w} =>
        2 * ((Pi.single w c : {w : InfinitePlace K // IsComplex w} → ℂ) x).re)
        = fun x => (Pi.single w (2 * c.re) : {w : InfinitePlace K // IsComplex w} → ℝ) x := by
      funext x
      by_cases hx : x = w
      · subst hx
        simp
      · simp [Pi.single_eq_of_ne hx]
    rw [this, Finset.sum_pi_single', if_pos (Finset.mem_univ w)]
  rw [h2]
  simp

private theorem exists_step {a α : K} (ha : a ≠ 0) (hα : α ≠ 0) (w : InfinitePlace K) :
    ∃ h : mixedEmbedding.mixedSpace K,
      infTraceSum K ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (mixedEmbedding K (a * α) * h))
          = 1 / 2 ∧
      ‖h‖ ≤ 1 / (2 * (w a * w α)) := by
  have hw : 0 < w a * w α := mul_pos (pos_iff.2 ha) (pos_iff.2 hα)
  by_cases hr : IsReal w
  · set r : ℝ := (mixedEmbedding K (a * α)).1 ⟨w, hr⟩ with hr_def
    have hrabs : |r| = w a * w α := by
      rw [hr_def, mixedEmbedding.mixedEmbedding_apply_isReal, ← Real.norm_eq_abs, norm_embedding_of_isReal, map_mul]
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hrabs
      exact hw.ne' hrabs.symm
    refine ⟨stepR ⟨w, hr⟩ (1 / (2 * r)), ?_, ?_⟩
    · rw [mul_stepR, infTraceSum_stepR, ← hr_def]
      field_simp
    · rw [norm_stepR, abs_div, abs_mul, abs_two, abs_one, hrabs]
  · have hc : IsComplex w := not_isReal_iff_isComplex.1 hr
    set z : ℂ := (mixedEmbedding K (a * α)).2 ⟨w, hc⟩ with hz_def
    have hzabs : ‖z‖ = w a * w α := by
      rw [hz_def, mixedEmbedding.mixedEmbedding_apply_isComplex, norm_embedding_eq, map_mul]
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hzabs
      exact hw.ne' hzabs.symm
    refine ⟨stepC ⟨w, hc⟩ (1 / (4 * z)), ?_, ?_⟩
    · rw [mul_stepC, infTraceSum_stepC, ← hz_def]
      have : z * (1 / (4 * z)) = ((1 / 4 : ℝ) : ℂ) := by
        rw [mul_one_div, mul_comm (4 : ℂ) z, ← div_div, div_self hz0]
        norm_num
      rw [this, Complex.ofReal_re]
      norm_num
    · rw [norm_stepC, norm_div, norm_mul, norm_one, hzabs]
      have h4 : ‖(4 : ℂ)‖ = 4 := by simp
      rw [h4]
      exact one_div_le_one_div_of_le (mul_pos two_pos hw) (by linarith [hw.le])

private theorem support_sub (hB : BallInvariance K) (hS : CharRescaling K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ) (g : AdelicGL2 (𝓞 K) K) :
    ∃ c : K, c ≠ 0 ∧ ∀ α : K, (∫ x, sl φ g x * ch ψ α x ∂(nuBox K)) ≠ 0 →
      ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c * α := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  obtain ⟨a, ha, hrs⟩ := hS hψ

  have hA : ∀ α : K, (∫ x, sl φ g x * ch ψ α x ∂(nuBox K)) ≠ 0 → ∀ n : 𝓞 K, n ∈ 𝔫 →
      ∃ m : ℤ, (Algebra.trace ℚ K (a * (α * algebraMap (𝓞 K) K n)) : ℚ) = m := by
    intro α hW n hn
    have hqb : algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K n) ∈ idealBall (𝓞 K) K 𝔫 :=
      algebraMap_mem_idealBall_of_mem h𝔫 hn
    have hs : ∀ x, sl φ g (x + finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K n)))
        = sl φ g x :=
      fun x => hinv x _ hqb
    have he : ∀ x, ch ψ α (x + finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K n)))
        = ch ψ α x * ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α
          * finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K n)))) :=
      fun x => ch_add ψ α x _
    have hT := integral_nuBox_add_right (f := fun x => sl φ g x * ch ψ α x) (prod_periodic₀ hleft hψ g α)
      (finPt (algebraMap K (FiniteAdeleRing (𝓞 K) K) (algebraMap (𝓞 K) K n)))
    have hω := eq_one_of_integral_mul_ne_zero (nuBox K) (s := sl φ g) (e := ch ψ α) hs he hT hW
    rw [AddChar.map_neg_eq_inv, inv_eq_one, alg_mul_finPt] at hω
    have hdiag : ψ (algebraMap K (AdeleRing (𝓞 K) K) (α * algebraMap (𝓞 K) K n)) = 1 := by
      rw [hψ.principalInvariant]
    rw [algebraMap_eq_archPt_add, AddChar.map_add_eq_mul, hω, mul_one, hrs, alg_mul_archPt,
      ← map_mul] at hdiag
    exact trace_mem_of_stdAddChar_archPt_eq_one hdiag

  obtain ⟨b, hb, hbint⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)).isFractional
  have hb0 : (b : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hN0 : Ideal.absNorm 𝔫 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact h𝔫
  have hNmem : ((Ideal.absNorm 𝔫 : ℕ) : 𝓞 K) ∈ 𝔫 := Ideal.absNorm_mem 𝔫
  refine ⟨algebraMap (𝓞 K) K b * (a * (Ideal.absNorm 𝔫 : ℕ)), ?_, fun α hW => ?_⟩
  · exact mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hb0)
      (mul_ne_zero ha (Nat.cast_ne_zero.2 hN0))
  ·
    have hmem : a * α * (Ideal.absNorm 𝔫 : ℕ) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0)]
      intro y hy
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      obtain ⟨m, hm⟩ := hA α hW ((Ideal.absNorm 𝔫 : ℕ) * r) (Ideal.mul_mem_right r 𝔫 hNmem)
      have harg : a * α * (Ideal.absNorm 𝔫 : ℕ) * algebraMap (𝓞 K) K r
          = a * (α * algebraMap (𝓞 K) K (((Ideal.absNorm 𝔫 : ℕ) : 𝓞 K) * r)) := by
        rw [map_mul, map_natCast]
        ring
      rw [RingHom.mem_range]
      refine ⟨m, ?_⟩
      rw [Algebra.traceForm_apply, harg, hm]
      simp
    have hint : _ ∈ (algebraMap (𝓞 K) K).rangeS := hbint _ hmem
    obtain ⟨r, hr⟩ := RingHom.mem_rangeS.mp hint
    refine ⟨r, ?_⟩
    rw [hr, Algebra.smul_def]
    ring

private def Sder (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) (x : AdeleRing (𝓞 K) K) :=
  iteratedFDeriv ℝ (Module.finrank ℚ K + 1)
    (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h)) 0

private theorem iteratedFDeriv_slice_eq (φ : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K)
    (x : AdeleRing (𝓞 K) K) (p : mixedEmbedding.mixedSpace K) :
    iteratedFDeriv ℝ (Module.finrank ℚ K + 1)
        (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h)) p
      = Sder φ g (x + archPt p) := by
  unfold Sder
  have hfun : (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt p + archPt h))
      = fun h => sl φ g (x + archPt (h + p)) := by
    funext h
    rw [archPt_add, add_assoc, add_comm (archPt p)]
  have key := iteratedFDeriv_comp_add_right (𝕜 := ℝ)
    (f := fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h)) (Module.finrank ℚ K + 1) p 0
  rw [zero_add] at key
  rw [hfun]
  exact key.symm

private theorem Sder_add_algebraMap {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (g : AdelicGL2 (𝓞 K) K) (k : K) (x : AdeleRing (𝓞 K) K) :
    Sder φ g (x + algebraMap K (AdeleRing (𝓞 K) K) k) = Sder φ g x := by
  unfold Sder
  congr 1
  funext h
  rw [add_right_comm, sl_add_algebraMap hleft]

private theorem Sder_add_fin {φ : AdelicGL2 (𝓞 K) K → ℂ} (g : AdelicGL2 (𝓞 K) K)
    {V : Set (FiniteAdeleRing (𝓞 K) K)} (hV : ∀ (x : AdeleRing (𝓞 K) K), ∀ v ∈ V, sl φ g (x + finPt v) = sl φ g x)
    (x : AdeleRing (𝓞 K) K) {v : FiniteAdeleRing (𝓞 K) K} (hv : v ∈ V) :
    Sder φ g (x + finPt v) = Sder φ g x := by
  unfold Sder
  congr 1
  funext h
  rw [add_right_comm, hV _ v hv]

private theorem continuous_Sder (hB : BallInvariance K) {φ : AdelicGL2 (𝓞 K) K → ℂ} (hsm : IsKfSmooth K φ)
    (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K) : Continuous (Sder φ g) := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  refine continuous_of_invariant_of_arch (Sder φ g) (isOpen_idealBall (𝓞 K) K h𝔫) archPt finPt
    archProj (fun z => z.2) continuous_archProj continuous_snd_adele (zero_mem_idealBall 𝔫) adele_decomp
    (fun x v hv => Sder_add_fin g hinv x hv) (fun x => ?_)
  have hfun : (fun p : mixedEmbedding.mixedSpace K => Sder φ g (x + archPt p))
      = fun p => iteratedFDeriv ℝ (Module.finrank ℚ K + 1)
          (fun h : mixedEmbedding.mixedSpace K => sl φ g (x + archPt h)) p := by
    funext p
    exact (iteratedFDeriv_slice_eq φ g x p).symm
  rw [hfun]
  exact (contDiff_slice harch g x).continuous_iteratedFDeriv'

private theorem exists_bound_Sder (hB : BallInvariance K) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ) (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K) :
    ∃ M : ℝ, ∀ x, ‖Sder φ g x‖ ≤ M := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset K
  refine exists_bound_of_continuous_of_forall_exists_mem (continuous_Sder hB hsm harch g) hC fun x => ?_
  obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox K x
  refine ⟨_, hBC hk, ?_⟩
  rw [show algebraMap K (AdeleRing (𝓞 K) K) k + x = x + algebraMap K (AdeleRing (𝓞 K) K) k from
    add_comm _ _, Sder_add_algebraMap hleft]

private theorem norm_fwdDiff_slice_le {φ : AdelicGL2 (𝓞 K) K → ℂ} (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K)
    {M : ℝ} (hM : ∀ x, ‖Sder φ g x‖ ≤ M) (x : AdeleRing (𝓞 K) K) (h : mixedEmbedding.mixedSpace K) :
    ‖((fwdDiff (archPt h))^[Module.finrank ℚ K + 1] (sl φ g)) x‖
      ≤ M * ‖h‖ ^ (Module.finrank ℚ K + 1) := by
  set s := Module.finrank ℚ K + 1 with hs
  set f : mixedEmbedding.mixedSpace K → ℂ := fun h' => sl φ g (x + archPt h') with hf
  set F : ℝ → ℂ := fun t => f (t • h) with hF
  have hfC : ContDiff ℝ s f := contDiff_slice harch g x
  have hFC : ContDiff ℝ s F := hfC.comp (contDiff_id.smul contDiff_const)
  have hFd : ∀ u, ‖iteratedDeriv s F u‖ ≤ M * ‖h‖ ^ s := by
    intro u
    refine (norm_iteratedDeriv_line_le hfC h u).trans ?_
    have h1 : ‖iteratedFDeriv ℝ s f (u • h)‖ ≤ M := by
      rw [hf, iteratedFDeriv_slice_eq]
      exact hM _
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg h) s)
  have hiter : ((fwdDiff (archPt h))^[s] (sl φ g)) x = ((fwdDiff (1 : ℝ))^[s] F) 0 := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [hF, hf]
    dsimp only
    rw [zero_add, smul_assoc, one_smul, archPt_nsmul]
  rw [hiter]
  simpa using norm_fwdDiff_iter_le hFC hFd 1 0

private theorem decay_bound (hB : BallInvariance K) (hS : CharRescaling K) (hN : CharUnitNorm K)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} {ψ : AddChar (AdeleRing (𝓞 K) K) ℂ} (hψ : IsGlobalAddChar K ψ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ) (harch : Harch φ) (g : AdelicGL2 (𝓞 K) K) :
    ∃ C : ℝ, ∀ α : K, α ≠ 0 →
      ‖∫ x, sl φ g x * ch ψ α x ∂(nuBox K)‖ ≤ C / ‖mixedEmbedding K α‖ ^ (Module.finrank ℚ K + 1) := by
  set s := Module.finrank ℚ K + 1 with hs_def
  obtain ⟨a, ha, hrs⟩ := hS hψ
  obtain ⟨M, hM⟩ := exists_bound_Sder hB hleft hsm harch g
  obtain ⟨w₁, -, hw₁⟩ :=
    Finset.exists_min_image Finset.univ (fun w : InfinitePlace K => w a) Finset.univ_nonempty
  have hma : 0 < w₁ a := pos_iff.2 ha
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨M / 2 ^ s / (2 * w₁ a) ^ s, fun α hα => ?_⟩
  obtain ⟨w, hw⟩ := exists_normAtPlace_eq_norm K (mixedEmbedding K α)
  rw [mixedEmbedding.normAtPlace_apply] at hw
  obtain ⟨h, htr, hnorm⟩ := exists_step ha hα w
  set ω : ℂ := ψ (-(algebraMap K (AdeleRing (𝓞 K) K) α * archPt h)) with hω_def
  have hω : ω = -1 := by
    rw [hω_def, hrs, mul_neg, AddChar.map_neg_eq_inv, alg_mul_archPt, alg_mul_archPt, ← mul_assoc,
      ← map_mul, stdAddChar_archPt, htr]
    have h' : (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [h', Complex.exp_pi_mul_I]
    norm_num
  have hω0 : ω ≠ 0 := by
    rw [hω]
    norm_num
  have he : ∀ x, ch ψ α (x + archPt h) = ch ψ α x * ω := fun x => ch_add ψ α x _
  have hen : ∀ x, ‖ch ψ α x‖ = 1 := norm_ch hN hψ α
  let Per : (AdeleRing (𝓞 K) K → ℂ) → Prop := fun F =>
    (∀ (k : K) (x : AdeleRing (𝓞 K) K), F (x + algebraMap K (AdeleRing (𝓞 K) K) k) = F x) ∧ Continuous F
  have hshift : ∀ F : AdeleRing (𝓞 K) K → ℂ, Per F → Per (fun x => F (x + archPt h)) := fun F hF =>
    ⟨fun k x => by
      dsimp only
      rw [add_right_comm, hF.1], hF.2.comp (continuous_id.add continuous_const)⟩
  have hsub : ∀ F G : AdeleRing (𝓞 K) K → ℂ, Per F → Per G → Per (fun x => F x - G x) :=
    fun F G hF hG =>
    ⟨fun k x => by
      dsimp only
      rw [hF.1, hG.1], hF.2.sub hG.2⟩
  have hint : ∀ F : AdeleRing (𝓞 K) K → ℂ, Per F → Integrable (fun x => F x * ch ψ α x) (nuBox K) :=
    fun F hF => integrable_nuBox_of_continuous (hF.2.mul (continuous_ch hψ α))
  have hT : ∀ F : AdeleRing (𝓞 K) K → ℂ, Per F →
      ∫ x, F (x + archPt h) * ch ψ α (x + archPt h) ∂(nuBox K) = ∫ x, F x * ch ψ α x ∂(nuBox K) :=
    fun F hF => integral_nuBox_add_right (f := fun x => F x * ch ψ α x)
      (fun k x => by
        beta_reduce
        rw [hF.1, ch_add_algebraMap hψ]) (archPt h)
  have hsl : Per (sl φ g) := ⟨fun k x => sl_add_algebraMap hleft g k x, continuous_sl hB hsm harch g⟩
  have hD : ∀ x, ‖((fwdDiff (archPt h))^[s] (sl φ g)) x‖ ≤ M * ‖h‖ ^ s := fun x =>
    norm_fwdDiff_slice_le harch g hM x h
  have key := norm_integral_mul_le_of_fwdDiff_iter (nuBox K) (ch ψ α) (archPt h) hω0 he hen Per hshift
    hsub hint hT s hsl hD
  have h2 : ‖ω⁻¹ - 1‖ = 2 := by
    rw [hω]
    have h' : ((-1 : ℂ))⁻¹ - 1 = -((2 : ℝ) : ℂ) := by
      push_cast
      norm_num
    rw [h', norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_two]
  rw [h2] at key
  have hwa : w₁ a ≤ w a := hw₁ w (Finset.mem_univ w)
  have hwα : 0 < w α := pos_iff.2 hα
  have hpos : (0 : ℝ) < 2 ^ s := pow_pos two_pos s
  have hW : ‖∫ x, sl φ g x * ch ψ α x ∂(nuBox K)‖ ≤ M * ‖h‖ ^ s / 2 ^ s := by
    rw [le_div_iff₀ hpos]
    exact key
  refine hW.trans ?_
  rw [← hw]
  have hh : ‖h‖ ^ s ≤ (1 / (2 * (w a * w α))) ^ s := pow_le_pow_left₀ (norm_nonneg h) hnorm s
  have heq : (1 / (2 * (w a * w α))) ^ s = 1 / ((2 * w a) ^ s * (w α) ^ s) := by
    rw [← mul_assoc, one_div_pow, mul_pow]
  calc M * ‖h‖ ^ s / 2 ^ s ≤ M * (1 / (2 * (w a * w α))) ^ s / 2 ^ s :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh hM0) hpos.le
    _ = M / 2 ^ s / (2 * w a) ^ s / (w α) ^ s := by
        rw [heq]
        ring
    _ ≤ M / 2 ^ s / (2 * w₁ a) ^ s / (w α) ^ s :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_left (div_nonneg hM0 hpos.le) (pow_pos (mul_pos two_pos hma) s)
            (pow_le_pow_left₀ (mul_pos two_pos hma).le (by linarith) s))
          (pow_nonneg hwα.le s)

private def toLat (r : 𝓞 K) : mixedEmbedding.integerLattice K :=
  ⟨mixedEmbedding K (algebraMap (𝓞 K) K r), LinearMap.mem_range_self _ r⟩

private theorem toLat_injective : Function.Injective (toLat (K := K)) := by
  intro r₁ r₂ h12
  have h' : mixedEmbedding K (algebraMap (𝓞 K) K r₁) = mixedEmbedding K (algebraMap (𝓞 K) K r₂) :=
    congrArg Subtype.val h12
  exact IsFractionRing.injective (𝓞 K) K (NumberField.mixedEmbedding_injective K h')

private theorem summable_norm_inv_pow_integerLattice {s : ℕ} (hs : Module.finrank ℚ K < s) :
    Summable (fun z : mixedEmbedding.integerLattice K => ‖z‖⁻¹ ^ s) := by
  refine ZLattice.summable_norm_pow_inv (mixedEmbedding.integerLattice K) s ?_
  rw [ZLattice.rank ℝ (mixedEmbedding.integerLattice K), mixedEmbedding.finrank]
  exact hs

private theorem summable_norm_inv_pow_ringOfIntegers {s : ℕ} (hs : Module.finrank ℚ K < s) :
    Summable (fun r : 𝓞 K => ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s) := by
  have h3 := (summable_norm_inv_pow_integerLattice (K := K) hs).comp_injective toLat_injective
  have h4 : ((fun z : mixedEmbedding.integerLattice K => ‖z‖⁻¹ ^ s) ∘ toLat (K := K))
      = fun r : 𝓞 K => ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s := by
    funext r
    simp only [Function.comp_apply, toLat, Submodule.coe_norm]
  rwa [h4] at h3

private theorem summable_of_support_of_decay {f : K → ℂ} {c : K} (hc : c ≠ 0)
    (hsupp : ∀ α : K, f α ≠ 0 → ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c * α)
    {C : ℝ} {s : ℕ} (hs : Module.finrank ℚ K < s)
    (hbound : ∀ α : K, α ≠ 0 → ‖f α‖ ≤ C / ‖mixedEmbedding K α‖ ^ s) : Summable f := by
  let i : 𝓞 K → K := fun r => c⁻¹ * algebraMap (𝓞 K) K r
  have hi_inj : Function.Injective i := by
    intro r₁ r₂ h12
    have h' : algebraMap (𝓞 K) K r₁ = algebraMap (𝓞 K) K r₂ := mul_left_cancel₀ (inv_ne_zero hc) h12
    exact IsFractionRing.injective (𝓞 K) K h'
  have hvan : ∀ α, α ∉ Set.range i → f α = 0 := by
    intro α hα
    by_contra hne
    obtain ⟨r, hr⟩ := hsupp α hne
    apply hα
    refine ⟨r, ?_⟩
    show c⁻¹ * algebraMap (𝓞 K) K r = α
    rw [hr, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  refine (hi_inj.summable_iff hvan).1 ?_
  have hjs := summable_norm_inv_pow_ringOfIntegers (K := K) hs
  let B : ℝ := max C 0 * ‖mixedEmbedding K c‖ ^ s
  have hc' : 0 < ‖mixedEmbedding K c‖ :=
    norm_pos_iff.mpr ((map_ne_zero_iff _ (NumberField.mixedEmbedding_injective K)).mpr hc)
  have hmain : ∀ r : 𝓞 K, r ≠ 0 →
      ‖f (i r)‖ ≤ B * ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s := by
    intro r hr
    have hr' : algebraMap (𝓞 K) K r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hr
    have hα : i r ≠ 0 := mul_ne_zero (inv_ne_zero hc) hr'
    have hypos : 0 < ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖ :=
      norm_pos_iff.mpr ((map_ne_zero_iff _ (NumberField.mixedEmbedding_injective K)).mpr hr')
    have hfac : mixedEmbedding K (algebraMap (𝓞 K) K r) = mixedEmbedding K c * mixedEmbedding K (i r) := by
      rw [← map_mul]
      congr 1
      show algebraMap (𝓞 K) K r = c * (c⁻¹ * algebraMap (𝓞 K) K r)
      rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    have hnorm : ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖
        ≤ ‖mixedEmbedding K c‖ * ‖mixedEmbedding K (i r)‖ := by
      rw [hfac]
      exact norm_mul_le _ _
    have hlow : ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖ / ‖mixedEmbedding K c‖
        ≤ ‖mixedEmbedding K (i r)‖ := by
      rw [div_le_iff₀ hc', mul_comm]
      exact hnorm
    have hlow_pos : 0 < ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖ / ‖mixedEmbedding K c‖ :=
      div_pos hypos hc'
    calc ‖f (i r)‖ ≤ C / ‖mixedEmbedding K (i r)‖ ^ s := hbound _ hα
      _ ≤ max C 0 / ‖mixedEmbedding K (i r)‖ ^ s :=
          div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg (norm_nonneg _) s)
      _ ≤ max C 0 / (‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖ / ‖mixedEmbedding K c‖) ^ s :=
          div_le_div_of_nonneg_left (le_max_right _ _) (pow_pos hlow_pos s)
            (pow_le_pow_left₀ hlow_pos.le hlow s)
      _ = B * ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s := by
          show _ = max C 0 * ‖mixedEmbedding K c‖ ^ s * ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s
          rw [div_pow, inv_pow, div_div_eq_mul_div, div_eq_mul_inv]
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (g := fun r : 𝓞 K => ‖f (i r)‖)
    (f := fun r : 𝓞 K => B * ‖mixedEmbedding K (algebraMap (𝓞 K) K r)‖⁻¹ ^ s
      + if r = 0 then ‖f (i 0)‖ else 0)
    (fun _ => norm_nonneg _) (fun r => ?_)
    ((hjs.mul_left B).add (summable_of_ne_finset_zero (s := {0}) ?_))
  · beta_reduce
    by_cases hr : r = 0
    · rw [if_pos hr, hr]
      have h0 : 0 ≤ B * ‖mixedEmbedding K (algebraMap (𝓞 K) K 0)‖⁻¹ ^ s :=
        mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg (norm_nonneg _) s))
          (pow_nonneg (inv_nonneg.2 (norm_nonneg _)) s)
      linarith
    · rw [if_neg hr, add_zero]
      exact hmain r hr
  · intro r hr
    rw [Finset.mem_singleton] at hr
    exact if_neg hr

end Glue

end

end P2GProbe.C4aK
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.P2GProbe P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.P2GProbe.C4aK"
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.P2GProbe"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "finiteAdelicGL2Subgroup IsKfSmooth productionPinsOf AdelicGL2 unipotentGL2 unipotentGL2_add IsGlobalAddChar whittakerCoefficient WhittakerCoefficientIntegrable IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar"
p2m_open "AutomorphicForm"
end AutomorphicForm
p2m_reactivate "P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.P2GProbe P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.P2GProbe.C4aK"
open IsDedekindDomain NumberField in
open NumberField.AdelicBox in
open scoped Classical in
open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.AutomorphicForm in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ)
    (harch : ∀ g : AdelicGL2 (𝓞 K) K,
      ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))) :
    (∀ (α : K) (g : AdelicGL2 (𝓞 K) K),
        WhittakerCoefficientIntegrable K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        Summable (fun α : K =>
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) := by
  have hB : P2GProbe.C4aK.BallInvariance K := fun h =>
    AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq h
  have hS : P2GProbe.C4aK.CharRescaling K := fun h =>
    AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar K h
  have hN : P2GProbe.C4aK.CharUnitNorm K := fun h x =>
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar K h x
  refine ⟨fun α g => ?_, fun g => ?_⟩
  · exact P2GProbe.C4aK.integrable_nuBox_of_continuous
      ((P2GProbe.C4aK.continuous_sl hB hsm harch g).mul (P2GProbe.C4aK.continuous_ch hψ α))
  · obtain ⟨c, hc, hsupp⟩ := P2GProbe.C4aK.support_sub hB hS hψ hleft hsm g
    obtain ⟨C, hC⟩ := P2GProbe.C4aK.decay_bound hB hS hN hψ hleft hsm harch g
    exact P2GProbe.C4aK.summable_of_support_of_decay hc hsupp (Nat.lt_succ_self _) hC

end S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace (solution)
