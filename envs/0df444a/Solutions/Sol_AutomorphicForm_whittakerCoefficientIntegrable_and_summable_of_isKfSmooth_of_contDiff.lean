-- Prove2me | solution 1 for AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/60e376bc-1742-5b41-a5d7-39fff3d1b22f

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicTraceProducer
import Theorems.Thm_AutomorphicForm_IsKfSmooth_exists_ideal_forall_apply_mul_conj_unipotentGL2_eq
import Theorems.Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff

set_option autoImplicit false

namespace P2GProbe
namespace C4a

noncomputable section

open IsDedekindDomain
open NumberField
open NumberField.AdelicBox
open NumberField.StandardAddChar
open NumberField.AdelicHaar
open NumberField.AdelicLevel
open NumberField.InfinitePlace.Completion
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff.AutomorphicForm"
open FLT.SmoothVectors
open MeasureTheory
open scoped Pointwise

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

private theorem continuous_of_invariant_of_line {A B : Type*} [TopologicalSpace A] [AddCommGroup A]
    [IsTopologicalAddGroup A] [TopologicalSpace B] (f : A → ℂ) {V : Set B} (hVo : IsOpen V)
    (Lr : ℝ → A) (Lf : B → A) (pA : A → ℝ) (pB : A → B) (hpA : Continuous pA) (hpB : Continuous pB)
    (hpB0 : pB 0 ∈ V) (hdec : ∀ z : A, z = Lr (pA z) + Lf (pB z))
    (hV : ∀ x : A, ∀ v ∈ V, f (x + Lf v) = f x)
    (hs : ∀ x : A, Continuous fun u : ℝ => f (x + Lr u)) : Continuous f := by
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

private theorem norm_second_difference_le {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F) {M : ℝ}
    (hM : ∀ u, ‖deriv (deriv F) u‖ ≤ M) (h : ℝ) :
    ‖F (h + h) - 2 * F h + F 0‖ ≤ M * (h * h) := by
  have hF' : ContDiff ℝ (1 + 1) F := by exact hF
  have hFd : Differentiable ℝ F := hF'.differentiable (by simp)
  have hF1 : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.mp hF').2.2
  have hF1d : Differentiable ℝ (deriv F) := hF1.differentiable one_ne_zero
  have step1 : ∀ u, ‖deriv F (u + h) - deriv F u‖ ≤ M * ‖h‖ := fun u => by
    have := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => hF1d x)
      (fun x _ => hM x) (Set.mem_univ u) (Set.mem_univ (u + h))
    simpa using this
  have hDhas : ∀ u, HasDerivAt (fun v => F (v + h) - F v) (deriv F (u + h) - deriv F u) u :=
    fun u => ((hFd (u + h)).hasDerivAt.comp_add_const u h).sub (hFd u).hasDerivAt
  have key := convex_univ.norm_image_sub_le_of_norm_deriv_le (fun x _ => (hDhas x).differentiableAt)
    (fun x _ => by rw [(hDhas x).deriv]; exact step1 x) (Set.mem_univ (0 : ℝ)) (Set.mem_univ h)
  have hre : F (h + h) - F h - (F (0 + h) - F 0) = F (h + h) - 2 * F h + F 0 := by
    rw [zero_add]; ring
  rw [hre, sub_zero, Real.norm_eq_abs] at key
  calc ‖F (h + h) - 2 * F h + F 0‖ ≤ M * |h| * |h| := key
    _ = M * (h * h) := by rw [mul_assoc, abs_mul_abs_self]

private theorem deriv_deriv_comp_add_const (G : ℝ → ℂ) (u : ℝ) :
    deriv (deriv fun u' => G (u' + u)) 0 = deriv (deriv G) u := by
  have h1 : (deriv fun u' => G (u' + u)) = fun u' => deriv G (u' + u) :=
    funext fun u' => deriv_comp_add_const G u u'
  rw [h1, deriv_comp_add_const, zero_add]

private theorem continuous_deriv_deriv {G : ℝ → ℂ} (hG : ContDiff ℝ 2 G) : Continuous (deriv (deriv G)) := by
  have hG' : ContDiff ℝ (1 + 1) G := by exact hG
  have h1 : ContDiff ℝ 1 (deriv G) := (contDiff_succ_iff_deriv.mp hG').2.2
  have h1' : ContDiff ℝ (0 + 1) (deriv G) := by simpa using h1
  exact ((contDiff_succ_iff_deriv.mp h1').2.2).continuous

private theorem exists_bound_of_continuous_of_forall_exists_mem {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} (hf : Continuous f) {C : Set X} (hC : IsCompact C)
    (hcov : ∀ x, ∃ c ∈ C, f x = f c) : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨c, hc, hxc⟩ := hcov x
  rw [hxc]
  exact hM c hc

private theorem exists_forall_eq_one_imp_eq_zsmul (χ : AddChar ℝ ℂ) (hχ : Continuous χ)
    (hne : ∃ u, χ u ≠ 1) : ∃ c : ℝ, ∀ u, χ u = 1 → ∃ n : ℤ, u = n • c := by
  let K : AddSubgroup ℝ :=
    { carrier := {u | χ u = 1}
      zero_mem' := by simp only [Set.mem_setOf_eq]; exact AddChar.map_zero_eq_one χ
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [AddChar.map_add_eq_mul, ha, hb, one_mul]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [AddChar.map_neg_eq_inv, ha, inv_one] }
  have hKc : IsClosed (K : Set ℝ) := by
    have : (K : Set ℝ) = χ ⁻¹' {1} := by ext u; simp [K]
    rw [this]
    exact isClosed_singleton.preimage hχ
  rcases K.dense_or_cyclic with hd | ⟨a, ha⟩
  · exfalso
    obtain ⟨u, hu⟩ := hne
    have huniv : (K : Set ℝ) = Set.univ := by
      rw [← hKc.closure_eq]; exact hd.closure_eq
    have : u ∈ (K : Set ℝ) := huniv ▸ Set.mem_univ u
    exact hu this
  · refine ⟨a, fun u hu => ?_⟩
    have hmem : u ∈ K := hu
    rw [ha, AddSubgroup.mem_closure_singleton] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, hn.symm⟩

private theorem summable_of_support_zsmul_of_norm_le {f : ℚ → ℂ} {c K : ℝ}
    (hsupp : ∀ α : ℚ, f α ≠ 0 → ∃ n : ℤ, (α : ℝ) = n • c)
    (hbound : ∀ α : ℚ, α ≠ 0 → ‖f α‖ ≤ K / ((α : ℝ) ^ 2)) : Summable f := by
  by_cases hex : ∃ α₀ : ℚ, α₀ ≠ 0 ∧ f α₀ ≠ 0
  · obtain ⟨α₀, hα₀, hf₀⟩ := hex
    obtain ⟨n₀, hn₀⟩ := hsupp α₀ hf₀
    have hn₀ne : n₀ ≠ 0 := by
      rintro rfl
      apply hα₀
      exact_mod_cast (by simpa using hn₀ : (α₀ : ℝ) = 0)

    set d : ℚ := α₀ / n₀ with hd_def
    have hdne : d ≠ 0 := div_ne_zero hα₀ (by exact_mod_cast hn₀ne)
    have hcd : c = (d : ℝ) := by
      have hn₀r : (n₀ : ℝ) ≠ 0 := by exact_mod_cast hn₀ne
      rw [zsmul_eq_mul] at hn₀
      rw [hd_def]; push_cast
      field_simp
      linarith [hn₀]
    let e : ℤ → ℚ := fun n => n * d
    have he_inj : Function.Injective e := fun m n hmn => by
      have : (m : ℚ) * d = n * d := hmn
      exact_mod_cast mul_right_cancel₀ hdne this
    have hvan : ∀ α, α ∉ Set.range e → f α = 0 := by
      intro α hα
      by_contra hfα
      obtain ⟨n, hn⟩ := hsupp α hfα
      apply hα
      refine ⟨n, ?_⟩
      rw [hcd, zsmul_eq_mul] at hn
      exact_mod_cast hn.symm
    refine (he_inj.summable_iff hvan).1 ?_

    set K' : ℝ := max K 0 / ((d : ℝ) ^ 2) with hK'
    have hK'0 : 0 ≤ K' := div_nonneg (le_max_right _ _) (sq_nonneg _)
    have hg1 : Summable fun n : ℤ => K' * (1 / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_int_pow.2 one_lt_two).mul_left K'
    have hg2 : Summable fun n : ℤ => if n = 0 then ‖f 0‖ else (0 : ℝ) := by
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      simp only [Finset.mem_singleton] at hn
      simp [hn]
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hg1.add hg2)
    simp only [Function.comp_apply]
    by_cases hn : n = 0
    · subst hn
      simp [e]
    · have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have hen : e n ≠ 0 := mul_ne_zero (by exact_mod_cast hn) hdne
      have hb := hbound (e n) hen
      simp only [hn, if_false, add_zero]
      refine hb.trans ?_
      have hcast : ((e n : ℚ) : ℝ) = (n : ℝ) * (d : ℝ) := by simp [e]
      rw [hcast, hK', mul_pow]
      have hrhs : max K 0 / (d : ℝ) ^ 2 * (1 / (n : ℝ) ^ 2) = max K 0 / ((n : ℝ) ^ 2 * (d : ℝ) ^ 2) := by
        rw [div_mul_div_comm, mul_one, mul_comm ((d : ℝ) ^ 2) ((n : ℝ) ^ 2)]
      rw [hrhs]
      gcongr
      exact le_max_left _ _
  · refine summable_of_ne_finset_zero (s := {0}) fun α hα => ?_
    simp only [Finset.mem_singleton] at hα
    by_contra hfα
    exact hex ⟨α, hα, hfα⟩

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

private theorem norm_integral_mul_le_of_second_difference {X : Type*} [MeasurableSpace X] [AddCommGroup X]
    (ν : Measure X) [IsProbabilityMeasure ν] {s e : X → ℂ} {y : X} {ω : ℂ} (hω : ω ≠ 1)
    (he : ∀ x, e (x + y) = e x * ω) (hen : ∀ x, ‖e x‖ = 1)
    (hT1 : ∫ x, s (x + y) * e (x + y) ∂ν = ∫ x, s x * e x ∂ν)
    (hT2 : ∫ x, s (x + y + y) * e (x + y) ∂ν = ∫ x, s (x + y) * e x ∂ν)
    (hi0 : Integrable (fun x => s x * e x) ν) (hi1 : Integrable (fun x => s (x + y) * e x) ν)
    (hi2 : Integrable (fun x => s (x + y + y) * e x) ν)
    {D : ℝ} (hΔ : ∀ x, ‖s (x + y + y) - 2 * s (x + y) + s x‖ ≤ D) :
    ‖∫ x, s x * e x ∂ν‖ ≤ D / ‖ω⁻¹ - 1‖ ^ 2 := by
  have hω0 : ω ≠ 0 := by
    intro h0
    have h1 := hen (0 + y)
    rw [he, norm_mul, hen, one_mul, h0, norm_zero] at h1
    exact zero_ne_one h1
  set W := ∫ x, s x * e x ∂ν with hW
  set I1 := ∫ x, s (x + y) * e x ∂ν with hI1
  set I2 := ∫ x, s (x + y + y) * e x ∂ν with hI2
  have e1 : ∫ x, s (x + y) * e (x + y) ∂ν = ω * I1 := by
    have hfun : (fun x => s (x + y) * e (x + y)) = fun x => ω * (s (x + y) * e x) := by
      funext x; rw [he]; ring
    have hcm : ∫ x, ω * (s (x + y) * e x) ∂ν = ω * ∫ x, s (x + y) * e x ∂ν := integral_const_mul ω _
    rw [hfun, hcm]
  have e2 : ∫ x, s (x + y + y) * e (x + y) ∂ν = ω * I2 := by
    have hfun : (fun x => s (x + y + y) * e (x + y)) = fun x => ω * (s (x + y + y) * e x) := by
      funext x; rw [he]; ring
    have hcm : ∫ x, ω * (s (x + y + y) * e x) ∂ν = ω * ∫ x, s (x + y + y) * e x ∂ν :=
      integral_const_mul ω _
    rw [hfun, hcm]
  have hI1W : I1 = ω⁻¹ * W := by
    rw [e1] at hT1; rw [← hT1]; field_simp
  have hI2W : I2 = ω⁻¹ * ω⁻¹ * W := by
    rw [e2] at hT2; rw [mul_assoc, ← hI1W, ← hT2]; field_simp
  have hΔint : ∫ x, (s (x + y + y) - 2 * s (x + y) + s x) * e x ∂ν = (ω⁻¹ - 1) ^ 2 * W := by
    have hsplit : (fun x => (s (x + y + y) - 2 * s (x + y) + s x) * e x)
        = fun x => s (x + y + y) * e x - 2 * (s (x + y) * e x) + s x * e x := by
      funext x; ring
    have hi1' : Integrable (fun x => 2 * (s (x + y) * e x)) ν := hi1.const_mul 2
    have hi12 : Integrable (fun x => s (x + y + y) * e x - 2 * (s (x + y) * e x)) ν := hi2.sub hi1'
    have hcm : ∫ x, 2 * (s (x + y) * e x) ∂ν = 2 * ∫ x, s (x + y) * e x ∂ν := integral_const_mul 2 _
    rw [hsplit, integral_add hi12 hi0, integral_sub hi2 hi1', hcm, ← hI2, ← hI1, ← hW, hI2W, hI1W]
    ring
  have hnorm : ‖∫ x, (s (x + y + y) - 2 * s (x + y) + s x) * e x ∂ν‖ ≤ D := by
    have := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun x => (s (x + y + y) - 2 * s (x + y) + s x) * e x) (C := D)
      (Filter.Eventually.of_forall fun x => by rw [norm_mul, hen, mul_one]; exact hΔ x)
    simpa using this
  rw [hΔint, norm_mul, norm_pow] at hnorm
  have hpos : 0 < ‖ω⁻¹ - 1‖ ^ 2 := by
    have : ω⁻¹ - 1 ≠ 0 := sub_ne_zero.2 (by rwa [Ne, inv_eq_one])
    positivity
  rw [le_div_iff₀ hpos]
  linarith [hnorm]

section Glue

attribute [local instance] NumberField.AdelicHaar.adeleBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar
attribute [local instance] NumberField.AdelicBox.isProbabilityMeasure_cond_adelicBox

local notation "nuBox" => ProbabilityTheory.cond (adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ)

private abbrev BallInvariance : Prop :=
  ∀ {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}, IsKfSmooth ℚ φ → ∃ 𝔫 : Ideal (𝓞 ℚ), 𝔫 ≠ ⊥ ∧
    ∀ (g x : AdelicGL2 (𝓞 ℚ) ℚ),
      NumberField.AdelicLevel.glFin (𝓞 ℚ) ℚ x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 ℚ) ℚ →
      ∀ (t : AdeleRing (𝓞 ℚ) ℚ), NumberField.AdelicLevel.adeleArch (𝓞 ℚ) ℚ t = 0 →
        NumberField.AdelicLevel.adeleFin (𝓞 ℚ) ℚ t ∈ NumberField.AdelicLevel.idealBall (𝓞 ℚ) ℚ 𝔫 →
          φ (g * (x⁻¹ * unipotentGL2 t * x)) = φ g

private abbrev CharRescaling : Prop :=
  ∀ {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}, IsGlobalAddChar ℚ ψ → ∃ a : ℚ, a ≠ 0 ∧
    ∀ x : AdeleRing (𝓞 ℚ) ℚ,
      ψ x = NumberField.StandardAddChar.stdAddChar ℚ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * x)

private abbrev CharUnitNorm : Prop :=
  ∀ {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}, IsGlobalAddChar ℚ ψ → ∀ x : AdeleRing (𝓞 ℚ) ℚ, ‖ψ x‖ = 1

private def sl (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  φ (unipotentGL2 x * g)

private def ch (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (α : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))

private def archPt (r : ℝ) : AdeleRing (𝓞 ℚ) ℚ := (ratArchLine r, 0)

private theorem archPt_zero : archPt 0 = 0 :=
  Prod.ext (map_zero ratArchLine) rfl

private theorem archPt_add (a b : ℝ) : archPt (a + b) = archPt a + archPt b :=
  Prod.ext (map_add ratArchLine a b) (zero_add (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)).symm

private def finPt (v : FiniteAdeleRing (𝓞 ℚ) ℚ) : AdeleRing (𝓞 ℚ) ℚ := (0, v)

private theorem ratArchLine_mul (a b : ℝ) : ratArchLine (a * b) = ratArchLine a * ratArchLine b := by
  funext v
  rw [ratArchLine_apply]
  exact map_mul (ringEquivRealOfIsReal (NumberField.StandardAddChar.isReal_rat_infinitePlace v)).symm a b

private theorem rat_mul_archPt (a : ℚ) (h : ℝ) :
    algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * archPt h = archPt ((a : ℝ) * h) := by
  refine Prod.ext ?_ ?_
  · show algebraMap ℚ (InfiniteAdeleRing ℚ) a * ratArchLine h = ratArchLine ((a : ℝ) * h)
    rw [ratArchLine_mul, ratArchLine_ratCast]
  · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a * 0 = 0
    exact mul_zero _

private theorem algebraMap_eq_archPt_add (w : ℚ) :
    algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) w
      = archPt (w : ℝ) + finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) w) := by
  refine Prod.ext ?_ ?_
  · show algebraMap ℚ (InfiniteAdeleRing ℚ) w = ratArchLine (w : ℝ) + 0
    rw [ratArchLine_ratCast, add_zero]
  · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) w = 0 + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) w
    rw [zero_add]

private theorem rat_mul_finPt (a q : ℚ) :
    algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) a * finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q)
      = finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (a * q)) := by
  refine Prod.ext ?_ ?_
  · show algebraMap ℚ (InfiniteAdeleRing ℚ) a * 0 = 0
    exact mul_zero _
  · show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) a * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (a * q)
    exact (map_mul _ _ _).symm

private theorem continuous_archPt : Continuous archPt :=
  continuous_ratArchLine.prodMk continuous_const

private noncomputable def archProj (z : InfiniteAdeleRing ℚ) : ℝ :=
  ringEquivRealOfIsReal (NumberField.StandardAddChar.isReal_rat_infinitePlace (default : InfinitePlace ℚ)) (z default)

private theorem ratArchLine_archProj (z : InfiniteAdeleRing ℚ) : ratArchLine (archProj z) = z := by
  funext v
  have hv : v = default := Subsingleton.elim _ _
  subst hv
  rw [ratArchLine_apply]
  exact (ringEquivRealOfIsReal (NumberField.StandardAddChar.isReal_rat_infinitePlace (default : InfinitePlace ℚ))).symm_apply_apply
    (z default)

private theorem continuous_archProj : Continuous archProj :=
  (isometryEquivRealOfIsReal (NumberField.StandardAddChar.isReal_rat_infinitePlace (default : InfinitePlace ℚ))).continuous.comp
    (continuous_apply (default : InfinitePlace ℚ))

private theorem continuous_archProj_fst : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => archProj z.1 :=
  continuous_archProj.comp continuous_fst

private theorem continuous_snd_adele : Continuous fun z : AdeleRing (𝓞 ℚ) ℚ => z.2 :=
  continuous_snd

private theorem adele_decomp (z : AdeleRing (𝓞 ℚ) ℚ) : z = archPt (archProj z.1) + finPt z.2 := by
  refine Prod.ext ?_ ?_
  · show z.1 = ratArchLine (archProj z.1) + 0
    rw [ratArchLine_archProj, add_zero]
  · show z.2 = 0 + z.2
    rw [zero_add]

private theorem algebraMap_mem_idealBall_of_mem {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) {r : 𝓞 ℚ} (hr : r ∈ N) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) ∈ idealBall (𝓞 ℚ) ℚ N := by
  classical
  intro v
  have hmem : r ∈ ⨅ w : HeightOneSpectrum (𝓞 ℚ), w.maxPowDividing N := by
    rw [Ideal.iInf_maxPowDividing_eq hN]
    exact hr
  have hv := Ideal.mem_iInf.1 hmem v
  rw [show algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ r) v
        = algebraMap ℚ (v.adicCompletion ℚ) (algebraMap (𝓞 ℚ) ℚ r) from rfl,
    valued_algebraMap, idealBound_of_ne_bot hN, HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact hv

private theorem exists_ideal_sl (hB : BallInvariance) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsKfSmooth ℚ φ)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ 𝔫 : Ideal (𝓞 ℚ), 𝔫 ≠ ⊥ ∧ ∀ (x : AdeleRing (𝓞 ℚ) ℚ), ∀ v ∈ idealBall (𝓞 ℚ) ℚ 𝔫,
      sl φ g (x + finPt v) = sl φ g x := by
  have hsm' : IsKfSmooth ℚ (fun h => φ (h * g)) := by
    haveI : (finiteAdelicGL2Subgroup ℚ).Normal :=
      MonoidHom.normal_ker (NumberField.AdelicLevel.glArch (𝓞 ℚ) ℚ)
    exact isSmoothVector_mk_mul_right (finiteAdelicGL2Subgroup ℚ) hsm g
  obtain ⟨𝔫, h𝔫, hinv⟩ := hB hsm'
  refine ⟨𝔫, h𝔫, fun x v hv => ?_⟩
  have h1 : glFin (𝓞 ℚ) ℚ (1 : AdelicGL2 (𝓞 ℚ) ℚ) ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [map_one]
    exact Subgroup.one_mem _
  have h2 := hinv (unipotentGL2 x) 1 h1 (finPt v) rfl hv
  simp only [inv_one, one_mul, mul_one] at h2
  unfold sl
  rw [unipotentGL2_add]
  exact h2

private theorem sl_add_algebraMap {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    sl φ g (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k) = sl φ g x := by
  unfold sl
  rw [add_comm, unipotentGL2_add, mul_assoc, hleft]

private theorem sl_add_archPt_eq (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    (fun u : ℝ => sl φ g (x + archPt u))
      = fun u : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine u, 0) * (unipotentGL2 x * g)) := by
  funext u
  unfold sl archPt
  rw [add_comm, unipotentGL2_add, mul_assoc]

private theorem contDiff_slice {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)))
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ContDiff ℝ 2 fun u : ℝ => sl φ g (x + archPt u) := by
  rw [sl_add_archPt_eq]
  exact harch _

private theorem continuous_sl (hB : BallInvariance) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsKfSmooth ℚ φ)
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)))
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : Continuous (sl φ g) := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  exact continuous_of_invariant_of_line (sl φ g) (isOpen_idealBall (𝓞 ℚ) ℚ h𝔫) archPt finPt
    (fun z => archProj z.1) (fun z => z.2) continuous_archProj_fst continuous_snd_adele
    (zero_mem_idealBall 𝔫) adele_decomp hinv (fun x => (contDiff_slice harch g x).continuous)

private theorem ch_add (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (α : ℚ) (x y : AdeleRing (𝓞 ℚ) ℚ) :
    ch ψ α (x + y) = ch ψ α x * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * y)) := by
  unfold ch
  rw [mul_add, neg_add, AddChar.map_add_eq_mul]

private theorem ch_add_algebraMap {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (α : ℚ)
    (k : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ch ψ α (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k) = ch ψ α x := by
  rw [ch_add, ← map_mul, ← map_neg, hψ.principalInvariant, mul_one]

private theorem norm_ch (hN : CharUnitNorm) {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (α : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ‖ch ψ α x‖ = 1 :=
  hN hψ _

private theorem continuous_ch {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (α : ℚ) :
    Continuous (ch ψ α) := by
  show Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * x))
  exact hψ.continuous.comp ((continuous_const.mul continuous_id).neg)

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) :=
  (Set.countable_range (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ))).to_subtype

private theorem integrable_nuBox_of_continuous {f : AdeleRing (𝓞 ℚ) ℚ → ℂ} (hf : Continuous f) :
    Integrable f nuBox := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset ℚ
  exact integrable_cond_of_continuous (adelicAddHaar (𝓞 ℚ) ℚ) hC hBC (measurableSet_adelicBox ℚ)
    (adelicAddHaar_adelicBox_pos ℚ).ne' (adelicAddHaar_adelicBox_lt_top ℚ).ne hf

private theorem integral_nuBox_add_right {f : AdeleRing (𝓞 ℚ) ℚ → ℂ}
    (hf : ∀ (k : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ), f (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k) = f x)
    (y : AdeleRing (𝓞 ℚ) ℚ) : ∫ x, f (x + y) ∂nuBox = ∫ x, f x ∂nuBox := by
  haveI := countable_principalSubgroup
  exact integral_cond_add_right_of_periodic (adelicAddHaar (𝓞 ℚ) ℚ)
    (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) (measurableSet_adelicBox ℚ)
    (isAddFundamentalDomain_adelicBox ℚ _) (by rintro _ ⟨k, rfl⟩ x; exact hf k x) y

private theorem exists_rat_ball {𝔫 : Ideal (𝓞 ℚ)} (h𝔫 : 𝔫 ≠ ⊥) :
    ∃ q : ℚ, q ≠ 0 ∧ algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ idealBall (𝓞 ℚ) ℚ 𝔫 := by
  obtain ⟨n, hn𝔫, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔫
  exact ⟨algebraMap (𝓞 ℚ) ℚ n, (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).2 hn0,
    algebraMap_mem_idealBall_of_mem h𝔫 hn𝔫⟩

private noncomputable def archChar (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) : AddChar ℝ ℂ where
  toFun h := ψ (archPt h)
  map_zero_eq_one' := by
    show ψ (archPt 0) = 1
    rw [archPt_zero]
    exact AddChar.map_zero_eq_one ψ
  map_add_eq_mul' a b := by
    show ψ (archPt (a + b)) = ψ (archPt a) * ψ (archPt b)
    rw [archPt_add]
    exact AddChar.map_add_eq_mul ψ _ _

private theorem archChar_apply (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (h : ℝ) : archChar ψ h = ψ (archPt h) := rfl

private theorem continuous_archChar {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) :
    Continuous (archChar ψ) := by
  show Continuous fun h : ℝ => ψ (archPt h)
  exact hψ.continuous.comp continuous_archPt

private theorem stdAddChar_archPt (r : ℝ) :
    stdAddChar ℚ (archPt r) = psiArch ((adelicTraceData ℚ).traceInf (ratArchLine r)) := by
  show (adelicTraceData ℚ).psiK (archPt r) = _
  rw [AdelicTraceData.psiK_apply, AdelicTraceData.adelicTrace_apply, psiQ_apply]
  unfold archPt
  dsimp only
  rw [map_zero, AddChar.map_zero_eq_one, mul_one]

private theorem exists_archChar_ne_one (hS : CharRescaling) {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) :
    ∃ h : ℝ, archChar ψ h ≠ 1 := by
  obtain ⟨a, ha, hrs⟩ := hS hψ
  obtain ⟨z, hz⟩ := (adelicTraceData ℚ).traceInf_surjective (algebraMap ℚ (InfiniteAdeleRing ℚ) (1 / 2 : ℚ))
  obtain ⟨r, hr⟩ := ratArchLine_surjective z
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  refine ⟨r / (a : ℝ), ?_⟩
  have hah : (a : ℝ) * (r / (a : ℝ)) = r := by field_simp
  rw [archChar_apply, hrs, rat_mul_archPt, hah, stdAddChar_archPt, hr, hz, psiArch_algebraMap]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * ((1 / 2 : ℚ) : ℂ)) = -1 := by
    rw [show (2 * Real.pi * Complex.I * ((1 / 2 : ℚ) : ℂ)) = Real.pi * Complex.I by push_cast; ring]
    exact Complex.exp_pi_mul_I
  rw [hexp]
  norm_num

private theorem prod_periodic {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (α : ℚ)
    (y : AdeleRing (𝓞 ℚ) ℚ) (k : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    sl φ g (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + y) * ch ψ α (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k)
      = sl φ g (x + y) * ch ψ α x := by
  rw [add_right_comm, sl_add_algebraMap hleft, ch_add_algebraMap hψ]

private theorem prod_periodic₀ {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (α : ℚ)
    (k : ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) :
    sl φ g (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k) * ch ψ α (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k)
      = sl φ g x * ch ψ α x := by
  rw [sl_add_algebraMap hleft, ch_add_algebraMap hψ]

private theorem support_archChar (hB : BallInvariance) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ} (hψ : IsGlobalAddChar ℚ ψ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hsm : IsKfSmooth ℚ φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ q : ℚ, q ≠ 0 ∧ ∀ α : ℚ, (∫ x, sl φ g x * ch ψ α x ∂nuBox) ≠ 0 → archChar ψ ((α * q : ℚ) : ℝ) = 1 := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  obtain ⟨q, hq, hqb⟩ := exists_rat_ball h𝔫
  refine ⟨q, hq, fun α hW => ?_⟩
  have hs : ∀ x, sl φ g (x + finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q)) = sl φ g x :=
    fun x => hinv x _ hqb
  have he : ∀ x, ch ψ α (x + finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q)) = ch ψ α x *
      ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q))) :=
    fun x => ch_add ψ α x _
  have hT := integral_nuBox_add_right (f := fun x => sl φ g x * ch ψ α x) (prod_periodic₀ hleft hψ g α)
    (finPt (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q))
  have hω := eq_one_of_integral_mul_ne_zero nuBox (s := sl φ g) (e := ch ψ α) hs he hT hW
  rw [AddChar.map_neg_eq_inv, inv_eq_one, rat_mul_finPt] at hω
  have hdiag : ψ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) (α * q)) = 1 := by rw [hψ.principalInvariant]
  rw [algebraMap_eq_archPt_add, AddChar.map_add_eq_mul, hω, mul_one] at hdiag
  exact hdiag

private noncomputable def s2 (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) : ℂ :=
  deriv (deriv fun u : ℝ => sl φ g (x + archPt u)) 0

private theorem s2_add_archPt (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ)
    (u : ℝ) : s2 φ g (x + archPt u) = deriv (deriv fun u' : ℝ => sl φ g (x + archPt u')) u := by
  unfold s2
  have hAB : (fun u' : ℝ => sl φ g (x + archPt u + archPt u'))
      = fun u' : ℝ => (fun t : ℝ => sl φ g (x + archPt t)) (u' + u) := by
    funext u'
    show sl φ g (x + archPt u + archPt u') = sl φ g (x + archPt (u' + u))
    rw [archPt_add, add_assoc, add_comm (archPt u)]
  rw [hAB]
  exact deriv_deriv_comp_add_const (fun t : ℝ => sl φ g (x + archPt t)) u

private theorem s2_add_fin {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (g : AdelicGL2 (𝓞 ℚ) ℚ) {V : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hinv : ∀ (x : AdeleRing (𝓞 ℚ) ℚ), ∀ v ∈ V, sl φ g (x + finPt v) = sl φ g x)
    (x : AdeleRing (𝓞 ℚ) ℚ) (v : FiniteAdeleRing (𝓞 ℚ) ℚ) (hv : v ∈ V) :
    s2 φ g (x + finPt v) = s2 φ g x := by
  unfold s2
  have hAB : (fun u : ℝ => sl φ g (x + finPt v + archPt u))
      = fun u : ℝ => sl φ g (x + archPt u) := by
    funext u
    rw [add_right_comm, hinv _ _ hv]
  rw [hAB]

private theorem s2_add_algebraMap {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (g : AdelicGL2 (𝓞 ℚ) ℚ) (x : AdeleRing (𝓞 ℚ) ℚ) (k : ℚ) :
    s2 φ g (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k) = s2 φ g x := by
  unfold s2
  have hAB : (fun u : ℝ => sl φ g (x + algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) k + archPt u))
      = fun u : ℝ => sl φ g (x + archPt u) := by
    funext u
    rw [add_right_comm, sl_add_algebraMap hleft]
  rw [hAB]

private theorem continuous_s2 (hB : BallInvariance) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (hsm : IsKfSmooth ℚ φ)
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)))
    (g : AdelicGL2 (𝓞 ℚ) ℚ) : Continuous (s2 φ g) := by
  obtain ⟨𝔫, h𝔫, hinv⟩ := exists_ideal_sl hB hsm g
  refine continuous_of_invariant_of_line (s2 φ g) (isOpen_idealBall (𝓞 ℚ) ℚ h𝔫) archPt finPt
    (fun z => archProj z.1) (fun z => z.2) continuous_archProj_fst continuous_snd_adele
    (zero_mem_idealBall 𝔫) adele_decomp (fun x v hv => s2_add_fin g hinv x v hv) (fun x => ?_)
  have hfun : (fun u : ℝ => s2 φ g (x + archPt u))
      = fun u : ℝ => deriv (deriv fun u' : ℝ => sl φ g (x + archPt u')) u :=
    funext fun u => s2_add_archPt φ g x u
  rw [hfun]
  exact continuous_deriv_deriv (contDiff_slice harch g x)

private theorem exists_bound_s2 (hB : BallInvariance) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hsm : IsKfSmooth ℚ φ)
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)))
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ M : ℝ, ∀ (x : AdeleRing (𝓞 ℚ) ℚ) (u : ℝ), ‖deriv (deriv fun u' : ℝ => sl φ g (x + archPt u')) u‖ ≤ M := by
  obtain ⟨C, hC, hBC⟩ := exists_isCompact_adelicBox_subset ℚ
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_of_forall_exists_mem (continuous_s2 hB hsm harch g) hC fun x => by
    obtain ⟨k, hk, -⟩ := existsUnique_algebraMap_add_mem_adelicBox ℚ x
    refine ⟨_, hBC hk, ?_⟩
    rw [add_comm, s2_add_algebraMap hleft]
  refine ⟨M, fun x u => ?_⟩
  rw [← s2_add_archPt]
  exact hM _

private theorem decay_bound (hB : BallInvariance) (hS : CharRescaling) (hN : CharUnitNorm) {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} {ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ}
    (hψ : IsGlobalAddChar ℚ ψ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hsm : IsKfSmooth ℚ φ)
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ => φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g)))
    (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ K : ℝ, ∀ α : ℚ, α ≠ 0 → ‖∫ x, sl φ g x * ch ψ α x ∂nuBox‖ ≤ K / ((α : ℝ) ^ 2) := by
  obtain ⟨h₀, hh₀⟩ := exists_archChar_ne_one hS hψ
  obtain ⟨M, hM⟩ := exists_bound_s2 hB hleft hsm harch g
  have hsl : Continuous (sl φ g) := continuous_sl hB hsm harch g
  refine ⟨M * (h₀ * h₀) / ‖(ψ (-(archPt h₀)))⁻¹ - 1‖ ^ 2, fun α hα => ?_⟩
  have hα' : (α : ℝ) ≠ 0 := by exact_mod_cast hα
  have hαh : (α : ℝ) * (h₀ / (α : ℝ)) = h₀ := by field_simp
  have hωeq : ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * archPt (h₀ / (α : ℝ)))) = ψ (-(archPt h₀)) := by
    rw [rat_mul_archPt, hαh]
  have hω : ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * archPt (h₀ / (α : ℝ)))) ≠ 1 := by
    rw [hωeq, AddChar.map_neg_eq_inv, Ne, inv_eq_one]
    exact hh₀
  have he : ∀ x, ch ψ α (x + archPt (h₀ / (α : ℝ)))
      = ch ψ α x * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) α * archPt (h₀ / (α : ℝ)))) := fun x => ch_add ψ α x _
  have hen : ∀ x, ‖ch ψ α x‖ = 1 := norm_ch hN hψ α
  have hT1 := integral_nuBox_add_right (f := fun x => sl φ g x * ch ψ α x) (prod_periodic₀ hleft hψ g α)
    (archPt (h₀ / (α : ℝ)))
  have hT2 := integral_nuBox_add_right (f := fun x => sl φ g (x + archPt (h₀ / (α : ℝ))) * ch ψ α x)
    (prod_periodic hleft hψ g α _) (archPt (h₀ / (α : ℝ)))
  have hch : Continuous (ch ψ α) := continuous_ch hψ α
  have hc0 : Continuous fun x => sl φ g x * ch ψ α x := hsl.mul hch
  have hc1 : Continuous fun x => sl φ g (x + archPt (h₀ / (α : ℝ))) * ch ψ α x :=
    (hsl.comp (continuous_add_const _)).mul hch
  have hc2 : Continuous fun x => sl φ g (x + archPt (h₀ / (α : ℝ)) + archPt (h₀ / (α : ℝ))) * ch ψ α x :=
    (hsl.comp ((continuous_add_const _).add continuous_const)).mul hch
  have hΔ : ∀ x, ‖sl φ g (x + archPt (h₀ / (α : ℝ)) + archPt (h₀ / (α : ℝ))) - 2 * sl φ g (x + archPt (h₀ / (α : ℝ)))
      + sl φ g x‖ ≤ M * ((h₀ / (α : ℝ)) * (h₀ / (α : ℝ))) := by
    intro x
    have h := norm_second_difference_le (contDiff_slice harch g x) (hM x) (h₀ / (α : ℝ))
    rw [archPt_add, ← add_assoc, archPt_zero, add_zero] at h
    exact h
  have hmain := norm_integral_mul_le_of_second_difference nuBox (s := sl φ g) (e := ch ψ α) hω he hen hT1 hT2
    (integrable_nuBox_of_continuous hc0) (integrable_nuBox_of_continuous hc1) (integrable_nuBox_of_continuous hc2) hΔ
  rw [hωeq] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hh : h₀ / (α : ℝ) * (h₀ / (α : ℝ)) = h₀ * h₀ / (α : ℝ) ^ 2 := by
    rw [div_mul_div_comm, pow_two]
  rw [hh, ← mul_div_assoc, div_right_comm]

end Glue

end

end P2GProbe.C4a

namespace AutomorphicForm
p2m_export "AutomorphicForm" "finiteAdelicGL2Subgroup IsKfSmooth productionPinsOf AdelicGL2 unipotentGL2 unipotentGL2_add IsGlobalAddChar whittakerCoefficient WhittakerCoefficientIntegrable IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar"
p2m_open "AutomorphicForm"
end AutomorphicForm
open IsDedekindDomain NumberField in
open NumberField.AdelicBox NumberField.StandardAddChar in
open _root_.AutomorphicForm _root_.P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff.AutomorphicForm in
theorem solution
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
    (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hleft : ∀ (β : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * g) = φ g)
    (hsm : IsKfSmooth ℚ φ)
    (harch : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ContDiff ℝ 2 (fun t : ℝ =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 ℚ) ℚ) (ratArchLine t, 0) * g))) :
    (∀ (α : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α g) ∧
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Summable (fun α : ℚ =>
          whittakerCoefficient ℚ (productionPinsOf ℚ D U gen (adelicBox ℚ)) ψ φ α g) := by
  have hB : P2GProbe.C4a.BallInvariance := fun h =>
    AutomorphicForm.IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq h
  have hS : P2GProbe.C4a.CharRescaling := fun h =>
    AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar ℚ h
  have hN : P2GProbe.C4a.CharUnitNorm := fun h x =>
    NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar ℚ h x
  refine ⟨fun α g => ?_, fun g => ?_⟩
  · exact P2GProbe.C4a.integrable_nuBox_of_continuous
      ((P2GProbe.C4a.continuous_sl hB hsm harch g).mul (P2GProbe.C4a.continuous_ch hψ α))
  · obtain ⟨q, hq, hsupp⟩ := P2GProbe.C4a.support_archChar hB hψ hleft hsm g
    obtain ⟨K, hK⟩ := P2GProbe.C4a.decay_bound hB hS hN hψ hleft hsm harch g
    obtain ⟨c, hc⟩ := P2GProbe.C4a.exists_forall_eq_one_imp_eq_zsmul (P2GProbe.C4a.archChar ψ)
      (P2GProbe.C4a.continuous_archChar hψ) (P2GProbe.C4a.exists_archChar_ne_one hS hψ)
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    refine P2GProbe.C4a.summable_of_support_zsmul_of_norm_le (c := c / (q : ℝ)) (K := K) (fun α hα => ?_)
      (fun α hα => hK α hα)
    obtain ⟨n, hn⟩ := hc _ (hsupp α hα)
    refine ⟨n, ?_⟩
    rw [zsmul_eq_mul] at hn ⊢
    push_cast at hn
    field_simp
    linarith [hn]

end S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff
end P2MW
export P2MW.S_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff (solution)
