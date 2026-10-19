-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_coercive_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:24:13.357659+00:00
-- url     : https://prove2.me/submissions/377ffec0-5722-40ab-b00f-04f9359207bb

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity
import Theorems.Thm_CauchyRiemannIndex_gaussian_poincare_rectangle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct



namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- Matrices as continuous linear maps of `ℝ²ⁿ`, continuously in the matrix. -/
def matCLM (n : ℕ) : Mat n →ₗ[ℝ] (Vec n →L[ℝ] Vec n) :=
  (LinearMap.toContinuousLinearMap : (Vec n →ₗ[ℝ] Vec n) ≃ₗ[ℝ] (Vec n →L[ℝ] Vec n)).toLinearMap ∘ₗ
    (Matrix.toEuclideanLin : Mat n ≃ₗ[ℝ] (Vec n →ₗ[ℝ] Vec n)).toLinearMap

lemma matCLM_apply (A : Mat n) (v : Vec n) : matCLM n A v = Matrix.toEuclideanLin A v := rfl

lemma continuous_matCLM : Continuous (matCLM n) := LinearMap.continuous_of_finiteDimensional _

/-- A uniform operator bound for a continuous `1`-periodic matrix loop. -/
lemma exists_bound_loop (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (hper : Function.Periodic Sinf 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t (v : Vec n), ‖Matrix.toEuclideanLin (Sinf t) v‖ ≤ M * ‖v‖ := by
  have hg : Continuous fun t => matCLM n (Sinf t) := continuous_matCLM.comp hc
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t v => ?_⟩
  obtain ⟨y, hy, hty⟩ := hper.exists_mem_Ico₀ one_pos t
  rw [← matCLM_apply, hty]
  calc ‖matCLM n (Sinf y) v‖ ≤ ‖matCLM n (Sinf y)‖ * ‖v‖ := (matCLM n (Sinf y)).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by
      gcongr
      exact (hC y (Set.Ico_subset_Icc_self hy)).trans (le_max_left _ _)

lemma exists_bound_mat (A : Mat n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Vec n), ‖Matrix.toEuclideanLin A v‖ ≤ M * ‖v‖ :=
  ⟨‖matCLM n A‖, norm_nonneg _, fun v => (matCLM n A).le_opNorm v⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous map on `ℝ × ℝ` vanishing for large `|s|` is in `L^p` of the strip. -/
lemma memLp_of_vanish {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E) (hg : Continuous g)
    (R : ℝ) (hR : ∀ s t, R < |s| → g (s, t) = 0) : MemLp g p cylMeasure := by
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.Icc 0 1 with hK
  have hKc : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet K := measurableSet_Icc.prod measurableSet_Icc
  have hae : K.indicator g =ᵐ[cylMeasure] g := by
    unfold cylMeasure
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Ico) ?_
    rintro ⟨s, t⟩ ⟨-, ht⟩
    by_cases hx : (s, t) ∈ K
    · simp [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have : R < |s| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.Ico_subset_Icc_self ht⟩
      exact (hR s t this).symm
  refine (memLp_congr_ae hae).1 ((memLp_indicator_iff_restrict hKm).2 ?_)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := by
    refine isFiniteMeasure_restrict.2 (ne_of_lt (lt_of_le_of_lt ?_ (hKc.measure_lt_top (μ := (volume : Measure (ℝ × ℝ))))))
    exact Measure.le_iff'.1 Measure.restrict_le_self K
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C (ae_restrict_of_forall_mem hKm hC)

lemma partialS_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialS u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialS, hev.fderiv_eq]

lemma partialT_eq_zero {u : ℝ × ℝ → Vec n} (R : ℝ) (hR : ∀ s t, R < |s| → u (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : partialT u (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} := isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : u =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  simp [partialT, hev.fderiv_eq]

lemma IsTestSection.continuous {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Continuous u :=
  hu.1.continuous

lemma IsTestSection.continuous_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialS u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.continuous_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (partialT u) :=
  (hu.1.continuous_fderiv (by simp)).clm_apply continuous_const

lemma IsTestSection.memLp {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : MemLp u p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish u hu.continuous R hR

lemma IsTestSection.memLp_partialS {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialS u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialS R fun s t hs => partialS_eq_zero R hR hs

lemma IsTestSection.memLp_partialT {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    MemLp (partialT u) p cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  exact memLp_of_vanish _ hu.continuous_partialT R fun s t hs => partialT_eq_zero R hR hs

lemma IsTestSection.sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u - v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.sub hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    IsTestSection (u + v) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  obtain ⟨R₂, h₂⟩ := hv.2.2
  refine ⟨ContDiff.add hu.1 hv.1, fun s t => by simp [hu.2.1, hv.2.1], max R₁ R₂, fun s t hs => ?_⟩
  simp [h₁ s t (lt_of_le_of_lt (le_max_left _ _) hs), h₂ s t (lt_of_le_of_lt (le_max_right _ _) hs)]

lemma IsTestSection.smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    IsTestSection (c • u) := by
  obtain ⟨R₁, h₁⟩ := hu.2.2
  refine ⟨ContDiff.const_smul c hu.1, fun s t => by simp [hu.2.1], R₁, fun s t hs => ?_⟩
  simp [h₁ s t hs]

lemma isTestSection_zero : IsTestSection (0 : ℝ × ℝ → Vec n) :=
  ⟨contDiff_const, fun _ _ => rfl, 0, fun _ _ _ => rfl⟩

lemma partialS_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u + v) = partialS u + partialS v := by
  funext x
  simp only [partialS, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_add {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u + v) = partialT u + partialT v := by
  funext x
  simp only [partialT, Pi.add_apply]
  rw [fderiv_add ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialS (u - v) = partialS u - partialS v := by
  funext x
  simp only [partialS, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialT_sub {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    partialT (u - v) = partialT u - partialT v := by
  funext x
  simp only [partialT, Pi.sub_apply]
  rw [fderiv_sub ((hu.1.differentiable (by simp)) x) ((hv.1.differentiable (by simp)) x)]
  rfl

lemma partialS_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialS (c • u) = c • partialS u := by
  funext x
  simp only [partialS, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialT_smul {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (c : ℝ) :
    partialT (c • u) = c • partialT u := by
  funext x
  simp only [partialT, Pi.smul_apply]
  rw [fderiv_const_smul ((hu.1.differentiable (by simp)) x)]
  rfl

lemma partialS_zero : partialS (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialS]

lemma partialT_zero : partialT (0 : ℝ × ℝ → Vec n) = 0 := by
  funext x; simp [partialT]

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma cylMeasure_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma fderiv_eq_zero_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ × ℝ → E} (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) {s t : ℝ} (hs : R < |s|) :
    fderiv ℝ φ (s, t) = 0 := by
  have hU : IsOpen {x : ℝ × ℝ | R < |x.1|} :=
    isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
  have hev : φ =ᶠ[𝓝 (s, t)] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hs) fun x hx => hR x.1 x.2 hx
  rw [hev.fderiv_eq]; simp

lemma hasCompactSupport_of_vanish {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} (R : ℝ)
    (hR : ∀ s, R < |s| → f s = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) fun s hs =>
    hR s (not_le.1 fun h => hs (abs_le.1 h))

/-- `∫ ∂ₛφ = 0` over the cylinder for a `C¹` function vanishing for large `|s|`. -/
lemma integral_fderiv_s_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (R : ℝ)
    (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (1, 0) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (1, 0) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (1, 0)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, fderiv ℝ φ (s, t) (1, 0) = 0 := by
    intro t
    have hd : ∀ s, HasDerivAt (fun s => φ (s, t)) (fderiv ℝ φ (s, t) (1, 0)) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
        (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt s h1
    refine integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ ?_
    · exact (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => by
          simp [fderiv_eq_zero_of_vanish R hR hs])
    · exact (hφ.continuous.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hR s t hs)
  simp [h]

/-- `∫ ∂ₜφ = 0` over the cylinder for a `C¹` function, `1`-periodic in `t`, vanishing for large
`|s|`. -/
lemma integral_fderiv_t_eq_zero (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hper : ∀ s t, φ (s, t + 1) = φ (s, t)) (R : ℝ) (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∫ x, fderiv ℝ φ x (0, 1) ∂cylMeasure = 0 := by
  have hc : Continuous fun x => fderiv ℝ φ x (0, 1) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hI : Integrable (fun x => fderiv ℝ φ x (0, 1)) cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish _ hc R fun s t hs => by simp [fderiv_eq_zero_of_vanish R hR hs]
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, fderiv ℝ φ (s, t) (0, 1) = 0 := by
    intro s
    have hd : ∀ t, HasDerivAt (fun t => φ (s, t)) (fderiv ℝ φ (s, t) (0, 1)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
        (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
      exact ((hφ.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        ((hc.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma inner_toEuclideanLin (A : Mat n) (x y : Vec n) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma fderiv_matCLM_comp {v : ℝ × ℝ → Vec n} (A : Mat n) {x : ℝ × ℝ}
    (hv : DifferentiableAt ℝ v x) (h : ℝ × ℝ) :
    fderiv ℝ (fun y => Matrix.toEuclideanLin A (v y)) x h =
      Matrix.toEuclideanLin A (fderiv ℝ v x h) := by
  have : (fun y => Matrix.toEuclideanLin A (v y)) = (matCLM n A) ∘ v := rfl
  rw [this, fderiv_comp x (matCLM n A).differentiableAt hv, ContinuousLinearMap.fderiv]
  rfl

end

end CauchyRiemannIndex

/-! Small integration helpers on rectangles. -/

namespace GPoin

open Real MeasureTheory Set

section mean

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma sq_expand (h φ : α → ℝ) (hA : Integrable (fun s => h s ^ 2 * φ s) μ)
    (hB : Integrable (fun s => h s * φ s) μ) (hZ : Integrable φ μ) (c : ℝ) :
    ∫ s, (h s - c) ^ 2 * φ s ∂μ =
      ∫ s, h s ^ 2 * φ s ∂μ - 2 * c * ∫ s, h s * φ s ∂μ + c ^ 2 * ∫ s, φ s ∂μ := by
  have : (fun s => (h s - c) ^ 2 * φ s) =
      fun s => (h s ^ 2 * φ s - 2 * c * (h s * φ s)) + c ^ 2 * φ s := by funext s; ring
  rw [this, integral_add ?_ (hZ.const_mul _), integral_sub hA (hB.const_mul _),
    integral_const_mul, integral_const_mul]
  exact hA.sub (hB.const_mul _)

end mean

lemma restrict_prod (I J : Set ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (I ×ˢ J) = (volume.restrict I).prod (volume.restrict J) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

lemma integrable_box {F : ℝ × ℝ → ℝ} (hF : Continuous F) (a b c d : ℝ) :
    Integrable F ((volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))) := by
  rw [← restrict_prod]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

end GPoin

/-! Large antilinear perturbations, kernel bound: scalar calculus on the cylinder. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `∂ₛf` for a scalar function. -/
def pS (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ f x (1, 0)

/-- `∂ₜf` for a scalar function. -/
def pT (f : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := fderiv ℝ f x (0, 1)

/-- The first and second coordinates of `ℝ² = Vec 1`. -/
abbrev i₁ : Fin 1 ⊕ Fin 1 := Sum.inl 0
abbrev i₂ : Fin 1 ⊕ Fin 1 := Sum.inr 0

lemma hasDerivAt_pS {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    HasDerivAt (fun s => f (s, t)) (pS f (s, t)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact ((hf.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_pT {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    HasDerivAt (fun t => f (s, t)) (pT f (s, t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact ((hf.differentiable (by simp)) (s, t)).hasFDerivAt.comp_hasDerivAt t h1

lemma continuous_pS {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (pS f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

lemma continuous_pT {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (pT f) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

lemma contDiff_pS {f : ℝ × ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) : ContDiff ℝ k (pS f) :=
  (hf.fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

lemma contDiff_pT {f : ℝ × ℝ → ℝ} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) : ContDiff ℝ k (pT f) :=
  (hf.fderiv_right (m := k) (by norm_cast)).clm_apply contDiff_const

lemma pS_eq_zero_of_vanish {f : ℝ × ℝ → ℝ} (R : ℝ) (hR : ∀ s t, R < |s| → f (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : pS f (s, t) = 0 := by
  simp [pS, fderiv_eq_zero_of_vanish R hR hs]

lemma pT_eq_zero_of_vanish {f : ℝ × ℝ → ℝ} (R : ℝ) (hR : ∀ s t, R < |s| → f (s, t) = 0)
    {s t : ℝ} (hs : R < |s|) : pT f (s, t) = 0 := by
  simp [pT, fderiv_eq_zero_of_vanish R hR hs]

lemma pT_periodic {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (s t : ℝ) : pT f (s, t + 1) = pT f (s, t) := by
  have h1 := hasDerivAt_pT hf s (t + 1)
  have h2 : HasDerivAt (fun t => f (s, t + 1)) (pT f (s, t + 1)) t :=
    h1.comp_add_const t 1
  have h3 : (fun t => f (s, t + 1)) = fun t => f (s, t) := funext fun t => hper s t
  rw [h3] at h2
  exact h2.unique (hasDerivAt_pT hf s t)

lemma pS_periodic {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hper : ∀ s t, f (s, t + 1) = f (s, t))
    (s t : ℝ) : pS f (s, t + 1) = pS f (s, t) := by
  have h1 := hasDerivAt_pS hf s (t + 1)
  have h3 : (fun s => f (s, t + 1)) = fun s => f (s, t) := funext fun s => hper s t
  rw [h3] at h1
  exact h1.unique (hasDerivAt_pS hf s t)

/-- `∫ g = 0` over the cylinder when `g = ∂ₛF` slice-wise, with `g` continuous and both `g` and
`F` vanishing for large `|s|`. -/
lemma lak_integral_s_eq_zero (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hFR : ∀ s t, R < |s| → F (s, t) = 0)
    (hF : ∀ s t, HasDerivAt (fun s => F (s, t)) (g (s, t)) s) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod_symm _ hI]
  have h : ∀ t : ℝ, ∫ s, g (s, t) = 0 := by
    intro t
    have hFc : Continuous fun s => F (s, t) :=
      continuous_iff_continuousAt.2 fun s => (hF s t).continuousAt
    refine integral_eq_zero_of_hasDerivAt_of_integrable (fun s => hF s t) ?_ ?_
    · exact (hg.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_of_vanish R fun s hs => hgR s t hs)
    · exact hFc.integrable_of_hasCompactSupport (hasCompactSupport_of_vanish R fun s hs => hFR s t hs)
  simp [h]

/-- `∫ g = 0` over the cylinder when `g = ∂ₜF` slice-wise, `F` periodic in `t`. -/
lemma integral_t_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hFper : ∀ s t, F (s, t + 1) = F (s, t))
    (hF : ∀ s t, HasDerivAt (fun t => F (s, t)) (g (s, t)) t) :
    ∫ x, g x ∂cylMeasure = 0 := by
  have hI : Integrable g cylMeasure := by
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish g hg R hgR
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI]
  have h : ∀ s : ℝ, ∫ t in Set.Ico (0 : ℝ) 1, g (s, t) = 0 := by
    intro s
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF s t)
        ((hg.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)]
    have := hFper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma integrable_of_vanish {g : ℝ × ℝ → ℝ} (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) : Integrable g cylMeasure := by
  rw [← memLp_one_iff_integrable]
  exact memLp_of_vanish g hg R hgR

/-- Integration by parts in `s`. -/
lemma ibp_s (f Φ : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hΦ : ContDiff ℝ 1 Φ) (R : ℝ)
    (hR : ∀ s t, R < |s| → Φ (s, t) = 0) :
    ∫ x, f x * pS Φ x ∂cylMeasure = -∫ x, pS f x * Φ x ∂cylMeasure := by
  have hc1 : Continuous fun x => f x * pS Φ x := hf.continuous.mul (continuous_pS hΦ)
  have hc2 : Continuous fun x => pS f x * Φ x := (continuous_pS hf).mul hΦ.continuous
  have v1 : ∀ s t, R < |s| → f (s, t) * pS Φ (s, t) = 0 := fun s t hs => by
    rw [pS_eq_zero_of_vanish R hR hs, mul_zero]
  have v2 : ∀ s t, R < |s| → pS f (s, t) * Φ (s, t) = 0 := fun s t hs => by
    rw [hR s t hs, mul_zero]
  have h0 := lak_integral_s_eq_zero (fun x => f x * pS Φ x + pS f x * Φ x)
    (fun x => f x * Φ x) (hc1.add hc2) R (fun s t hs => by simp only [v1 s t hs, v2 s t hs]; ring)
    (fun s t hs => by simp only [hR s t hs, mul_zero])
    (fun s t => by
      have := (hasDerivAt_pS hf s t).mul (hasDerivAt_pS hΦ s t)
      exact this.congr_deriv (by ring))
  rw [integral_add (integrable_of_vanish hc1 R v1) (integrable_of_vanish hc2 R v2)] at h0
  linarith

/-- Integration by parts in `t`. -/
lemma ibp_t (f Φ : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hΦ : ContDiff ℝ 1 Φ)
    (hfper : ∀ s t, f (s, t + 1) = f (s, t)) (hΦper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) (R : ℝ)
    (hR : ∀ s t, R < |s| → Φ (s, t) = 0) :
    ∫ x, f x * pT Φ x ∂cylMeasure = -∫ x, pT f x * Φ x ∂cylMeasure := by
  have hc1 : Continuous fun x => f x * pT Φ x := hf.continuous.mul (continuous_pT hΦ)
  have hc2 : Continuous fun x => pT f x * Φ x := (continuous_pT hf).mul hΦ.continuous
  have v1 : ∀ s t, R < |s| → f (s, t) * pT Φ (s, t) = 0 := fun s t hs => by
    rw [pT_eq_zero_of_vanish R hR hs, mul_zero]
  have v2 : ∀ s t, R < |s| → pT f (s, t) * Φ (s, t) = 0 := fun s t hs => by
    rw [hR s t hs, mul_zero]
  have h0 := integral_t_eq_zero_of_hasDerivAt (fun x => f x * pT Φ x + pT f x * Φ x)
    (fun x => f x * Φ x) (hc1.add hc2) R (fun s t hs => by simp only [v1 s t hs, v2 s t hs]; ring)
    (fun s t => by simp only [hfper, hΦper])
    (fun s t => by
      have := (hasDerivAt_pT hf s t).mul (hasDerivAt_pT hΦ s t)
      exact this.congr_deriv (by ring))
  rw [integral_add (integrable_of_vanish hc1 R v1) (integrable_of_vanish hc2 R v2)] at h0
  linarith

/-! ### Components in `ℝ² = Vec 1` -/

lemma norm_sq_vec1 (v : Vec 1) : ‖v‖ ^ 2 = v i₁ ^ 2 + v i₂ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fintype.sum_sum_type]

lemma inner_vec1 (v w : Vec 1) : ⟪v, w⟫ = v i₁ * w i₁ + v i₂ * w i₂ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]
  ring

lemma J_apply₁ (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v i₁ = -v i₂ := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks]

lemma J_apply₂ (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v i₂ = v i₁ := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.fromBlocks]

lemma A_apply₁ (β : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat β) v i₁ = β.re * v i₁ + β.im * v i₂ := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks]

lemma A_apply₂ (β : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat β) v i₂ = β.im * v i₁ - β.re * v i₂ := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Matrix.fromBlocks]
  ring

lemma smulA_apply₁ (σ : ℝ) (β : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (σ • antilinearMat β) v i₁ = σ * (β.re * v i₁ + β.im * v i₂) := by
  rw [map_smul, LinearMap.smul_apply, PiLp.smul_apply, A_apply₁, smul_eq_mul]

lemma smulA_apply₂ (σ : ℝ) (β : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (σ • antilinearMat β) v i₂ = σ * (β.im * v i₁ - β.re * v i₂) := by
  rw [map_smul, LinearMap.smul_apply, PiLp.smul_apply, A_apply₂, smul_eq_mul]

/-- The coordinate function `x ↦ u x i`. -/
def coord (u : ℝ × ℝ → Vec 1) (i : Fin 1 ⊕ Fin 1) : ℝ × ℝ → ℝ := fun x => u x i

lemma coord_contDiff {u : ℝ × ℝ → Vec 1} {k : ℕ∞} (hu : ContDiff ℝ k u) (i) :
    ContDiff ℝ k (coord u i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hu

lemma partialS_coord {u : ℝ × ℝ → Vec 1} (hu : Differentiable ℝ u) (i) (x : ℝ × ℝ) :
    partialS u x i = pS (coord u i) x := by
  have : coord u i = (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ u := rfl
  rw [pS, this, fderiv_comp x (ContinuousLinearMap.differentiableAt _) (hu x),
    ContinuousLinearMap.fderiv]
  rfl

lemma partialT_coord {u : ℝ × ℝ → Vec 1} (hu : Differentiable ℝ u) (i) (x : ℝ × ℝ) :
    partialT u x i = pT (coord u i) x := by
  have : coord u i = (EuclideanSpace.proj (𝕜 := ℝ) i) ∘ u := rfl
  rw [pT, this, fderiv_comp x (ContinuousLinearMap.differentiableAt _) (hu x),
    ContinuousLinearMap.fderiv]
  rfl

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the scalar identities on the cylinder. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma pS_eq_of_hasDerivAt {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h : ∀ s t, HasDerivAt (fun s => f (s, t)) (g (s, t)) s) (x : ℝ × ℝ) : pS f x = g x :=
  (hasDerivAt_pS hf x.1 x.2).unique (h x.1 x.2)

lemma pT_eq_of_hasDerivAt {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (h : ∀ s t, HasDerivAt (fun t => f (s, t)) (g (s, t)) t) (x : ℝ × ℝ) : pT f x = g x :=
  (hasDerivAt_pT hf x.1 x.2).unique (h x.1 x.2)

lemma pS_mul {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : ℝ × ℝ) :
    pS (fun y => f y * g y) x = pS f x * g x + f x * pS g x :=
  pS_eq_of_hasDerivAt (g := fun x => pS f x * g x + f x * pS g x) (hf.mul hg) (fun s t => (hasDerivAt_pS hf s t).mul (hasDerivAt_pS hg s t)) x

lemma pT_mul {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : ℝ × ℝ) :
    pT (fun y => f y * g y) x = pT f x * g x + f x * pT g x :=
  pT_eq_of_hasDerivAt (g := fun x => pT f x * g x + f x * pT g x) (hf.mul hg) (fun s t => (hasDerivAt_pT hf s t).mul (hasDerivAt_pT hg s t)) x

/-- Functions vanishing for `|s| > R`. -/
def VanS (R : ℝ) (f : ℝ × ℝ → ℝ) : Prop := ∀ s t, R < |s| → f (s, t) = 0

/-- Functions `1`-periodic in `t`. -/
def PerT (f : ℝ × ℝ → ℝ) : Prop := ∀ s t, f (s, t + 1) = f (s, t)

lemma VanS.mul_left {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : VanS R f) (g : ℝ × ℝ → ℝ) :
    VanS R fun x => g x * f x := fun s t hs => by simp [hf s t hs]

lemma VanS.mul_right {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : VanS R f) (g : ℝ × ℝ → ℝ) :
    VanS R fun x => f x * g x := fun s t hs => by simp [hf s t hs]

lemma VanS.pS {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : VanS R f) : VanS R (pS f) := fun s t hs =>
  pS_eq_zero_of_vanish R hf hs

lemma VanS.pT {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : VanS R f) : VanS R (pT f) := fun s t hs =>
  pT_eq_zero_of_vanish R hf hs

lemma VanS.integrable {R : ℝ} {f : ℝ × ℝ → ℝ} (hf : VanS R f) (hc : Continuous f) :
    Integrable f cylMeasure := integrable_of_vanish hc R hf

/-- `∫ (∂ₛW + σ f W)² = ∫ (∂ₛW)² + σ² ∫ f² W² - σ ∫ (∂ₛf) W²`. -/
lemma osc_s (W f : ℝ × ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 1 f) (R : ℝ)
    (hR : VanS R W) (σ : ℝ) :
    ∫ x, (pS W x + σ * f x * W x) ^ 2 ∂cylMeasure =
      ∫ x, pS W x ^ 2 ∂cylMeasure + σ ^ 2 * ∫ x, f x ^ 2 * W x ^ 2 ∂cylMeasure -
        σ * ∫ x, pS f x * W x ^ 2 ∂cylMeasure := by
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have hWd : Differentiable ℝ W := hW1.differentiable (by simp)
  have hsq : ContDiff ℝ 1 fun x => W x * W x := hW1.mul hW1
  have hsqR : VanS R fun x => W x * W x := hR.mul_left W
  have hibp := ibp_s f (fun x => W x * W x) hf hsq R hsqR
  have hps : ∀ x, pS (fun x => W x * W x) x = 2 * (W x * pS W x) := fun x => by
    rw [pS_mul hW1 hW1]; ring
  simp only [hps] at hibp
  have cW := hW1.continuous
  have cWs := continuous_pS hW1
  have cf := hf.continuous
  have cfs := continuous_pS hf
  have i1 : Integrable (fun x => pS W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR.pS s t hs]) (by fun_prop)
  have i2 : Integrable (fun x => f x ^ 2 * W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have i3 : Integrable (fun x => f x * (2 * (W x * pS W x))) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have i4 : Integrable (fun x => pS f x * W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have e : (fun x => (pS W x + σ * f x * W x) ^ 2) =
      fun x => pS W x ^ 2 + σ ^ 2 * (f x ^ 2 * W x ^ 2) + σ * (f x * (2 * (W x * pS W x))) := by
    funext x; ring
  rw [e, integral_add ?_ (i3.const_mul _), integral_add i1 (i2.const_mul _),
    integral_const_mul, integral_const_mul, hibp]
  rotate_left
  · exact i1.add (i2.const_mul (σ ^ 2))
  have e2 : (fun x => pS f x * (W x * W x)) = fun x => pS f x * W x ^ 2 := by funext x; ring
  rw [e2]
  ring

/-- `∫ (∂ₜW + σ f W)² = ∫ (∂ₜW)² + σ² ∫ f² W² - σ ∫ (∂ₜf) W²`. -/
lemma osc_t (W f : ℝ × ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 1 f) (R : ℝ)
    (hR : VanS R W) (hWp : PerT W) (hfp : PerT f) (σ : ℝ) :
    ∫ x, (pT W x + σ * f x * W x) ^ 2 ∂cylMeasure =
      ∫ x, pT W x ^ 2 ∂cylMeasure + σ ^ 2 * ∫ x, f x ^ 2 * W x ^ 2 ∂cylMeasure -
        σ * ∫ x, pT f x * W x ^ 2 ∂cylMeasure := by
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have hWd : Differentiable ℝ W := hW1.differentiable (by simp)
  have hsq : ContDiff ℝ 1 fun x => W x * W x := hW1.mul hW1
  have hsqR : VanS R fun x => W x * W x := hR.mul_left W
  have hibp := ibp_t f (fun x => W x * W x) hf hsq hfp (fun s t => by simp only [hWp s t]) R hsqR
  have hps : ∀ x, pT (fun x => W x * W x) x = 2 * (W x * pT W x) := fun x => by
    rw [pT_mul hW1 hW1]; ring
  simp only [hps] at hibp
  have cW := hW1.continuous
  have cWs := continuous_pT hW1
  have cf := hf.continuous
  have cfs := continuous_pT hf
  have i1 : Integrable (fun x => pT W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR.pT s t hs]) (by fun_prop)
  have i2 : Integrable (fun x => f x ^ 2 * W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have i3 : Integrable (fun x => f x * (2 * (W x * pT W x))) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have i4 : Integrable (fun x => pT f x * W x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [hR s t hs]) (by fun_prop)
  have e : (fun x => (pT W x + σ * f x * W x) ^ 2) =
      fun x => pT W x ^ 2 + σ ^ 2 * (f x ^ 2 * W x ^ 2) + σ * (f x * (2 * (W x * pT W x))) := by
    funext x; ring
  rw [e, integral_add ?_ (i3.const_mul _), integral_add i1 (i2.const_mul _),
    integral_const_mul, integral_const_mul, hibp]
  rotate_left
  · exact i1.add (i2.const_mul (σ ^ 2))
  have e2 : (fun x => pT f x * (W x * W x)) = fun x => pT f x * W x ^ 2 := by funext x; ring
  rw [e2]
  ring

/-- The cross term of `‖(∂ₛ + J₀∂ₜ)u + σ A(β) u‖²`, integrated by parts. -/
lemma cross_ibp (X Y br bi : ℝ × ℝ → ℝ) (hX : ContDiff ℝ 2 X) (hY : ContDiff ℝ 2 Y)
    (hr : ContDiff ℝ 1 br) (hi : ContDiff ℝ 1 bi) (R : ℝ) (hXR : VanS R X) (hYR : VanS R Y)
    (hXp : PerT X) (hYp : PerT Y) (hrp : PerT br) (hip : PerT bi) :
    ∫ x, ((pS X x - pT Y x) * (br x * X x + bi x * Y x) +
        (pS Y x + pT X x) * (bi x * X x - br x * Y x)) ∂cylMeasure =
      -(1 / 2) * ∫ x, (pS br x + pT bi x) * (X x ^ 2 - Y x ^ 2) ∂cylMeasure -
        ∫ x, (pS bi x - pT br x) * (X x * Y x) ∂cylMeasure := by
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  have hY1 : ContDiff ℝ 1 Y := hY.of_le (by norm_num)
  have hXd : Differentiable ℝ X := hX1.differentiable (by simp)
  have hYd : Differentiable ℝ Y := hY1.differentiable (by simp)
  set Φ₁ : ℝ × ℝ → ℝ := fun x => X x * X x - Y x * Y x with hΦ₁
  set Φ₂ : ℝ × ℝ → ℝ := fun x => X x * Y x with hΦ₂
  have c1 : ContDiff ℝ 1 Φ₁ := (hX1.mul hX1).sub (hY1.mul hY1)
  have c2 : ContDiff ℝ 1 Φ₂ := hX1.mul hY1
  have v1 : VanS R Φ₁ := fun s t hs => by simp [hΦ₁, hXR s t hs, hYR s t hs]
  have v2 : VanS R Φ₂ := fun s t hs => by simp [hΦ₂, hXR s t hs]
  have p1 : ∀ s t, Φ₁ (s, t + 1) = Φ₁ (s, t) := fun s t => by simp only [hΦ₁, hXp s t, hYp s t]
  have p2 : ∀ s t, Φ₂ (s, t + 1) = Φ₂ (s, t) := fun s t => by simp only [hΦ₂, hXp s t, hYp s t]
  have dS1 : ∀ x, pS Φ₁ x = 2 * (X x * pS X x - Y x * pS Y x) := fun x =>
    pS_eq_of_hasDerivAt (g := fun x => 2 * (X x * pS X x - Y x * pS Y x)) c1 (fun s t => (((hasDerivAt_pS hX1 s t).mul (hasDerivAt_pS hX1 s t)).sub
      ((hasDerivAt_pS hY1 s t).mul (hasDerivAt_pS hY1 s t))).congr_deriv (by ring)) x
  have dT1 : ∀ x, pT Φ₁ x = 2 * (X x * pT X x - Y x * pT Y x) := fun x =>
    pT_eq_of_hasDerivAt (g := fun x => 2 * (X x * pT X x - Y x * pT Y x)) c1 (fun s t => (((hasDerivAt_pT hX1 s t).mul (hasDerivAt_pT hX1 s t)).sub
      ((hasDerivAt_pT hY1 s t).mul (hasDerivAt_pT hY1 s t))).congr_deriv (by ring)) x
  have dS2 : ∀ x, pS Φ₂ x = pS X x * Y x + X x * pS Y x := fun x => pS_mul hX1 hY1 x
  have dT2 : ∀ x, pT Φ₂ x = pT X x * Y x + X x * pT Y x := fun x => pT_mul hX1 hY1 x
  have I1 := ibp_s br Φ₁ hr c1 R v1
  have I2 := ibp_s bi Φ₂ hi c2 R v2
  have I3 := ibp_t bi Φ₁ hi c1 hip p1 R v1
  have I4 := ibp_t br Φ₂ hr c2 hrp p2 R v2
  have cX := hX1.continuous
  have cY := hY1.continuous
  have cXs := continuous_pS hX1
  have cXt := continuous_pT hX1
  have cYs := continuous_pS hY1
  have cYt := continuous_pT hY1
  have cr := hr.continuous
  have ci := hi.continuous
  have crs := continuous_pS hr
  have crt := continuous_pT hr
  have cis := continuous_pS hi
  have cit := continuous_pT hi
  have j1 : Integrable (fun x => br x * pS Φ₁ x) cylMeasure :=
    VanS.integrable (v1.pS.mul_left br) (cr.mul (continuous_pS c1))
  have j2 : Integrable (fun x => bi x * pS Φ₂ x) cylMeasure :=
    VanS.integrable (v2.pS.mul_left bi) (ci.mul (continuous_pS c2))
  have j3 : Integrable (fun x => bi x * pT Φ₁ x) cylMeasure :=
    VanS.integrable (v1.pT.mul_left bi) (ci.mul (continuous_pT c1))
  have j4 : Integrable (fun x => br x * pT Φ₂ x) cylMeasure :=
    VanS.integrable (v2.pT.mul_left br) (cr.mul (continuous_pT c2))
  have k1 : Integrable (fun x => pS br x * Φ₁ x) cylMeasure :=
    VanS.integrable (v1.mul_left _) (crs.mul c1.continuous)
  have k2 : Integrable (fun x => pS bi x * Φ₂ x) cylMeasure :=
    VanS.integrable (v2.mul_left _) (cis.mul c2.continuous)
  have k3 : Integrable (fun x => pT bi x * Φ₁ x) cylMeasure :=
    VanS.integrable (v1.mul_left _) (cit.mul c1.continuous)
  have k4 : Integrable (fun x => pT br x * Φ₂ x) cylMeasure :=
    VanS.integrable (v2.mul_left _) (crt.mul c2.continuous)
  have e : (fun x => (pS X x - pT Y x) * (br x * X x + bi x * Y x) +
        (pS Y x + pT X x) * (bi x * X x - br x * Y x)) =
      fun x => (1 / 2) * (br x * pS Φ₁ x) + bi x * pS Φ₂ x + (1 / 2) * (bi x * pT Φ₁ x) -
        br x * pT Φ₂ x := by
    funext x; rw [dS1, dT1, dS2, dT2]; ring
  rw [e, integral_sub ?_ j4, integral_add ?_ (j3.const_mul _), integral_add (j1.const_mul _) j2,
    integral_const_mul, integral_const_mul, I1, I2, I3, I4]
  rotate_left
  · exact (j1.const_mul (1 / 2)).add j2
  · exact ((j1.const_mul (1 / 2)).add j2).add (j3.const_mul (1 / 2))
  have e1 : (fun x => (pS br x + pT bi x) * (X x ^ 2 - Y x ^ 2)) =
      fun x => pS br x * Φ₁ x + pT bi x * Φ₁ x := by funext x; simp only [hΦ₁]; ring
  have e2 : (fun x => (pS bi x - pT br x) * (X x * Y x)) =
      fun x => pS bi x * Φ₂ x - pT br x * Φ₂ x := by funext x; simp only [hΦ₂]; ring
  rw [e1, e2, integral_add k1 k3, integral_sub k2 k4]
  ring

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: expansion of `‖D_σ u‖²` for test sections. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma IsTestSection.vanS {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) :
    ∃ R, ∀ i, VanS R (coord U i) := by
  obtain ⟨R, hR⟩ := hU.2.2
  exact ⟨R, fun i s t hs => by simp [coord, hR s t hs]⟩

lemma IsTestSection.perT {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) (i) :
    PerT (coord U i) := fun s t => by simp [coord, hU.2.1 s t]

lemma IsTestSection.coord_smooth {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) (i) {k : ℕ} :
    ContDiff ℝ k (coord U i) :=
  (coord_contDiff hU.1 i).of_le (by exact_mod_cast le_top)

lemma re_contDiff {β : ℝ × ℝ → ℂ} {k : ℕ∞} (hβ : ContDiff ℝ k β) :
    ContDiff ℝ k fun x => (β x).re := Complex.reCLM.contDiff.comp hβ

lemma im_contDiff {β : ℝ × ℝ → ℂ} {k : ℕ∞} (hβ : ContDiff ℝ k β) :
    ContDiff ℝ k fun x => (β x).im := Complex.imCLM.contDiff.comp hβ

lemma norm_sq_coord (U : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) :
    ‖U x‖ ^ 2 = coord U i₁ x ^ 2 + coord U i₂ x ^ 2 := norm_sq_vec1 _

/-- Pointwise components of `D_σ u = ∂ₛu + J₀∂ₜu + σ A(β) u`. -/
lemma crOp_sq (σ : ℝ) (β : ℝ × ℝ → ℂ) {U : ℝ × ℝ → Vec 1} (hU : Differentiable ℝ U)
    (x : ℝ × ℝ) :
    ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 =
      (pS (coord U i₁) x - pT (coord U i₂) x +
          σ * ((β x).re * coord U i₁ x + (β x).im * coord U i₂ x)) ^ 2 +
        (pS (coord U i₂) x + pT (coord U i₁) x +
          σ * ((β x).im * coord U i₁ x - (β x).re * coord U i₂ x)) ^ 2 := by
  rw [norm_sq_vec1]
  simp only [crOp, PiLp.add_apply, J_apply₁, J_apply₂, smulA_apply₁, smulA_apply₂,
    partialS_coord hU, partialT_coord hU]
  simp only [coord]
  ring

/-- `∫ ‖∂ₛu + J₀∂ₜu‖² = ∫ ‖∇u‖²` in coordinates. -/
lemma dbar_energy {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) :
    ∫ x, ((pS (coord U i₁) x - pT (coord U i₂) x) ^ 2 +
        (pS (coord U i₂) x + pT (coord U i₁) x) ^ 2) ∂cylMeasure =
      ∫ x, (pS (coord U i₁) x ^ 2 + pT (coord U i₁) x ^ 2 + pS (coord U i₂) x ^ 2 +
        pT (coord U i₂) x ^ 2) ∂cylMeasure := by
  have hd : Differentiable ℝ U := hU.1.differentiable (by simp)
  have h := crOp_energy_identity 1 (fun _ : ℝ => (0 : Mat 1)) continuous_const
    (fun _ => Matrix.isSymm_zero) U hU
  have e1 : ∀ x, ‖crOp (fun x : ℝ × ℝ => (fun _ : ℝ => (0 : Mat 1)) x.2) U x‖ ^ 2 =
      (pS (coord U i₁) x - pT (coord U i₂) x) ^ 2 + (pS (coord U i₂) x + pT (coord U i₁) x) ^ 2 := by
    intro x
    rw [norm_sq_vec1]
    simp only [crOp, PiLp.add_apply, J_apply₁, J_apply₂, map_zero, LinearMap.zero_apply,
      PiLp.zero_apply, partialS_coord hd, partialT_coord hd]
    ring
  have e2 : ∀ x, ‖partialS U x‖ ^ 2 = pS (coord U i₁) x ^ 2 + pS (coord U i₂) x ^ 2 := by
    intro x; rw [norm_sq_vec1, partialS_coord hd, partialS_coord hd]
  have e3 : ∀ x, ‖Matrix.toEuclideanLin (J₀ 1) (partialT U x) +
      Matrix.toEuclideanLin ((fun _ : ℝ => (0 : Mat 1)) x.2) (U x)‖ ^ 2 =
      pT (coord U i₁) x ^ 2 + pT (coord U i₂) x ^ 2 := by
    intro x
    rw [norm_sq_vec1]
    simp only [PiLp.add_apply, J_apply₁, J_apply₂, map_zero, LinearMap.zero_apply,
      PiLp.zero_apply, partialT_coord hd]
    ring
  simp only [e1, e2, e3] at h
  rw [h, ← integral_add]
  · congr 1; funext x; ring
  · obtain ⟨R, hR⟩ := hU.vanS
    have c1 := continuous_pS (hU.coord_smooth i₁ (k := 1))
    have c2 := continuous_pS (hU.coord_smooth i₂ (k := 1))
    exact VanS.integrable (R := R) (fun s t hs => by simp [(hR i₁).pS s t hs, (hR i₂).pS s t hs])
      (by fun_prop)
  · obtain ⟨R, hR⟩ := hU.vanS
    have c1 := continuous_pT (hU.coord_smooth i₁ (k := 1))
    have c2 := continuous_pT (hU.coord_smooth i₂ (k := 1))
    exact VanS.integrable (R := R) (fun s t hs => by simp [(hR i₁).pT s t hs, (hR i₂).pT s t hs])
      (by fun_prop)

/-- Expansion of `∫ ‖D_σ u‖²` for a test section `u`. -/
theorem D0_expand (σ : ℝ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) :
    ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure =
      ∫ x, (pS (coord U i₁) x ^ 2 + pT (coord U i₁) x ^ 2 + pS (coord U i₂) x ^ 2 +
        pT (coord U i₂) x ^ 2) ∂cylMeasure +
      σ ^ 2 * ∫ x, ((β x).re ^ 2 + (β x).im ^ 2) * (coord U i₁ x ^ 2 + coord U i₂ x ^ 2)
        ∂cylMeasure -
      σ * ∫ x, (pS (fun y => (β y).re) x + pT (fun y => (β y).im) x) *
        (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure -
      2 * σ * ∫ x, (pS (fun y => (β y).im) x - pT (fun y => (β y).re) x) *
        (coord U i₁ x * coord U i₂ x) ∂cylMeasure := by
  have hd : Differentiable ℝ U := hU.1.differentiable (by simp)
  obtain ⟨R, hR⟩ := hU.vanS
  have hen := dbar_energy hU
  simp only [crOp_sq σ β hd]
  have cX2' : ContDiff ℝ 2 (coord U i₁) := hU.coord_smooth i₁
  have cY2' : ContDiff ℝ 2 (coord U i₂) := hU.coord_smooth i₂
  have pX := hU.perT i₁
  have pY := hU.perT i₂
  have vX := hR i₁
  have vY := hR i₂
  have cr : ContDiff ℝ 1 fun y => (β y).re := re_contDiff hβ
  have ci : ContDiff ℝ 1 fun y => (β y).im := im_contDiff hβ
  have prp : PerT fun y => (β y).re := fun s t => by simp [hβper s t]
  have pip : PerT fun y => (β y).im := fun s t => by simp [hβper s t]
  set X := coord U i₁ with hX
  set Y := coord U i₂ with hY
  set br : ℝ × ℝ → ℝ := fun y => (β y).re with hbr
  set bi : ℝ × ℝ → ℝ := fun y => (β y).im with hbi
  clear_value X Y br bi
  have ebr : ∀ x, (β x).re = br x := fun x => by rw [hbr]
  have ebi : ∀ x, (β x).im = bi x := fun x => by rw [hbi]
  simp only [ebr, ebi]
  have cX2 : ContDiff ℝ 2 X := cX2'
  have cY2 : ContDiff ℝ 2 Y := cY2'
  have cX1 : ContDiff ℝ 1 X := cX2'.of_le (by norm_num)
  have cY1 : ContDiff ℝ 1 Y := cY2'.of_le (by norm_num)
  have hcross := cross_ibp X Y br bi cX2 cY2 cr ci R vX vY pX pY prp pip
  have cXc := cX1.continuous
  have cYc := cY1.continuous
  have cXs := continuous_pS cX1
  have cXt := continuous_pT cX1
  have cYs := continuous_pS cY1
  have cYt := continuous_pT cY1
  have crc := cr.continuous
  have cic := ci.continuous
  have iA : Integrable (fun x => (pS X x - pT Y x) ^ 2 + (pS Y x + pT X x) ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by
      simp [vX.pS s t hs, vX.pT s t hs, vY.pS s t hs, vY.pT s t hs]) (by fun_prop)
  have iB : Integrable (fun x => (br x ^ 2 + bi x ^ 2) * (X x ^ 2 + Y x ^ 2)) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs, vY s t hs]) (by fun_prop)
  have iC : Integrable (fun x => (pS X x - pT Y x) * (br x * X x + bi x * Y x) +
      (pS Y x + pT X x) * (bi x * X x - br x * Y x)) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs, vY s t hs]) (by fun_prop)
  have e : (fun x => (pS X x - pT Y x + σ * (br x * X x + bi x * Y x)) ^ 2 +
      (pS Y x + pT X x + σ * (bi x * X x - br x * Y x)) ^ 2) =
      fun x => ((pS X x - pT Y x) ^ 2 + (pS Y x + pT X x) ^ 2) +
        σ ^ 2 * ((br x ^ 2 + bi x ^ 2) * (X x ^ 2 + Y x ^ 2)) +
        (2 * σ) * ((pS X x - pT Y x) * (br x * X x + bi x * Y x) +
          (pS Y x + pT X x) * (bi x * X x - br x * Y x)) := by
    funext x; ring
  rw [e, integral_add ?_ (iC.const_mul _), integral_add iA (iB.const_mul _), integral_const_mul,
    integral_const_mul, hcross, hen]
  · ring
  · exact iA.add (iB.const_mul (σ ^ 2))

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the global and the local lower bounds. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma integral_add4 {f₁ f₂ f₃ f₄ : ℝ × ℝ → ℝ} (h₁ : Integrable f₁ cylMeasure)
    (h₂ : Integrable f₂ cylMeasure) (h₃ : Integrable f₃ cylMeasure) (h₄ : Integrable f₄ cylMeasure) :
    ∫ x, (f₁ x + f₂ x + f₃ x + f₄ x) ∂cylMeasure =
      ∫ x, f₁ x ∂cylMeasure + ∫ x, f₂ x ∂cylMeasure + ∫ x, f₃ x ∂cylMeasure +
        ∫ x, f₄ x ∂cylMeasure := by
  rw [integral_add ?_ h₄, integral_add ?_ h₃, integral_add h₁ h₂]
  · exact h₁.add h₂
  · exact (h₁.add h₂).add h₃

lemma pS_re {β : ℝ × ℝ → ℂ} (hβ : Differentiable ℝ β) (x : ℝ × ℝ) :
    pS (fun y => (β y).re) x = (fderiv ℝ β x (1, 0)).re := by
  have : (fun y => (β y).re) = Complex.reCLM ∘ β := rfl
  rw [pS, this, fderiv_comp x Complex.reCLM.differentiableAt (hβ x), ContinuousLinearMap.fderiv]
  rfl

lemma pT_re {β : ℝ × ℝ → ℂ} (hβ : Differentiable ℝ β) (x : ℝ × ℝ) :
    pT (fun y => (β y).re) x = (fderiv ℝ β x (0, 1)).re := by
  have : (fun y => (β y).re) = Complex.reCLM ∘ β := rfl
  rw [pT, this, fderiv_comp x Complex.reCLM.differentiableAt (hβ x), ContinuousLinearMap.fderiv]
  rfl

lemma pS_im {β : ℝ × ℝ → ℂ} (hβ : Differentiable ℝ β) (x : ℝ × ℝ) :
    pS (fun y => (β y).im) x = (fderiv ℝ β x (1, 0)).im := by
  have : (fun y => (β y).im) = Complex.imCLM ∘ β := rfl
  rw [pS, this, fderiv_comp x Complex.imCLM.differentiableAt (hβ x), ContinuousLinearMap.fderiv]
  rfl

lemma pT_im {β : ℝ × ℝ → ℂ} (hβ : Differentiable ℝ β) (x : ℝ × ℝ) :
    pT (fun y => (β y).im) x = (fderiv ℝ β x (0, 1)).im := by
  have : (fun y => (β y).im) = Complex.imCLM ∘ β := rfl
  rw [pT, this, fderiv_comp x Complex.imCLM.differentiableAt (hβ x), ContinuousLinearMap.fderiv]
  rfl

lemma fderiv_apply_le {β : ℝ × ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C) (x : ℝ × ℝ)
    (v : ℝ × ℝ) (hv : ‖v‖ ≤ 1) : ‖fderiv ℝ β x v‖ ≤ C := by
  calc ‖fderiv ℝ β x v‖ ≤ ‖fderiv ℝ β x‖ * ‖v‖ := (fderiv ℝ β x).le_opNorm v
    _ ≤ ‖fderiv ℝ β x‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ ≤ C := by rw [mul_one]; exact hC x

lemma norm_e1 : ‖((1 : ℝ), (0 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]
lemma norm_e2 : ‖((0 : ℝ), (1 : ℝ))‖ ≤ 1 := by simp [Prod.norm_def]

/-- Global lower bound: `∫ ‖D_σ u‖² ≥ σ² ∫ |β|² |u|² - 4 C σ ∫ |u|²`. -/
theorem D0_global (σ : ℝ) (hσ : 0 ≤ σ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) :
    σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖U x‖ ^ 2 ∂cylMeasure - 4 * C * σ * ∫ x, ‖U x‖ ^ 2 ∂cylMeasure ≤
      ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure := by
  have hβd : Differentiable ℝ β := hβ.differentiable (by simp)
  rw [D0_expand σ hβ hβper hU]
  obtain ⟨R, hR⟩ := hU.vanS
  have vX := hR i₁
  have vY := hR i₂
  have cX1 : ContDiff ℝ 1 (coord U i₁) := hU.coord_smooth i₁
  have cY1 : ContDiff ℝ 1 (coord U i₂) := hU.coord_smooth i₂
  have cr : ContDiff ℝ 1 fun y => (β y).re := re_contDiff hβ
  have ci : ContDiff ℝ 1 fun y => (β y).im := im_contDiff hβ
  set X := coord U i₁ with hX
  set Y := coord U i₂ with hY
  set br : ℝ × ℝ → ℝ := fun y => (β y).re with hbr
  set bi : ℝ × ℝ → ℝ := fun y => (β y).im with hbi
  have ebr : ∀ x, (β x).re = br x := fun x => by rw [hbr]
  have ebi : ∀ x, (β x).im = bi x := fun x => by rw [hbi]
  have hb1 : ∀ x, |pS br x| ≤ C := fun x => by
    rw [hbr, pS_re hβd]; exact (Complex.abs_re_le_norm _).trans (fderiv_apply_le hC x _ norm_e1)
  have hb2 : ∀ x, |pT br x| ≤ C := fun x => by
    rw [hbr, pT_re hβd]; exact (Complex.abs_re_le_norm _).trans (fderiv_apply_le hC x _ norm_e2)
  have hb3 : ∀ x, |pS bi x| ≤ C := fun x => by
    rw [hbi, pS_im hβd]; exact (Complex.abs_im_le_norm _).trans (fderiv_apply_le hC x _ norm_e1)
  have hb4 : ∀ x, |pT bi x| ≤ C := fun x => by
    rw [hbi, pT_im hβd]; exact (Complex.abs_im_le_norm _).trans (fderiv_apply_le hC x _ norm_e2)
  clear_value X Y br bi
  have nβ : ∀ x, ‖β x‖ ^ 2 = br x ^ 2 + bi x ^ 2 := fun x => by
    rw [← ebr, ← ebi, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have nU : ∀ x, ‖U x‖ ^ 2 = X x ^ 2 + Y x ^ 2 := fun x => by rw [hX, hY]; exact norm_sq_coord U x
  simp only [nβ, nU, ebr, ebi]
  have cXc := cX1.continuous
  have cYc := cY1.continuous
  have cXs := continuous_pS cX1
  have cXt := continuous_pT cX1
  have cYs := continuous_pS cY1
  have cYt := continuous_pT cY1
  have crs := continuous_pS cr
  have crt := continuous_pT cr
  have cis := continuous_pS ci
  have cit := continuous_pT ci
  have crc : Continuous br := cr.continuous
  have cic : Continuous bi := ci.continuous
  have iE : Integrable (fun x => pS X x ^ 2 + pT X x ^ 2 + pS Y x ^ 2 + pT Y x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by
      simp [vX.pS s t hs, vX.pT s t hs, vY.pS s t hs, vY.pT s t hs]) (by fun_prop)
  have iU : Integrable (fun x => X x ^ 2 + Y x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs, vY s t hs]) (by fun_prop)
  have i1 : Integrable (fun x => (pS br x + pT bi x) * (X x ^ 2 - Y x ^ 2)) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs, vY s t hs]) (by fun_prop)
  have i2 : Integrable (fun x => (pS bi x - pT br x) * (X x * Y x)) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs, vY s t hs]) (by fun_prop)
  have hE : 0 ≤ ∫ x, (pS X x ^ 2 + pT X x ^ 2 + pS Y x ^ 2 + pT Y x ^ 2) ∂cylMeasure :=
    integral_nonneg fun x => by positivity
  have h1 : ∫ x, (pS br x + pT bi x) * (X x ^ 2 - Y x ^ 2) ∂cylMeasure ≤
      ∫ x, 2 * C * (X x ^ 2 + Y x ^ 2) ∂cylMeasure := by
    refine integral_mono i1 (iU.const_mul _) fun x => ?_
    have a1 := hb1 x
    have a2 := hb4 x
    have : |(pS br x + pT bi x) * (X x ^ 2 - Y x ^ 2)| ≤ 2 * C * (X x ^ 2 + Y x ^ 2) := by
      rw [abs_mul]
      have e1 : |pS br x + pT bi x| ≤ 2 * C := (abs_add_le _ _).trans (by linarith)
      have e2 : |X x ^ 2 - Y x ^ 2| ≤ X x ^ 2 + Y x ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X x), sq_nonneg (Y x)]
      calc |pS br x + pT bi x| * |X x ^ 2 - Y x ^ 2| ≤ (2 * C) * (X x ^ 2 + Y x ^ 2) :=
            mul_le_mul e1 e2 (abs_nonneg _) (by linarith [abs_nonneg (pS br x)])
        _ = _ := by ring
    exact (le_abs_self _).trans this
  have h2 : ∫ x, (pS bi x - pT br x) * (X x * Y x) ∂cylMeasure ≤
      ∫ x, C * (X x ^ 2 + Y x ^ 2) ∂cylMeasure := by
    refine integral_mono i2 (iU.const_mul _) fun x => ?_
    have a1 := hb3 x
    have a2 := hb2 x
    have : |(pS bi x - pT br x) * (X x * Y x)| ≤ C * (X x ^ 2 + Y x ^ 2) := by
      rw [abs_mul]
      have e1 : |pS bi x - pT br x| ≤ 2 * C := (abs_sub _ _).trans (by linarith)
      have e2 : |X x * Y x| ≤ (X x ^ 2 + Y x ^ 2) / 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (X x - Y x), sq_nonneg (X x + Y x)]
      calc |pS bi x - pT br x| * |X x * Y x| ≤ (2 * C) * ((X x ^ 2 + Y x ^ 2) / 2) :=
            mul_le_mul e1 e2 (abs_nonneg _) (by linarith [abs_nonneg (pS bi x)])
        _ = _ := by ring
    exact (le_abs_self _).trans this
  rw [integral_const_mul] at h1 h2
  have hσ2 : 0 ≤ 2 * σ := by linarith
  linarith [mul_le_mul_of_nonneg_left h1 hσ, mul_le_mul_of_nonneg_left h2 hσ2]

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the local models at negative and positive zeros. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma coord_eq_zero_of_eventually {U : ℝ × ℝ → Vec 1} {x : ℝ × ℝ} (h : U =ᶠ[𝓝 x] 0) (i) :
    coord U i x = 0 := by
  simp [coord, h.self_of_nhds]

/-- Common data for the local models: all the splittings of the integrals. -/
structure LocData (σ : ℝ) (β : ℝ × ℝ → ℂ) (U : ℝ × ℝ → Vec 1) : Prop where
  expand : ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure =
      (∫ x, pS (coord U i₁) x ^ 2 ∂cylMeasure + ∫ x, pT (coord U i₁) x ^ 2 ∂cylMeasure +
        ∫ x, pS (coord U i₂) x ^ 2 ∂cylMeasure + ∫ x, pT (coord U i₂) x ^ 2 ∂cylMeasure) +
      σ ^ 2 * (∫ x, (β x).re ^ 2 * coord U i₁ x ^ 2 ∂cylMeasure +
        ∫ x, (β x).im ^ 2 * coord U i₁ x ^ 2 ∂cylMeasure +
        ∫ x, (β x).re ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure +
        ∫ x, (β x).im ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure) -
      σ * ∫ x, (pS (fun y => (β y).re) x + pT (fun y => (β y).im) x) *
        (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure -
      2 * σ * ∫ x, (pS (fun y => (β y).im) x - pT (fun y => (β y).re) x) *
        (coord U i₁ x * coord U i₂ x) ∂cylMeasure
  norm : ∫ x, ‖U x‖ ^ 2 ∂cylMeasure =
      ∫ x, coord U i₁ x ^ 2 ∂cylMeasure + ∫ x, coord U i₂ x ^ 2 ∂cylMeasure
  diff : ∫ x, (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure =
      ∫ x, coord U i₁ x ^ 2 ∂cylMeasure - ∫ x, coord U i₂ x ^ 2 ∂cylMeasure
  oss : ∀ (i : Fin 1 ⊕ Fin 1) (f : ℝ × ℝ → ℝ), ContDiff ℝ 1 f → ∀ τ : ℝ,
      ∫ x, (pS (coord U i) x + τ * f x * coord U i x) ^ 2 ∂cylMeasure =
        ∫ x, pS (coord U i) x ^ 2 ∂cylMeasure + τ ^ 2 * ∫ x, f x ^ 2 * coord U i x ^ 2 ∂cylMeasure -
          τ * ∫ x, pS f x * coord U i x ^ 2 ∂cylMeasure
  ost : ∀ (i : Fin 1 ⊕ Fin 1) (f : ℝ × ℝ → ℝ), ContDiff ℝ 1 f → PerT f → ∀ τ : ℝ,
      ∫ x, (pT (coord U i) x + τ * f x * coord U i x) ^ 2 ∂cylMeasure =
        ∫ x, pT (coord U i) x ^ 2 ∂cylMeasure + τ ^ 2 * ∫ x, f x ^ 2 * coord U i x ^ 2 ∂cylMeasure -
          τ * ∫ x, pT f x * coord U i x ^ 2 ∂cylMeasure

lemma locData (σ : ℝ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) :
    LocData σ β U := by
  obtain ⟨R, hR⟩ := hU.vanS
  have vX := hR i₁
  have vY := hR i₂
  have cX1 : ContDiff ℝ 1 (coord U i₁) := hU.coord_smooth i₁
  have cY1 : ContDiff ℝ 1 (coord U i₂) := hU.coord_smooth i₂
  have cXc := cX1.continuous
  have cYc := cY1.continuous
  have cXs := continuous_pS cX1
  have cXt := continuous_pT cX1
  have cYs := continuous_pS cY1
  have cYt := continuous_pT cY1
  have cβ := hβ.continuous
  have cr : Continuous fun x => (β x).re := Complex.continuous_re.comp cβ
  have ci : Continuous fun x => (β x).im := Complex.continuous_im.comp cβ
  have iX : Integrable (fun x => coord U i₁ x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs]) (by fun_prop)
  have iY : Integrable (fun x => coord U i₂ x ^ 2) cylMeasure :=
    VanS.integrable (R := R) (fun s t hs => by simp [vY s t hs]) (by fun_prop)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [D0_expand σ hβ hβper hU]
    have e1 : (fun x => pS (coord U i₁) x ^ 2 + pT (coord U i₁) x ^ 2 + pS (coord U i₂) x ^ 2 +
        pT (coord U i₂) x ^ 2) = fun x => pS (coord U i₁) x ^ 2 + pT (coord U i₁) x ^ 2 +
        pS (coord U i₂) x ^ 2 + pT (coord U i₂) x ^ 2 := rfl
    rw [integral_add4 (f₁ := fun x => pS (coord U i₁) x ^ 2) (f₂ := fun x => pT (coord U i₁) x ^ 2)
      (f₃ := fun x => pS (coord U i₂) x ^ 2) (f₄ := fun x => pT (coord U i₂) x ^ 2)
      (VanS.integrable (R := R) (fun s t hs => by simp [vX.pS s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vX.pT s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vY.pS s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vY.pT s t hs]) (by fun_prop))]
    have e2 : (fun x => ((β x).re ^ 2 + (β x).im ^ 2) * (coord U i₁ x ^ 2 + coord U i₂ x ^ 2)) =
        fun x => (β x).re ^ 2 * coord U i₁ x ^ 2 + (β x).im ^ 2 * coord U i₁ x ^ 2 +
          (β x).re ^ 2 * coord U i₂ x ^ 2 + (β x).im ^ 2 * coord U i₂ x ^ 2 := by
      funext x; ring
    rw [e2, integral_add4
      (VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vX s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vY s t hs]) (by fun_prop))
      (VanS.integrable (R := R) (fun s t hs => by simp [vY s t hs]) (by fun_prop))]
  · simp only [norm_sq_coord]
    exact integral_add iX iY
  · exact integral_sub iX iY
  · intro i f hf τ
    exact osc_s (coord U i) f (hU.coord_smooth i) hf R (hR i) τ
  · intro i f hf hfp τ
    exact osc_t (coord U i) f (hU.coord_smooth i) hf R (hR i) (hU.perT i) hfp τ

/-- The local model at a negative zero: `∫ ‖D_σ u‖² ≥ 2σ ∫ |u|²`. -/
theorem D0_neg (σ : ℝ) (hσ : 0 ≤ σ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U)
    (hP : ∀ x, U =ᶠ[𝓝 x] 0 ∨ (pS (fun y => (β y).re) x = 1 ∧ pT (fun y => (β y).im) x = -1 ∧
      pS (fun y => (β y).im) x = 0 ∧ pT (fun y => (β y).re) x = 0)) :
    2 * σ * ∫ x, ‖U x‖ ^ 2 ∂cylMeasure ≤
      ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure := by
  have D := locData σ hβ hβper hU
  have cr : ContDiff ℝ 1 fun y => (β y).re := re_contDiff hβ
  have ci : ContDiff ℝ 1 fun y => (β y).im := im_contDiff hβ
  have pip : PerT fun y => (β y).im := fun s t => by simp [hβper s t]
  have z1 : ∫ x, (pS (fun y => (β y).re) x + pT (fun y => (β y).im) x) *
      (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨h1, h2, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h1, h2]
  have z2 : ∫ x, (pS (fun y => (β y).im) x - pT (fun y => (β y).re) x) *
      (coord U i₁ x * coord U i₂ x) ∂cylMeasure = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨-, -, h3, h4⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h3, h4]
  have ws : ∀ i, ∫ x, pS (fun y => (β y).re) x * coord U i x ^ 2 ∂cylMeasure =
      ∫ x, coord U i x ^ 2 ∂cylMeasure := fun i => by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨h1, -, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h1]
  have wt : ∀ i, ∫ x, pT (fun y => (β y).im) x * coord U i x ^ 2 ∂cylMeasure =
      -∫ x, coord U i x ^ 2 ∂cylMeasure := fun i => by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨-, h2, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h2]
  have a1 := D.oss i₁ _ cr σ
  have a2 := D.oss i₂ _ cr σ
  have a3 := D.ost i₁ _ ci pip (-σ)
  have a4 := D.ost i₂ _ ci pip (-σ)
  rw [ws] at a1 a2
  rw [wt] at a3 a4
  have q1 : 0 ≤ ∫ x, (pS (coord U i₁) x + σ * (β x).re * coord U i₁ x) ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => sq_nonneg _
  have q2 : 0 ≤ ∫ x, (pS (coord U i₂) x + σ * (β x).re * coord U i₂ x) ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => sq_nonneg _
  have q3 : 0 ≤ ∫ x, (pT (coord U i₁) x + -σ * (β x).im * coord U i₁ x) ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => sq_nonneg _
  have q4 : 0 ≤ ∫ x, (pT (coord U i₂) x + -σ * (β x).im * coord U i₂ x) ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => sq_nonneg _
  rw [D.expand, D.norm, z1, z2]
  nlinarith

/-- The local model at a positive zero: `∫ ‖D_σ u‖²` dominates the two squares of the
first component plus `2σ ∫ (u₂)²`. -/
theorem D0_pos (σ : ℝ) (hσ : 0 ≤ σ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U)
    (hP : ∀ x, U =ᶠ[𝓝 x] 0 ∨ (pS (fun y => (β y).re) x = 1 ∧ pT (fun y => (β y).im) x = 1 ∧
      pS (fun y => (β y).im) x = 0 ∧ pT (fun y => (β y).re) x = 0)) :
    ∫ x, (pS (coord U i₁) x + σ * (β x).re * coord U i₁ x) ^ 2 ∂cylMeasure +
      ∫ x, (pT (coord U i₁) x + σ * (β x).im * coord U i₁ x) ^ 2 ∂cylMeasure +
      2 * σ * ∫ x, coord U i₂ x ^ 2 ∂cylMeasure ≤
      ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure := by
  have D := locData σ hβ hβper hU
  have cr : ContDiff ℝ 1 fun y => (β y).re := re_contDiff hβ
  have ci : ContDiff ℝ 1 fun y => (β y).im := im_contDiff hβ
  have pip : PerT fun y => (β y).im := fun s t => by simp [hβper s t]
  have z1 : ∫ x, (pS (fun y => (β y).re) x + pT (fun y => (β y).im) x) *
      (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure =
      2 * ∫ x, (coord U i₁ x ^ 2 - coord U i₂ x ^ 2) ∂cylMeasure := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨h1, h2, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp only [h1, h2]; ring
  have z2 : ∫ x, (pS (fun y => (β y).im) x - pT (fun y => (β y).re) x) *
      (coord U i₁ x * coord U i₂ x) ∂cylMeasure = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨-, -, h3, h4⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h3, h4]
  have ws : ∫ x, pS (fun y => (β y).re) x * coord U i₁ x ^ 2 ∂cylMeasure =
      ∫ x, coord U i₁ x ^ 2 ∂cylMeasure := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨h1, -, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h1]
  have wt : ∫ x, pT (fun y => (β y).im) x * coord U i₁ x ^ 2 ∂cylMeasure =
      ∫ x, coord U i₁ x ^ 2 ∂cylMeasure := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rcases hP x with h | ⟨-, h2, -, -⟩
    · simp [coord_eq_zero_of_eventually h]
    · simp [h2]
  have a1 := D.oss i₁ _ cr σ
  have a3 := D.ost i₁ _ ci pip σ
  rw [ws] at a1
  rw [wt] at a3
  have p1 : 0 ≤ ∫ x, pS (coord U i₂) x ^ 2 ∂cylMeasure := integral_nonneg fun x => sq_nonneg _
  have p2 : 0 ≤ ∫ x, pT (coord U i₂) x ^ 2 ∂cylMeasure := integral_nonneg fun x => sq_nonneg _
  have p3 : 0 ≤ ∫ x, (β x).re ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => by positivity
  have p4 : 0 ≤ ∫ x, (β x).im ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => by positivity
  rw [D.expand, z1, z2, D.diff]
  have : 0 ≤ σ ^ 2 * (∫ x, (β x).re ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure +
      ∫ x, (β x).im ^ 2 * coord U i₂ x ^ 2 ∂cylMeasure) := by positivity
  nlinarith

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the spectral gap at a positive zero. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- The box `[a - 1/2, a + 1/2] × [b - 1/2, b + 1/2]`. -/
abbrev box (a b : ℝ) : Set (ℝ × ℝ) := Icc (a - 1 / 2) (a + 1 / 2) ×ˢ Icc (b - 1 / 2) (b + 1 / 2)

/-- A `t`-periodic function supported in `|s - a| < 1/2` integrates over the cylinder as over
the box centred at `(a, b)`. -/
lemma cyl_eq_box {F : ℝ × ℝ → ℝ} (hF : Continuous F) (hper : PerT F) (a b : ℝ)
    (hv : ∀ s t, 1 / 2 ≤ |s - a| → F (s, t) = 0) :
    ∫ x, F x ∂cylMeasure = ∫ x in box a b, F x := by
  have hvR : VanS (|a| + 1 / 2) F := fun s t hs => hv s t (by
    have := abs_sub_abs_le_abs_sub s a; linarith)
  have hI := hvR.integrable hF
  rw [cylMeasure_eq_prod] at hI ⊢
  rw [integral_prod _ hI, box, GPoin.restrict_prod, integral_prod _ (GPoin.integrable_box hF _ _ _ _)]
  have hslice : ∀ s, ∫ t in Ico (0 : ℝ) 1, F (s, t) = ∫ t in Icc (b - 1 / 2) (b + 1 / 2), F (s, t) := by
    intro s
    have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hper s t
    have h := hp.intervalIntegral_add_eq 0 (b - 1 / 2)
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have e1 : (0 : ℝ) + 1 = 1 := by norm_num
    have e2 : b - 1 / 2 + 1 = b + 1 / 2 := by ring
    rw [e1, e2] at h
    exact h
  simp only [hslice]
  symm
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
  have : 1 / 2 ≤ |s - a| := by
    by_contra hlt
    push_neg at hlt
    exact hs ⟨by linarith [(abs_lt.1 hlt).1], by linarith [(abs_lt.1 hlt).2]⟩
  simp [hv s _ this]

lemma pS_eq_zero_of_eventually {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : f =ᶠ[𝓝 x] 0) : pS f x = 0 := by
  simp [pS, h.fderiv_eq]

lemma pT_eq_zero_of_eventually {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : f =ᶠ[𝓝 x] 0) : pT f x = 0 := by
  simp [pT, h.fderiv_eq]

lemma coord_eventually {U : ℝ × ℝ → Vec 1} {x : ℝ × ℝ} (h : U =ᶠ[𝓝 x] 0) (i) :
    coord U i =ᶠ[𝓝 x] 0 := h.mono fun y hy => by simp [coord, hy]

/-- The spectral gap at a positive zero. Here `G = exp(-σ|β|²/2)` and `N = ∫_box w`. -/
theorem D0_pos_gap (σ : ℝ) (hσ : 0 < σ) {β : ℝ × ℝ → ℂ} (hβ : ContDiff ℝ 2 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) {U : ℝ × ℝ → Vec 1} (hU : IsTestSection U) (a b : ℝ)
    (hP : ∀ x, U =ᶠ[𝓝 x] 0 ∨ (pS (fun y => (β y).re) x = 1 ∧ pT (fun y => (β y).im) x = 1 ∧
      pS (fun y => (β y).im) x = 0 ∧ pT (fun y => (β y).re) x = 0 ∧
      (|x.2 - b| ≤ 1 / 2 → (β x).re = x.1 - a ∧ (β x).im = x.2 - b)))
    (hstrip : ∀ s t, 1 / 4 ≤ |s - a| → U (s, t) = 0) :
    σ / 8 * (∫ x, ‖U x‖ ^ 2 ∂cylMeasure -
        (∫ x, Real.exp (-σ * ((β x).re ^ 2 + (β x).im ^ 2) / 2) * coord U i₁ x ∂cylMeasure) ^ 2 /
          ∫ x in box a b, Real.exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2))) ≤
      ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure := by
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by norm_num)
  have hpos := D0_pos σ hσ.le hβ1 hβper hU (fun x => (hP x).imp_right fun h => ⟨h.1, h.2.1, h.2.2.1,
    h.2.2.2.1⟩)
  have D := locData σ hβ1 hβper hU
  set X := coord U i₁ with hX
  have cX : ContDiff ℝ 2 X := hU.coord_smooth i₁
  have cX1 : ContDiff ℝ 1 X := cX.of_le (by norm_num)
  have cr : ContDiff ℝ 2 fun y => (β y).re := re_contDiff hβ
  have ci : ContDiff ℝ 2 fun y => (β y).im := im_contDiff hβ
  have cr1 : ContDiff ℝ 1 fun y => (β y).re := cr.of_le (by norm_num)
  have ci1 : ContDiff ℝ 1 fun y => (β y).im := ci.of_le (by norm_num)
  set br : ℝ × ℝ → ℝ := fun y => (β y).re with hbr
  set bi : ℝ × ℝ → ℝ := fun y => (β y).im with hbi
  -- the Gaussian weight and its inverse
  set q : ℝ × ℝ → ℝ := fun x => br x ^ 2 + bi x ^ 2 with hq
  have cq : ContDiff ℝ 2 q := (cr.pow 2).add (ci.pow 2)
  set E : ℝ × ℝ → ℝ := fun x => Real.exp (σ * q x / 2) with hE
  set G : ℝ × ℝ → ℝ := fun x => Real.exp (-σ * q x / 2) with hG
  have cE : ContDiff ℝ 2 E := ((contDiff_const.mul cq).div_const _).exp
  have cE1 : ContDiff ℝ 1 E := cE.of_le (by norm_num)
  have hGE : ∀ x, G x * E x = 1 := fun x => by
    simp only [hG, hE, ← Real.exp_add]; ring_nf; simp
  set g : ℝ × ℝ → ℝ := fun x => X x * E x with hg
  have cg : ContDiff ℝ 2 g := cX.mul cE
  have cg1 : ContDiff ℝ 1 g := cg.of_le (by norm_num)
  have hXg : ∀ x, X x = G x * g x := fun x => by
    simp only [hg]; rw [← mul_assoc, mul_comm (G x), mul_assoc, hGE, mul_one]
  -- derivatives of `E`
  have dES : ∀ x, pS E x = E x * (σ * (br x * pS br x + bi x * pS bi x)) := fun x =>
    pS_eq_of_hasDerivAt (g := fun x => E x * (σ * (br x * pS br x + bi x * pS bi x))) cE1
      (fun s t => by
        have h1 := ((((hasDerivAt_pS cr1 s t).pow 2).add ((hasDerivAt_pS ci1 s t).pow 2)).const_mul
          σ).div_const 2
        exact h1.exp.congr_deriv (by simp only [hE, hq, Pi.add_apply, Pi.pow_apply]; ring)) x
  have dET : ∀ x, pT E x = E x * (σ * (br x * pT br x + bi x * pT bi x)) := fun x =>
    pT_eq_of_hasDerivAt (g := fun x => E x * (σ * (br x * pT br x + bi x * pT bi x))) cE1
      (fun s t => by
        have h1 := ((((hasDerivAt_pT cr1 s t).pow 2).add ((hasDerivAt_pT ci1 s t).pow 2)).const_mul
          σ).div_const 2
        exact h1.exp.congr_deriv (by simp only [hE, hq, Pi.add_apply, Pi.pow_apply]; ring)) x
  -- the ground-state substitution
  have subS : ∀ x, pS X x + σ * br x * X x = G x * pS g x := by
    intro x
    rcases hP x with h | ⟨h1, -, h3, -, -⟩
    · have hx := coord_eventually h i₁
      have hg0 : g =ᶠ[𝓝 x] 0 := hx.mono fun y hy => by
        simp only [hg]; rw [show X y = 0 from hy]; simp
      have hx0 : X x = 0 := hx.self_of_nhds
      rw [pS_eq_zero_of_eventually hx, pS_eq_zero_of_eventually hg0, hx0]
      simp
    · rw [hg, pS_mul cX1 cE1, dES, h1, h3]
      have := hGE x
      linear_combination -(pS X x + σ * br x * X x) * this
  have subT : ∀ x, pT X x + σ * bi x * X x = G x * pT g x := by
    intro x
    rcases hP x with h | ⟨-, h2, -, h4, -⟩
    · have hx := coord_eventually h i₁
      have hg0 : g =ᶠ[𝓝 x] 0 := hx.mono fun y hy => by
        simp only [hg]; rw [show X y = 0 from hy]; simp
      have hx0 : X x = 0 := hx.self_of_nhds
      rw [pT_eq_zero_of_eventually hx, pT_eq_zero_of_eventually hg0, hx0]
      simp
    · rw [hg, pT_mul cX1 cE1, dET, h2, h4]
      have := hGE x
      linear_combination -(pT X x + σ * bi x * X x) * this
  -- Poincaré on the box
  obtain ⟨c, hc⟩ := gaussian_poincare_rectangle σ hσ a b (1 / 2) (1 / 2) (by norm_num) (by norm_num) g cg1
  set w : ℝ × ℝ → ℝ := fun x => Real.exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) with hw
  have cw : Continuous w := by fun_prop
  -- on the box, `w = G²` wherever `U` does not vanish near the point
  have hbox : ∀ x ∈ box a b, U =ᶠ[𝓝 x] 0 ∨ w x = G x ^ 2 := by
    intro x hx
    rcases hP x with h | ⟨-, -, -, -, h5⟩
    · exact Or.inl h
    · right
      have hb : |x.2 - b| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
      obtain ⟨e1, e2⟩ := h5 hb
      simp only [hw, hG, hq, ← Real.exp_nat_mul]
      rw [show br x = x.1 - a from e1, show bi x = x.2 - b from e2]
      congr 1; push_cast; ring
  have cG : Continuous G := by fun_prop
  have cgs := continuous_pS cg1
  have cgt := continuous_pT cg1
  have cXc := cX1.continuous
  have pXp : PerT X := hU.perT i₁
  have pq : PerT q := fun s t => by simp [hq, hbr, hbi, hβper s t]
  have pG : PerT G := fun s t => by simp only [hG, pq s t]
  have pE : PerT E := fun s t => by simp only [hE, pq s t]
  have pg : PerT g := fun s t => by simp only [hg, pXp s t, pE s t]
  have vU : ∀ s t, 1 / 2 ≤ |s - a| → U =ᶠ[𝓝 (s, t)] 0 := by
    intro s t hs
    have hO : IsOpen {y : ℝ × ℝ | 1 / 4 < |y.1 - a|} :=
      isOpen_lt continuous_const ((continuous_fst.sub continuous_const).abs)
    refine Filter.eventually_of_mem (hO.mem_nhds (by show 1 / 4 < |s - a|; linarith)) ?_
    intro y hy
    have := hstrip y.1 y.2 (le_of_lt hy)
    simpa using this
  have vg : ∀ s t, 1 / 2 ≤ |s - a| → g =ᶠ[𝓝 (s, t)] 0 := fun s t hs =>
    (coord_eventually (vU s t hs) i₁).mono fun y hy => by
      simp only [hg]; rw [show X y = 0 from hy]; simp
  have gzero : ∀ x, U =ᶠ[𝓝 x] 0 → g x = 0 ∧ pS g x = 0 ∧ pT g x = 0 ∧ X x = 0 := by
    intro x h
    have hx := coord_eventually h i₁
    have hg0 : g =ᶠ[𝓝 x] 0 := hx.mono fun y hy => by
      simp only [hg]; rw [show X y = 0 from hy]; simp
    exact ⟨hg0.self_of_nhds, pS_eq_zero_of_eventually hg0, pT_eq_zero_of_eventually hg0,
      hx.self_of_nhds⟩
  have hmb : MeasurableSet (box a b) := measurableSet_Icc.prod measurableSet_Icc
  -- transfer the three box integrals to the cylinder
  have T1 : ∫ x in box a b, (pS g x ^ 2 + pT g x ^ 2) * w x =
      ∫ x, G x ^ 2 * (pS g x ^ 2 + pT g x ^ 2) ∂cylMeasure := by
    rw [cyl_eq_box (by fun_prop) (fun s t => by
      simp only [pG s t, pS_periodic cg1 pg s t, pT_periodic cg1 pg s t]) a b (fun s t hs => by
        simp [pS_eq_zero_of_eventually (vg s t hs), pT_eq_zero_of_eventually (vg s t hs)])]
    refine setIntegral_congr_fun hmb fun x hx => ?_
    rcases hbox x hx with h | h
    · obtain ⟨-, h2, h3, -⟩ := gzero x h
      simp [h2, h3]
    · simp only [h]; ring
  have T2 : ∫ x in box a b, g x ^ 2 * w x = ∫ x, X x ^ 2 ∂cylMeasure := by
    rw [cyl_eq_box (by fun_prop) (fun s t => by simp only [pXp s t]) a b (fun s t hs => by
        have := hstrip s t (by linarith); simp [hX, coord, this])]
    refine setIntegral_congr_fun hmb fun x hx => ?_
    rcases hbox x hx with h | h
    · obtain ⟨h1, -, -, h4⟩ := gzero x h
      simp [h1, h4]
    · simp only [h, hXg x]; ring
  have T3 : ∫ x in box a b, g x * w x = ∫ x, G x * X x ∂cylMeasure := by
    rw [cyl_eq_box (by fun_prop) (fun s t => by simp only [pXp s t, pG s t]) a b (fun s t hs => by
        have := hstrip s t (by linarith); simp [hX, coord, this])]
    refine setIntegral_congr_fun hmb fun x hx => ?_
    rcases hbox x hx with h | h
    · obtain ⟨h1, -, -, h4⟩ := gzero x h
      simp [h1, h4]
    · simp only [h, hXg x]; ring
  -- the Gaussian mass of the box
  have hbc : IsCompact (box a b) := isCompact_Icc.prod isCompact_Icc
  have iB : ∀ {F : ℝ × ℝ → ℝ}, Continuous F → Integrable F (volume.restrict (box a b)) :=
    fun hF => hF.continuousOn.integrableOn_compact hbc
  have Npos : 0 < ∫ x in box a b, w x := by
    have : NeZero (volume.restrict (box a b)) := ⟨by
      rw [Ne, Measure.restrict_eq_zero, Measure.volume_eq_prod, Measure.prod_prod,
        Real.volume_Icc, Real.volume_Icc]
      norm_num⟩
    exact integral_exp_pos (iB cw)
  -- expand the Poincaré inequality
  have hexp := GPoin.sq_expand (μ := volume.restrict (box a b)) g w (iB (by fun_prop))
    (iB (by fun_prop)) (iB cw) c
  have hc' : ∫ x in box a b, (g x - c) ^ 2 * w x ≤
      8 / σ * ∫ x in box a b, (pS g x ^ 2 + pT g x ^ 2) * w x := hc
  rw [hexp, T1, T2, T3] at hc'
  have hsq : ∫ x, G x ^ 2 * (pS g x ^ 2 + pT g x ^ 2) ∂cylMeasure =
      ∫ x, (pS X x + σ * br x * X x) ^ 2 ∂cylMeasure +
        ∫ x, (pT X x + σ * bi x * X x) ^ 2 ∂cylMeasure := by
    rw [← integral_add]
    · congr 1; funext x; rw [subS, subT]; ring
    · obtain ⟨R, hR⟩ := hU.vanS
      have v := hR i₁
      have c1 := continuous_pS cX1
      have c2 := cr1.continuous
      exact VanS.integrable (R := R) (fun s t hs => by
        rw [show X (s, t) = 0 from v s t hs, show pS X (s, t) = 0 from v.pS s t hs]; ring) (by fun_prop)
    · obtain ⟨R, hR⟩ := hU.vanS
      have v := hR i₁
      have c1 := continuous_pT cX1
      have c2 := ci1.continuous
      exact VanS.integrable (R := R) (fun s t hs => by
        rw [show X (s, t) = 0 from v s t hs, show pT X (s, t) = 0 from v.pT s t hs]; ring) (by fun_prop)
  rw [hsq] at hc'
  rw [D.norm]
  set Xi := ∫ x, X x ^ 2 ∂cylMeasure
  set Yi := ∫ x, coord U i₂ x ^ 2 ∂cylMeasure
  set ℓ := ∫ x, G x * X x ∂cylMeasure
  set N := ∫ x in box a b, w x
  set Q := ∫ x, (pS X x + σ * br x * X x) ^ 2 ∂cylMeasure +
    ∫ x, (pT X x + σ * bi x * X x) ^ 2 ∂cylMeasure
  have hY0 : 0 ≤ Yi := integral_nonneg fun x => sq_nonneg _
  have hamgm : Xi - ℓ ^ 2 / N ≤ Xi - 2 * c * ℓ + c ^ 2 * N := by
    have : 2 * c * ℓ - c ^ 2 * N ≤ ℓ ^ 2 / N := by
      rw [le_div_iff₀ Npos]
      nlinarith [sq_nonneg (c * N - ℓ)]
    linarith
  have h8 : σ / 8 * (Xi - ℓ ^ 2 / N) ≤ Q := by
    have := hamgm.trans hc'
    have e : σ / 8 * (8 / σ * Q) = Q := by field_simp
    calc σ / 8 * (Xi - ℓ ^ 2 / N) ≤ σ / 8 * (8 / σ * Q) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = Q := e
  have hpos' : Q + 2 * σ * Yi ≤ ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) U x‖ ^ 2 ∂cylMeasure :=
    hpos
  nlinarith

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: cut-offs around the zeros. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma per_fract {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma per_int {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ)
    (m : ℤ) : F (s, t + m) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.int_mul m t
  rw [mul_one] at this
  exact this

/-- A continuous, `t`-periodic function vanishing for large `|s|` is bounded. -/
lemma bounded_of_per_van {f : ℝ × ℝ → ℝ} (hf : Continuous f) (hp : PerT f) {R : ℝ}
    (hR : VanS R f) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (s := Icc (-R) R)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : R < |x.1|
  · rw [show x = (x.1, x.2) from rfl, hR _ _ hx]; simp
  · push_neg at hx
    rw [show x = (x.1, x.2) from rfl, ← per_fract hp]
    have := hC (x.1, Int.fract x.2) ⟨⟨by linarith [neg_abs_le x.1], by linarith [le_abs_self x.1]⟩,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-! ### The periodic distance function and the cut-off -/

/-- `q(τ) = (sin(πτ)/π)²`, a smooth `1`-periodic substitute for `τ²`. -/
def qf (τ : ℝ) : ℝ := (Real.sin (π * τ) / π) ^ 2

lemma qf_int (τ : ℝ) (m : ℤ) : qf (τ + m) = qf τ := by
  have h : ((-1 : ℝ) ^ m) ^ 2 = 1 := by
    rw [sq, ← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  simp only [qf]
  rw [mul_add, mul_comm π (m : ℝ), sin_add_int_mul_pi, mul_div_assoc, mul_pow, h, one_mul]

lemma qf_le (τ : ℝ) : qf τ ≤ τ ^ 2 := by
  simp only [qf]
  have hπ := Real.pi_pos
  rw [div_pow, div_le_iff₀ (by positivity)]
  have h := abs_sin_le_abs (x := π * τ)
  rw [abs_mul, abs_of_pos hπ] at h
  calc Real.sin (π * τ) ^ 2 = |Real.sin (π * τ)| ^ 2 := (sq_abs _).symm
    _ ≤ (π * |τ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = τ ^ 2 * π ^ 2 := by rw [mul_pow, sq_abs]; ring

lemma qf_abs (τ : ℝ) : qf |τ| = qf τ := by
  rcases abs_choice τ with h | h <;> rw [h]
  simp only [qf, mul_neg, Real.sin_neg, neg_div, neg_sq]

lemma qf_ge {τ : ℝ} (hτ : |τ| ≤ 1 / 2) : 4 / π ^ 2 * τ ^ 2 ≤ qf τ := by
  rw [← qf_abs, ← sq_abs τ]
  set u := |τ| with hu
  have hu0 : 0 ≤ u := abs_nonneg τ
  have hπ := Real.pi_pos
  have h1 : 2 / π * (π * u) ≤ Real.sin (π * u) :=
    mul_le_sin (by positivity) (by nlinarith)
  have e : 2 / π * (π * u) = 2 * u := by field_simp
  rw [e] at h1
  have h2 : (2 * u) ^ 2 ≤ Real.sin (π * u) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  simp only [qf]
  rw [div_pow, le_div_iff₀ (by positivity)]
  calc 4 / π ^ 2 * u ^ 2 * π ^ 2 = (2 * u) ^ 2 := by field_simp; ring
    _ ≤ _ := h2

lemma contDiff_qf : ContDiff ℝ ∞ qf := by
  unfold qf; fun_prop

/-- The squared periodic distance to `ζ`. -/
def wz (ζ : ℝ × ℝ) (x : ℝ × ℝ) : ℝ := (x.1 - ζ.1) ^ 2 + qf (x.2 - ζ.2)

/-- `x - ζ - (0, m)` as a complex number. -/
def zc (ζ : ℝ × ℝ) (m : ℤ) (x : ℝ × ℝ) : ℂ := ⟨x.1 - ζ.1, x.2 - ζ.2 - m⟩

lemma norm_zc_sq (ζ : ℝ × ℝ) (m : ℤ) (x : ℝ × ℝ) :
    ‖zc ζ m x‖ ^ 2 = (x.1 - ζ.1) ^ 2 + (x.2 - ζ.2 - m) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp [zc]; ring

lemma contDiff_wz (ζ : ℝ × ℝ) : ContDiff ℝ ∞ (wz ζ) := by
  unfold wz
  exact ((contDiff_fst.sub contDiff_const).pow 2).add (contDiff_qf.comp (contDiff_snd.sub contDiff_const))

lemma wz_per (ζ : ℝ × ℝ) : PerT (wz ζ) := fun s t => by
  simp only [wz]
  have := qf_int (t - ζ.2) 1
  push_cast at this
  rw [show t + 1 - ζ.2 = t - ζ.2 + 1 by ring, this]

lemma wz_le (ζ : ℝ × ℝ) (m : ℤ) (x : ℝ × ℝ) : wz ζ x ≤ ‖zc ζ m x‖ ^ 2 := by
  rw [norm_zc_sq, wz]
  have := qf_int (x.2 - ζ.2 - m) m
  rw [sub_add_cancel] at this
  rw [this]
  linarith [qf_le (x.2 - ζ.2 - m)]

lemma wz_ge (ζ : ℝ × ℝ) (x : ℝ × ℝ) :
    4 / π ^ 2 * ‖zc ζ (round (x.2 - ζ.2)) x‖ ^ 2 ≤ wz ζ x := by
  rw [norm_zc_sq, wz]
  set m := round (x.2 - ζ.2)
  have hm : |x.2 - ζ.2 - m| ≤ 1 / 2 := abs_sub_round _
  have := qf_int (x.2 - ζ.2 - m) m
  rw [sub_add_cancel] at this
  rw [this]
  have h1 := qf_ge hm
  have hπ : 4 / π ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  nlinarith [sq_nonneg (x.1 - ζ.1)]

lemma pi_sq_lt : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- The radial profile: `1` on `[0, r²/256]`, supported in `(-r²/64, r²/64)`. -/
def prof (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) :=
  ⟨r ^ 2 / 256, r ^ 2 / 64, by positivity, by nlinarith [sq_pos_of_pos hr]⟩

/-- The cut-off around `ζ`. -/
def chi (r : ℝ) (hr : 0 < r) (ζ : ℝ × ℝ) (x : ℝ × ℝ) : ℝ := prof r hr (wz ζ x)

lemma contDiff_chi (r : ℝ) (hr : 0 < r) (ζ : ℝ × ℝ) : ContDiff ℝ ∞ (chi r hr ζ) :=
  (prof r hr).contDiff.comp (contDiff_wz ζ)

lemma chi_per (r : ℝ) (hr : 0 < r) (ζ : ℝ × ℝ) : PerT (chi r hr ζ) := fun s t => by
  simp only [chi, wz_per ζ s t]

lemma chi_nonneg (r : ℝ) (hr : 0 < r) (ζ x) : 0 ≤ chi r hr ζ x := (prof r hr).nonneg

lemma chi_le_one (r : ℝ) (hr : 0 < r) (ζ x) : chi r hr ζ x ≤ 1 := (prof r hr).le_one

lemma wz_nonneg (ζ x) : 0 ≤ wz ζ x := by
  simp only [wz, qf]; positivity

lemma chi_eq_one (r : ℝ) (hr : 0 < r) {ζ x} (h : wz ζ x ≤ r ^ 2 / 256) : chi r hr ζ x = 1 :=
  (prof r hr).one_of_mem_closedBall (x := wz ζ x) (by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_nonneg (wz_nonneg ζ x)]; exact h)

lemma chi_ne_zero (r : ℝ) (hr : 0 < r) {ζ x} (h : chi r hr ζ x ≠ 0) : wz ζ x < r ^ 2 / 64 := by
  have h2 : wz ζ x ∈ Function.support (prof r hr) := h
  rw [(prof r hr).support_eq, Metric.mem_ball, Real.dist_eq, sub_zero,
    abs_of_nonneg (wz_nonneg ζ x)] at h2
  exact h2

/-- Where `wz > r²/64`, the cut-off vanishes near the point. -/
lemma chi_eventually_zero (r : ℝ) (hr : 0 < r) {ζ x} (h : r ^ 2 / 64 < wz ζ x) :
    chi r hr ζ =ᶠ[𝓝 x] 0 := by
  have hO : IsOpen {y | r ^ 2 / 64 < wz ζ y} := isOpen_lt continuous_const (contDiff_wz ζ).continuous
  refine Filter.eventually_of_mem (hO.mem_nhds h) fun y hy => ?_
  by_contra hne
  exact absurd (chi_ne_zero r hr hne) (not_lt.2 (le_of_lt hy))

/-- Where `wz < r²/256`, the cut-off is `1` near the point. -/
lemma chi_eventually_one (r : ℝ) (hr : 0 < r) {ζ x} (h : wz ζ x < r ^ 2 / 256) :
    chi r hr ζ =ᶠ[𝓝 x] fun _ => 1 := by
  have hO : IsOpen {y | wz ζ y < r ^ 2 / 256} := isOpen_lt (contDiff_wz ζ).continuous continuous_const
  exact Filter.eventually_of_mem (hO.mem_nhds h) fun y hy => chi_eq_one r hr (le_of_lt hy)

/-- Where `wz ≤ r²/64`, some copy of `ζ` is at distance `< r/4`. -/
lemma near_of_wz (r : ℝ) (hr : 0 < r) {ζ x} (h : wz ζ x ≤ r ^ 2 / 64) :
    ‖zc ζ (round (x.2 - ζ.2)) x‖ < r / 4 := by
  have h1 := wz_ge ζ x
  have hπ := pi_sq_lt
  have hπ0 := Real.pi_pos
  have h2 : ‖zc ζ (round (x.2 - ζ.2)) x‖ ^ 2 < (r / 4) ^ 2 := by
    have : 4 / π ^ 2 * ‖zc ζ (round (x.2 - ζ.2)) x‖ ^ 2 ≤ r ^ 2 / 64 := h1.trans h
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at this
    nlinarith [sq_nonneg ‖zc ζ (round (x.2 - ζ.2)) x‖, sq_pos_of_pos hr]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2

/-- Away from all copies of `ζ` (distance `≥ r/2`), `wz > r²/64`. -/
lemma wz_gt_of_far (r : ℝ) (hr : 0 < r) {ζ x} (h : r / 2 ≤ ‖zc ζ (round (x.2 - ζ.2)) x‖) :
    r ^ 2 / 64 < wz ζ x := by
  have h1 := wz_ge ζ x
  have hπ := pi_sq_lt
  have hπ0 := Real.pi_pos
  have h2 : (r / 2) ^ 2 ≤ ‖zc ζ (round (x.2 - ζ.2)) x‖ ^ 2 := pow_le_pow_left₀ (by positivity) h 2
  have : r ^ 2 / 64 < 4 / π ^ 2 * (r / 2) ^ 2 := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    nlinarith [sq_pos_of_pos hr]
  calc r ^ 2 / 64 < 4 / π ^ 2 * (r / 2) ^ 2 := this
    _ ≤ 4 / π ^ 2 * ‖zc ζ (round (x.2 - ζ.2)) x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ wz ζ x := h1

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: geometry of the zeros. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma continuous_zc (ζ : ℝ × ℝ) (m : ℤ) : Continuous (zc ζ m) := by
  have : zc ζ m = fun x => ((x.1 - ζ.1 : ℝ) : ℂ) + ((x.2 - ζ.2 - m : ℝ) : ℂ) * Complex.I := by
    funext x; apply Complex.ext <;> simp [zc]
  rw [this]; fun_prop

lemma pS_congr {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : f =ᶠ[𝓝 x] g) : pS f x = pS g x := by
  simp [pS, h.fderiv_eq]

lemma pT_congr {f g : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (h : f =ᶠ[𝓝 x] g) : pT f x = pT g x := by
  simp [pT, h.fderiv_eq]

lemma pS_fst (c : ℝ) (x : ℝ × ℝ) : pS (fun y => y.1 - c) x = 1 :=
  pS_eq_of_hasDerivAt (g := fun _ => 1) (contDiff_fst.sub contDiff_const)
    (fun s t => (hasDerivAt_id s).sub_const c) x

lemma pT_fst (c : ℝ) (x : ℝ × ℝ) : pT (fun y => y.1 - c) x = 0 :=
  pT_eq_of_hasDerivAt (g := fun _ => 0) (contDiff_fst.sub contDiff_const)
    (fun s t => hasDerivAt_const t (s - c)) x

lemma pS_snd (c : ℝ) (x : ℝ × ℝ) : pS (fun y => y.2 - c) x = 0 :=
  pS_eq_of_hasDerivAt (g := fun _ => 0) (contDiff_snd.sub contDiff_const)
    (fun s t => hasDerivAt_const s (t - c)) x

lemma pT_snd (c : ℝ) (x : ℝ × ℝ) : pT (fun y => y.2 - c) x = 1 :=
  pT_eq_of_hasDerivAt (g := fun _ => 1) (contDiff_snd.sub contDiff_const)
    (fun s t => (hasDerivAt_id t).sub_const c) x

lemma pS_neg_snd (c : ℝ) (x : ℝ × ℝ) : pS (fun y => -(y.2 - c)) x = 0 :=
  pS_eq_of_hasDerivAt (g := fun _ => 0) (contDiff_snd.sub contDiff_const).neg
    (fun s t => hasDerivAt_const s (-(t - c))) x

lemma pT_neg_snd (c : ℝ) (x : ℝ × ℝ) : pT (fun y => -(y.2 - c)) x = -1 :=
  pT_eq_of_hasDerivAt (g := fun _ => -1) (contDiff_snd.sub contDiff_const).neg
    (fun s t => ((hasDerivAt_id t).sub_const c).neg) x

section geometry

variable {β : ℝ × ℝ → ℂ} {Zplus Zminus : Finset (ℝ × ℝ)} {r : ℝ}

/-- The local normal form at a positive zero, on every copy of the disc. -/
lemma beta_plus (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Zplus) (m : ℤ) {x : ℝ × ℝ} (hx : ‖zc ζ m x‖ < r) :
    β x = zc ζ m x := by
  have h := hplusZ ζ hζ _ hx
  have e : (ζ.1 + (zc ζ m x).re, ζ.2 + (zc ζ m x).im) = (x.1, x.2 - m) := by
    simp [zc]; ring
  rw [e] at h
  have := per_int hβper x.1 (x.2 - m) m
  rw [sub_add_cancel] at this
  rw [← h, ← this]

lemma beta_minus (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Zminus) (m : ℤ) {x : ℝ × ℝ} (hx : ‖zc ζ m x‖ < r) :
    β x = (starRingEnd ℂ) (zc ζ m x) := by
  have h := hminusZ ζ hζ _ hx
  have e : (ζ.1 + (zc ζ m x).re, ζ.2 + (zc ζ m x).im) = (x.1, x.2 - m) := by
    simp [zc]; ring
  rw [e] at h
  have := per_int hβper x.1 (x.2 - m) m
  rw [sub_add_cancel] at this
  rw [← h, ← this]

lemma isOpen_disc (ζ : ℝ × ℝ) (m : ℤ) (r : ℝ) : IsOpen {y | ‖zc ζ m y‖ < r} :=
  isOpen_lt (continuous_norm.comp (continuous_zc ζ m)) continuous_const

/-- The derivatives of `Re β`, `Im β` near a positive zero. -/
lemma deriv_plus (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Zplus) (m : ℤ) {x : ℝ × ℝ} (hx : ‖zc ζ m x‖ < r) :
    pS (fun y => (β y).re) x = 1 ∧ pT (fun y => (β y).im) x = 1 ∧
      pS (fun y => (β y).im) x = 0 ∧ pT (fun y => (β y).re) x = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, β y = zc ζ m y :=
    Filter.eventually_of_mem ((isOpen_disc ζ m r).mem_nhds hx) fun y hy =>
      beta_plus hβper hplusZ hζ m hy
  have hr : (fun y => (β y).re) =ᶠ[𝓝 x] fun y => y.1 - ζ.1 :=
    hev.mono fun y hy => by simp [hy, zc]
  have hi : (fun y => (β y).im) =ᶠ[𝓝 x] fun y => y.2 - (ζ.2 + m) :=
    hev.mono fun y hy => by simp [hy, zc]; ring
  exact ⟨(pS_congr hr).trans (pS_fst _ x), (pT_congr hi).trans (pT_snd _ x),
    (pS_congr hi).trans (pS_snd _ x), (pT_congr hr).trans (pT_fst _ x)⟩

/-- The derivatives of `Re β`, `Im β` near a negative zero. -/
lemma deriv_minus (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Zminus) (m : ℤ) {x : ℝ × ℝ} (hx : ‖zc ζ m x‖ < r) :
    pS (fun y => (β y).re) x = 1 ∧ pT (fun y => (β y).im) x = -1 ∧
      pS (fun y => (β y).im) x = 0 ∧ pT (fun y => (β y).re) x = 0 := by
  have hev : ∀ᶠ y in 𝓝 x, β y = (starRingEnd ℂ) (zc ζ m y) :=
    Filter.eventually_of_mem ((isOpen_disc ζ m r).mem_nhds hx) fun y hy =>
      beta_minus hβper hminusZ hζ m hy
  have hr : (fun y => (β y).re) =ᶠ[𝓝 x] fun y => y.1 - ζ.1 :=
    hev.mono fun y hy => by simp [hy, zc]
  have hi : (fun y => (β y).im) =ᶠ[𝓝 x] fun y => -(y.2 - (ζ.2 + m)) :=
    hev.mono fun y hy => by simp [hy, zc]; ring
  exact ⟨(pS_congr hr).trans (pS_fst _ x), (pT_congr hi).trans (pT_neg_snd _ x),
    (pS_congr hi).trans (pS_neg_snd _ x), (pT_congr hr).trans (pT_fst _ x)⟩

/-- Two zeros (or two copies of one zero) are at distance at least `r`. -/
lemma zeros_sep (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    {ζ ζ' : ℝ × ℝ} (hζ : ζ ∈ Zplus ∪ Zminus) (hζ' : ζ' ∈ Zplus ∪ Zminus) (m : ℤ)
    (h : ‖zc ζ m ζ'‖ < r) : ζ' = ζ ∧ m = 0 := by
  have h0 : β ζ' = 0 := (hzero ζ').2 ⟨ζ', hζ', 0, by simp⟩
  have hz : zc ζ m ζ' = 0 := by
    rcases Finset.mem_union.1 hζ with hp | hm
    · rw [← beta_plus hβper hplusZ hp m h, h0]
    · have := beta_minus hβper hminusZ hm m h
      rw [h0] at this
      exact (map_eq_zero _).1 this.symm
  have h1 : ζ'.1 = ζ.1 := by
    have := congrArg Complex.re hz; simp [zc] at this; linarith
  have h2 : ζ'.2 = ζ.2 + m := by
    have := congrArg Complex.im hz; simp [zc] at this; linarith
  have hm0 : m = 0 := by
    obtain ⟨a1, a2⟩ := hZ ζ hζ
    obtain ⟨b1, b2⟩ := hZ ζ' hζ'
    have lo : (-1 : ℝ) < m := by linarith
    have hi : (m : ℝ) < 1 := by linarith
    have lo' : -1 < m := by exact_mod_cast lo
    have hi' : m < 1 := by exact_mod_cast hi
    omega
  subst hm0
  refine ⟨Prod.ext h1 (by simpa using h2), rfl⟩

lemma r_le_one (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Zplus ∪ Zminus) : r ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  have : ‖zc ζ (-1) ζ‖ < r := by
    have e : zc ζ (-1) ζ = Complex.I := by apply Complex.ext <;> simp [zc]
    rw [e, Complex.norm_I]; exact hlt
  have := (zeros_sep hβper hZ hzero hplusZ hminusZ hζ hζ (-1) this).2
  norm_num at this

/-- The supports of the cut-offs of two different zeros are disjoint. -/
lemma near_unique (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    (hr : 0 < r) {ζ ζ' : ℝ × ℝ} (hζ : ζ ∈ Zplus ∪ Zminus) (hζ' : ζ' ∈ Zplus ∪ Zminus)
    {x : ℝ × ℝ} (h1 : wz ζ x ≤ r ^ 2 / 64) (h2 : wz ζ' x ≤ r ^ 2 / 64) : ζ' = ζ := by
  have a1 := near_of_wz r hr h1
  have a2 := near_of_wz r hr h2
  set m := round (x.2 - ζ.2)
  set m' := round (x.2 - ζ'.2)
  have e : zc ζ (m - m') ζ' = zc ζ m x - zc ζ' m' x := by
    apply Complex.ext <;> simp [zc] <;> ring
  have : ‖zc ζ (m - m') ζ'‖ < r := by
    rw [e]
    calc ‖zc ζ m x - zc ζ' m' x‖ ≤ ‖zc ζ m x‖ + ‖zc ζ' m' x‖ := norm_sub_le _ _
      _ < r / 4 + r / 4 := add_lt_add a1 a2
      _ ≤ r := by linarith
  exact (zeros_sep hβper hZ hzero hplusZ hminusZ hζ hζ' _ this).1

end geometry

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the cut-off family. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

section family

variable {β : ℝ × ℝ → ℂ} {Zplus Zminus : Finset (ℝ × ℝ)} {r : ℝ}

/-- `|β|` is bounded below outside the inner discs. -/
lemma beta_lower (hβc : Continuous β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hr : 0 < r) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ x : ℝ × ℝ, (∀ ζ ∈ Zplus ∪ Zminus, r ^ 2 / 256 ≤ wz ζ x) →
      c₁ ≤ ‖β x‖ := by
  obtain ⟨R, c, hc, hends⟩ := hβends
  set O := {x : ℝ × ℝ | ∀ ζ ∈ Zplus ∪ Zminus, r ^ 2 / 256 ≤ wz ζ x} with hO
  have hOc : IsClosed O := by
    have : O = ⋂ ζ ∈ Zplus ∪ Zminus, {x | r ^ 2 / 256 ≤ wz ζ x} := by ext x; simp [hO]
    rw [this]
    exact isClosed_biInter fun ζ _ => isClosed_le continuous_const (contDiff_wz ζ).continuous
  have hne : ∀ x ∈ O, β x ≠ 0 := by
    intro x hx h0
    obtain ⟨ζ, hζ, m, rfl⟩ := (hzero x).1 h0
    have := hx ζ hζ
    have e : wz ζ (ζ.1, ζ.2 + m) = 0 := by
      simp only [wz, sub_self, add_sub_cancel_left]
      rw [show (m : ℝ) = 0 + m by ring, qf_int]
      simp [qf]
    rw [e] at this
    have : 0 < r ^ 2 / 256 := by positivity
    linarith
  set K := O ∩ (Icc (-R) R ×ˢ Icc (0 : ℝ) 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).inter_left hOc
  have hOper : ∀ s t, (s, t) ∈ O → (s, Int.fract t) ∈ O := by
    intro s t h ζ hζ
    have := h ζ hζ
    rwa [per_fract (wz_per ζ)]
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · refine ⟨c, hc, fun x hx => ?_⟩
    by_cases hs : R ≤ |x.1|
    · exact (hends x.1 x.2 hs).1
    · push_neg at hs
      exfalso
      have : (x.1, Int.fract x.2) ∈ K := ⟨hOper x.1 x.2 hx,
        ⟨by linarith [neg_abs_le x.1], by linarith [le_abs_self x.1]⟩,
        ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
      rw [hKe] at this; exact this
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKn (continuous_norm.comp hβc).continuousOn
    have hpos : 0 < ‖β x₀‖ := norm_pos_iff.2 (hne x₀ hx₀.1)
    refine ⟨min c ‖β x₀‖, lt_min hc hpos, fun x hx => ?_⟩
    by_cases hs : R ≤ |x.1|
    · exact (min_le_left _ _).trans (hends x.1 x.2 hs).1
    · push_neg at hs
      have hm : (x.1, Int.fract x.2) ∈ K := ⟨hOper x.1 x.2 hx,
        ⟨by linarith [neg_abs_le x.1], by linarith [le_abs_self x.1]⟩,
        ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
      have := hmin hm
      simp only [Function.comp, mem_setOf_eq] at this
      rw [per_fract hβper] at this
      exact (min_le_right _ _).trans this

/-- At most one cut-off is nonzero at a point, so `Σ χ_ζ² ≤ 1`. -/
lemma sum_chi_sq_le (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    (hr : 0 < r) (x : ℝ × ℝ) : ∑ ζ ∈ Zplus ∪ Zminus, chi r hr ζ x ^ 2 ≤ 1 := by
  by_cases h : ∃ ζ ∈ Zplus ∪ Zminus, chi r hr ζ x ≠ 0
  · obtain ⟨ζ₀, hζ₀, h0⟩ := h
    rw [Finset.sum_eq_single_of_mem ζ₀ hζ₀ fun ζ hζ hne => ?_]
    · have := chi_le_one r hr ζ₀ x
      have := chi_nonneg r hr ζ₀ x
      nlinarith
    · by_contra hc
      have hc' : chi r hr ζ x ≠ 0 := fun h' => hc (by rw [h']; ring)
      exact hne (near_unique hβper hZ hzero hplusZ hminusZ hr hζ₀ hζ
        (chi_ne_zero r hr h0).le (chi_ne_zero r hr hc').le)
  · push_neg at h
    rw [Finset.sum_eq_zero fun ζ hζ => by rw [h ζ hζ]; ring]
    norm_num

lemma pS_const (c : ℝ) (x : ℝ × ℝ) : pS (fun _ => c) x = 0 := by simp [pS]

lemma pT_const (c : ℝ) (x : ℝ × ℝ) : pT (fun _ => c) x = 0 := by simp [pT]

/-- The gradient of a cut-off lives outside the inner discs of all zeros. -/
lemma grad_chi_outside (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    (hr : 0 < r) {ζ : ℝ × ℝ} (hζ : ζ ∈ Zplus ∪ Zminus) {x : ℝ × ℝ}
    (hx : pS (chi r hr ζ) x ≠ 0 ∨ pT (chi r hr ζ) x ≠ 0) :
    ∀ ζ' ∈ Zplus ∪ Zminus, r ^ 2 / 256 ≤ wz ζ' x := by
  have h1 : r ^ 2 / 256 ≤ wz ζ x := by
    by_contra hlt
    push_neg at hlt
    have he := chi_eventually_one r hr hlt
    rcases hx with h | h
    · exact h ((pS_congr he).trans (pS_const 1 x))
    · exact h ((pT_congr he).trans (pT_const 1 x))
  have h2 : wz ζ x ≤ r ^ 2 / 64 := by
    by_contra hlt
    push_neg at hlt
    have he := chi_eventually_zero r hr hlt
    rcases hx with h | h
    · exact h ((pS_congr he).trans (pS_const 0 x))
    · exact h ((pT_congr he).trans (pT_const 0 x))
  intro ζ' hζ'
  by_contra hlt
  push_neg at hlt
  have := near_unique hβper hZ hzero hplusZ hminusZ hr hζ hζ' h2
    (hlt.le.trans (by nlinarith [sq_nonneg r]))
  subst this
  linarith

/-- Either the cut-off vanishes near `x`, or `x` is within `r/2` of a copy of `ζ`. -/
lemma chi_or_near (hr : 0 < r) (ζ x : ℝ × ℝ) :
    chi r hr ζ =ᶠ[𝓝 x] 0 ∨ ‖zc ζ (round (x.2 - ζ.2)) x‖ < r / 2 := by
  by_cases h : ‖zc ζ (round (x.2 - ζ.2)) x‖ < r / 2
  · exact Or.inr h
  · push_neg at h
    exact Or.inl (chi_eventually_zero r hr (wz_gt_of_far r hr h))

lemma round_eq_zero_of_near {ζ x : ℝ × ℝ} (hr1 : r ≤ 1)
    (h : ‖zc ζ (round (x.2 - ζ.2)) x‖ < r / 2) (hb : |x.2 - ζ.2| ≤ 1 / 2) :
    round (x.2 - ζ.2) = 0 := by
  set m := round (x.2 - ζ.2)
  have him := Complex.abs_im_le_norm (zc ζ m x)
  have e : (zc ζ m x).im = x.2 - ζ.2 - m := rfl
  rw [e] at him
  have h1 : |(m : ℝ)| < 1 := by
    have : (m : ℝ) = (x.2 - ζ.2) - (x.2 - ζ.2 - m) := by ring
    rw [this]
    calc |(x.2 - ζ.2) - (x.2 - ζ.2 - m)| ≤ |x.2 - ζ.2| + |x.2 - ζ.2 - m| := abs_sub _ _
      _ < 1 / 2 + r / 2 := by linarith
      _ ≤ 1 := by linarith
  have : |m| < 1 := by exact_mod_cast h1
  have := abs_lt.1 this
  omega

lemma chi_strip (hr : 0 < r) {ζ : ℝ × ℝ} {s t : ℝ} (h : chi r hr ζ (s, t) ≠ 0) :
    |s - ζ.1| < r / 8 := by
  have h1 := chi_ne_zero r hr h
  have h2 : (s - ζ.1) ^ 2 ≤ wz ζ (s, t) := by
    simp only [wz]; have : 0 ≤ qf (t - ζ.2) := by simp only [qf]; positivity
    linarith
  have h3 : (s - ζ.1) ^ 2 < (r / 8) ^ 2 := by nlinarith
  exact abs_lt_of_sq_lt_sq' h3 (by positivity) |> fun h => abs_lt.2 h

end family

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: localising a test section. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma IsTestSection.smul_fun {χ : ℝ × ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχp : PerT χ)
    {η : ℝ × ℝ → Vec 1} (hη : IsTestSection η) : IsTestSection fun x => χ x • η x := by
  obtain ⟨h1, h2, R, hR⟩ := hη
  refine ⟨hχ.smul h1, fun s t => by simp only [hχp s t, h2 s t], R, fun s t hs => by
    simp [hR s t hs]⟩

lemma partialS_smul_fun {χ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ) {η : ℝ × ℝ → Vec 1}
    (hη : Differentiable ℝ η) (x : ℝ × ℝ) :
    partialS (fun x => χ x • η x) x = χ x • partialS η x + pS χ x • η x := by
  have : (fun x => χ x • η x) = χ • η := rfl
  rw [partialS, this, fderiv_smul (hχ x) (hη x)]
  simp [partialS, pS]

lemma partialT_smul_fun {χ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ) {η : ℝ × ℝ → Vec 1}
    (hη : Differentiable ℝ η) (x : ℝ × ℝ) :
    partialT (fun x => χ x • η x) x = χ x • partialT η x + pT χ x • η x := by
  have : (fun x => χ x • η x) = χ • η := rfl
  rw [partialT, this, fderiv_smul (hχ x) (hη x)]
  simp [partialT, pT]

lemma coord_smul_fun (χ : ℝ × ℝ → ℝ) (η : ℝ × ℝ → Vec 1) (i) (x : ℝ × ℝ) :
    coord (fun x => χ x • η x) i x = χ x * coord η i x := by
  simp [coord]

lemma crOp_smul_eq (S : ℝ × ℝ → Mat 1) {χ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {η : ℝ × ℝ → Vec 1} (hη : Differentiable ℝ η) (x : ℝ × ℝ) :
    crOp S (fun x => χ x • η x) x =
      χ x • crOp S η x + (pS χ x • η x + pT χ x • Matrix.toEuclideanLin (J₀ 1) (η x)) := by
  simp only [crOp, partialS_smul_fun hχ hη, partialT_smul_fun hχ hη, map_add, map_smul]
  module

lemma norm_grad_part (p q : ℝ) (v : Vec 1) :
    ‖p • v + q • Matrix.toEuclideanLin (J₀ 1) v‖ ^ 2 = (p ^ 2 + q ^ 2) * ‖v‖ ^ 2 := by
  rw [norm_sq_vec1, norm_sq_vec1]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, J_apply₁, J_apply₂]
  ring

/-- `‖D_σ(χ η)‖² ≤ 2 χ² ‖D_σ η‖² + 2 |∇χ|² |η|²`, pointwise. -/
lemma crOp_smul_le (S : ℝ × ℝ → Mat 1) {χ : ℝ × ℝ → ℝ} (hχ : Differentiable ℝ χ)
    {η : ℝ × ℝ → Vec 1} (hη : Differentiable ℝ η) (x : ℝ × ℝ) :
    ‖crOp S (fun x => χ x • η x) x‖ ^ 2 ≤
      2 * (χ x ^ 2 * ‖crOp S η x‖ ^ 2) + 2 * ((pS χ x ^ 2 + pT χ x ^ 2) * ‖η x‖ ^ 2) := by
  rw [crOp_smul_eq S hχ hη, ← norm_grad_part]
  set a := χ x • crOp S η x
  set b := pS χ x • η x + pT χ x • Matrix.toEuclideanLin (J₀ 1) (η x)
  have ha : ‖a‖ ^ 2 = χ x ^ 2 * ‖crOp S η x‖ ^ 2 := by
    simp only [a, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [← ha]
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h0 : 0 ≤ ‖a + b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

end

end CauchyRiemannIndex

/-! Large antilinear perturbations, kernel bound: the coercive estimate on test sections. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma continuous_crOp {S : ℝ × ℝ → Mat 1} (hS : Continuous S) {u : ℝ × ℝ → Vec 1}
    (hu : IsTestSection u) : Continuous (crOp S u) := by
  have h1 := hu.continuous_partialS
  have h2 := hu.continuous_partialT
  have h3 := hu.continuous
  have hJ : Continuous fun x => Matrix.toEuclideanLin (J₀ 1) (partialT u x) :=
    (matCLM 1 (J₀ 1)).continuous.comp h2
  have hSu : Continuous fun x => Matrix.toEuclideanLin (S x) (u x) :=
    (continuous_matCLM.comp hS).clm_apply h3
  exact (h1.add hJ).add hSu

lemma IsTestSection.vanS_norm {u : ℝ × ℝ → Vec 1} (hu : IsTestSection u) :
    ∃ R, ∀ s t, R < |s| → u (s, t) = 0 := hu.2.2

/-- The cut-off of `ζ` vanishes for `|s| > |ζ.1| + r`. -/
lemma chi_vanS {r : ℝ} (hr : 0 < r) (ζ : ℝ × ℝ) : VanS (|ζ.1| + r) (chi r hr ζ) := by
  intro s t hs
  by_contra h
  have := chi_strip hr h
  have : |s| ≤ |ζ.1| + r / 8 := by
    have := abs_sub_abs_le_abs_sub s ζ.1
    linarith
  linarith

lemma box_mass_pos (σ a b : ℝ) :
    0 < ∫ x in box a b, Real.exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2)) := by
  have : NeZero (volume.restrict (box a b)) := ⟨by
    rw [Ne, Measure.restrict_eq_zero, Measure.volume_eq_prod, Measure.prod_prod,
      Real.volume_Icc, Real.volume_Icc]
    norm_num⟩
  exact integral_exp_pos ((by fun_prop : Continuous fun x : ℝ × ℝ =>
    Real.exp (-σ * ((x.1 - a) ^ 2 + (x.2 - b) ^ 2))).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc))

section local_est

variable {β : ℝ × ℝ → ℂ} {Zplus Zminus : Finset (ℝ × ℝ)} {r : ℝ}

/-- Localised estimate at a negative zero. -/
lemma local_minus (σ : ℝ) (hσ : 1 ≤ σ) (hβ : ContDiff ℝ ∞ β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z)
    (hr : 0 < r) {ζ : ℝ × ℝ} (hζ : ζ ∈ Zminus) {η : ℝ × ℝ → Vec 1} (hη : IsTestSection η) :
    ∫ x, ‖chi r hr ζ x • η x‖ ^ 2 ∂cylMeasure ≤
      8 / σ * ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) (fun x => chi r hr ζ x • η x) x‖ ^ 2
        ∂cylMeasure := by
  have hU := hη.smul_fun (contDiff_chi r hr ζ) (chi_per r hr ζ)
  have h := D0_neg σ (by linarith) (hβ.of_le (by exact_mod_cast le_top)) hβper hU (fun x => by
    rcases chi_or_near hr ζ x with h | h
    · exact Or.inl (h.mono fun y hy => by simp [show chi r hr ζ y = 0 from hy])
    · exact Or.inr (deriv_minus hβper hminusZ hζ _ (h.trans (half_lt_self hr))))
  have hD : 0 ≤ ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) (fun x => chi r hr ζ x • η x) x‖ ^ 2
      ∂cylMeasure := integral_nonneg fun x => sq_nonneg _
  have hσ0 : 0 < σ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hσ0]
  nlinarith

/-- Localised estimate at a positive zero. -/
lemma local_plus (σ : ℝ) (hσ : 1 ≤ σ) (hβ : ContDiff ℝ ∞ β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hr : 0 < r) (hr1 : r ≤ 1) {ζ : ℝ × ℝ} (hζ : ζ ∈ Zplus) {η : ℝ × ℝ → Vec 1}
    (hη : IsTestSection η) :
    ∫ x, ‖chi r hr ζ x • η x‖ ^ 2 ∂cylMeasure ≤
      8 / σ * ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) (fun x => chi r hr ζ x • η x) x‖ ^ 2
        ∂cylMeasure +
      (∫ x, Real.exp (-σ * ((β x).re ^ 2 + (β x).im ^ 2) / 2) * (chi r hr ζ x * η x i₁)
        ∂cylMeasure) ^ 2 /
        ∫ x in box ζ.1 ζ.2, Real.exp (-σ * ((x.1 - ζ.1) ^ 2 + (x.2 - ζ.2) ^ 2)) := by
  have hU := hη.smul_fun (contDiff_chi r hr ζ) (chi_per r hr ζ)
  have hσ0 : 0 < σ := by linarith
  have h := D0_pos_gap σ hσ0 (hβ.of_le (WithTop.coe_le_coe.2 le_top)) hβper hU ζ.1 ζ.2 (fun x => by
    rcases chi_or_near hr ζ x with h | h
    · exact Or.inl (h.mono fun y hy => by simp [show chi r hr ζ y = 0 from hy])
    · right
      have hlt : ‖zc ζ (round (x.2 - ζ.2)) x‖ < r := h.trans (half_lt_self hr)
      obtain ⟨d1, d2, d3, d4⟩ := deriv_plus hβper hplusZ hζ _ hlt
      refine ⟨d1, d2, d3, d4, fun hb => ?_⟩
      have h0 := round_eq_zero_of_near hr1 h hb
      rw [h0] at hlt
      have := beta_plus hβper hplusZ hζ 0 hlt
      rw [this]
      simp [zc]) (fun s t hs => by
    by_contra hne
    have : chi r hr ζ (s, t) ≠ 0 := fun h0 => hne (by simp [h0])
    have := chi_strip hr this
    linarith)
  have e : ∀ x, coord (fun x => chi r hr ζ x • η x) i₁ x = chi r hr ζ x * η x i₁ := fun x => by
    simp [coord]
  simp only [e] at h
  set N := ∫ x in box ζ.1 ζ.2, Real.exp (-σ * ((x.1 - ζ.1) ^ 2 + (x.2 - ζ.2) ^ 2))
  set D := ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) (fun x => chi r hr ζ x • η x) x‖ ^ 2
    ∂cylMeasure
  set u := ∫ x, ‖chi r hr ζ x • η x‖ ^ 2 ∂cylMeasure
  set L := (∫ x, Real.exp (-σ * ((β x).re ^ 2 + (β x).im ^ 2) / 2) * (chi r hr ζ x * η x i₁)
        ∂cylMeasure) ^ 2 / N
  have : u - L ≤ 8 / σ * D := by
    have h8 : 8 / σ * (σ / 8 * (u - L)) = u - L := by field_simp
    rw [← h8]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  linarith

end local_est

lemma final_arith {σ X Y a Sp K Nn C' c₁ : ℝ} (hσ1 : 1 ≤ σ) (hc₁ : 0 < c₁) (hX0 : 0 ≤ X)
    (ha0 : 0 ≤ a) (hY0 : 0 ≤ Y) (hσK : 16 * K * Nn ≤ σ) (hσC : 16 * C' / c₁ ^ 2 ≤ σ)
    (hX : X ≤ 8 / σ * (2 * Y + 2 * K * Nn * a) + Sp + a)
    (hglob : σ ^ 2 * (c₁ ^ 2 * a) ≤ Y + 4 * C' * σ * X) :
    X ≤ (32 + 4 / c₁ ^ 2) / σ * Y + 2 * Sp := by
  have hσ0 : 0 < σ := by linarith
  have hc2 : 0 < c₁ ^ 2 := by positivity
  have e1 : σ * X ≤ 16 * Y + 2 * (σ * a) + σ * Sp := by
    have h := mul_le_mul_of_nonneg_left hX hσ0.le
    have h' : σ * (8 / σ * (2 * Y + 2 * K * Nn * a) + Sp + a) =
        16 * Y + 16 * K * Nn * a + σ * Sp + σ * a := by field_simp; ring
    rw [h'] at h
    nlinarith [mul_le_mul_of_nonneg_right hσK ha0]
  have h16 : 16 * C' ≤ σ * c₁ ^ 2 := by rwa [div_le_iff₀ hc2] at hσC
  have e2 : (σ * c₁ ^ 2) * (2 * (σ * a)) ≤ 2 * Y + (σ * c₁ ^ 2) * (σ * X / 2) := by
    nlinarith [hglob, mul_le_mul_of_nonneg_right h16 (mul_nonneg hσ0.le hX0)]
  have hM : 0 < σ * c₁ ^ 2 := by positivity
  have e3 : 2 * (σ * a) ≤ 2 * Y / (σ * c₁ ^ 2) + σ * X / 2 := by
    rw [show 2 * Y / (σ * c₁ ^ 2) + σ * X / 2 = (2 * Y + (σ * c₁ ^ 2) * (σ * X / 2)) / (σ * c₁ ^ 2)
      by field_simp, le_div_iff₀ hM]
    linarith
  have e5 : 4 * Y / (σ * c₁ ^ 2) ≤ 4 * Y / c₁ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) hc2 (by nlinarith)
  have e4 : σ * X ≤ (32 + 4 / c₁ ^ 2) * Y + σ * (2 * Sp) := by
    have : 2 * (2 * Y / (σ * c₁ ^ 2)) = 4 * Y / (σ * c₁ ^ 2) := by ring
    have : 4 / c₁ ^ 2 * Y = 4 * Y / c₁ ^ 2 := by ring
    nlinarith
  rw [div_mul_eq_mul_div, ← sub_le_iff_le_add, le_div_iff₀ hσ0]
  nlinarith



/-- The coercive estimate for `∂ₛ + J₀∂ₜ + σ A(β)` on test sections. -/
theorem large_antilinear_coercive_estimate_aux (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z) :
    ∃ A σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ ≥ σ₀, ∃ Φ : ℝ × ℝ → ℝ × ℝ → Vec 1,
      (∀ ζ ∈ Zplus, IsTestSection (Φ ζ)) ∧
      ∀ η : ℝ × ℝ → Vec 1, IsTestSection η →
        ∫ x, ‖η x‖ ^ 2 ∂cylMeasure ≤
          A / σ * ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) η x‖ ^ 2 ∂cylMeasure +
            ∑ ζ ∈ Zplus, (∫ x, ⟪Φ ζ x, η x⟫ ∂cylMeasure) ^ 2 := by
  set Z := Zplus ∪ Zminus with hZdef
  obtain ⟨C, hC⟩ := hβC1
  set C' := max C 0
  have hC' : ∀ x, ‖fderiv ℝ β x‖ ≤ C' := fun x => (hC x).trans (le_max_left _ _)
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨c₁, hc₁, hlow⟩ := beta_lower hβ.continuous hβper hβends hzero hr
  have hr1 : ∀ ζ ∈ Z, r ≤ 1 := fun ζ hζ => r_le_one hβper hZ hzero hplusZ hminusZ hζ
  -- uniform bound on the gradients of the cut-offs
  have hBex : ∀ ζ : ℝ × ℝ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ x, pS (chi r hr ζ) x ^ 2 + pT (chi r hr ζ) x ^ 2 ≤ B := by
    intro ζ
    have c1 : ContDiff ℝ 1 (chi r hr ζ) := (contDiff_chi r hr ζ).of_le (by exact_mod_cast le_top)
    obtain ⟨B1, hB1, h1⟩ := bounded_of_per_van (continuous_pS c1)
      (fun s t => pS_periodic c1 (chi_per r hr ζ) s t) (chi_vanS hr ζ).pS
    obtain ⟨B2, hB2, h2⟩ := bounded_of_per_van (continuous_pT c1)
      (fun s t => pT_periodic c1 (chi_per r hr ζ) s t) (chi_vanS hr ζ).pT
    refine ⟨B1 ^ 2 + B2 ^ 2, by positivity, fun x => ?_⟩
    have a1 : pS (chi r hr ζ) x ^ 2 ≤ B1 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1 x) 2
    have a2 : pT (chi r hr ζ) x ^ 2 ≤ B2 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2 x) 2
    linarith
  choose B hB0 hB using hBex
  set K := ∑ ζ ∈ Z, B ζ
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun ζ _ => hB0 ζ
  have hBK : ∀ ζ ∈ Z, B ζ ≤ K := fun ζ hζ =>
    Finset.single_le_sum (f := B) (fun ζ _ => hB0 ζ) hζ
  set O := {x : ℝ × ℝ | ∀ ζ ∈ Z, r ^ 2 / 256 ≤ wz ζ x} with hO
  have hOm : MeasurableSet O := by
    have : O = ⋂ ζ ∈ Z, {x | r ^ 2 / 256 ≤ wz ζ x} := by ext x; simp [hO]
    rw [this]
    exact (isClosed_biInter fun ζ _ =>
      isClosed_le continuous_const (contDiff_wz ζ).continuous).measurableSet
  have hgrad : ∀ ζ ∈ Z, ∀ x, pS (chi r hr ζ) x ^ 2 + pT (chi r hr ζ) x ^ 2 ≤
      K * O.indicator (fun _ => (1 : ℝ)) x := by
    intro ζ hζ x
    by_cases hx : pS (chi r hr ζ) x ≠ 0 ∨ pT (chi r hr ζ) x ≠ 0
    · have hxO : x ∈ O := grad_chi_outside hβper hZ hzero hplusZ hminusZ hr hζ hx
      rw [indicator_of_mem hxO, mul_one]
      exact (hB ζ x).trans (hBK ζ hζ)
    · push_neg at hx
      rw [hx.1, hx.2]
      have : 0 ≤ O.indicator (fun _ => (1 : ℝ)) x := indicator_nonneg (fun _ _ => zero_le_one) x
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      positivity
  set Nn : ℝ := (Z.card : ℝ)
  have hNn : 0 ≤ Nn := Nat.cast_nonneg _
  refine ⟨32 + 4 / c₁ ^ 2, max 1 (max (16 * K * Nn) (16 * C' / c₁ ^ 2)), by positivity,
    fun σ hσ => ?_⟩
  have hσ1 : 1 ≤ σ := (le_max_left _ _).trans hσ
  have hσK : 16 * K * Nn ≤ σ := ((le_max_left _ _).trans (le_max_right _ _)).trans hσ
  have hσC : 16 * C' / c₁ ^ 2 ≤ σ := ((le_max_right _ _).trans (le_max_right _ _)).trans hσ
  have hσ0 : 0 < σ := by linarith
  set G : ℝ × ℝ → ℝ := fun x => Real.exp (-σ * ((β x).re ^ 2 + (β x).im ^ 2) / 2) with hG
  have cG : ContDiff ℝ ∞ G := by
    have h1 := re_contDiff hβ
    have h2 := im_contDiff hβ
    exact ((contDiff_const.mul ((h1.pow 2).add (h2.pow 2))).div_const _).exp
  have pG : PerT G := fun s t => by simp only [hG, hβper s t]
  set Nz : ℝ × ℝ → ℝ := fun ζ =>
    ∫ x in box ζ.1 ζ.2, Real.exp (-σ * ((x.1 - ζ.1) ^ 2 + (x.2 - ζ.2) ^ 2)) with hNz
  have hNz : ∀ ζ, 0 < Nz ζ := fun ζ => box_mass_pos σ ζ.1 ζ.2
  set e₁ : Vec 1 := EuclideanSpace.single i₁ 1
  refine ⟨fun ζ x => (Real.sqrt (2 / Nz ζ) * G x * chi r hr ζ x) • e₁, fun ζ _ => ?_,
    fun η hη => ?_⟩
  · refine ⟨((contDiff_const.mul cG).mul (contDiff_chi r hr ζ)).smul contDiff_const,
      fun s t => by simp only [pG s t, chi_per r hr ζ s t], |ζ.1| + r, fun s t hs => ?_⟩
    simp [chi_vanS hr ζ s t hs]
  -- the estimate for a test section `η`
  obtain ⟨Rη, hRη⟩ := hη.2.2
  have hηd : Differentiable ℝ η := hη.1.differentiable (by simp)
  have cAm : Continuous antilinearMat := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat, Matrix.fromBlocks] <;>
      fun_prop
  set S : ℝ × ℝ → Mat 1 := fun x => σ • antilinearMat (β x) with hS
  have cS : Continuous S := (cAm.comp hβ.continuous).const_smul σ
  have cη : Continuous fun x => ‖η x‖ ^ 2 := (continuous_norm.comp hη.continuous).pow 2
  have cD : Continuous fun x => ‖crOp S η x‖ ^ 2 := (continuous_norm.comp (continuous_crOp cS hη)).pow 2
  have vη : VanS Rη fun x => ‖η x‖ ^ 2 := fun s t hs => by simp [hRη s t hs]
  have vD : VanS Rη fun x => ‖crOp S η x‖ ^ 2 := fun s t hs => by
    simp [crOp, hRη s t hs, partialS_eq_zero Rη hRη hs, partialT_eq_zero Rη hRη hs]
  have iη : Integrable (fun x => ‖η x‖ ^ 2) cylMeasure := vη.integrable cη
  have iD : Integrable (fun x => ‖crOp S η x‖ ^ 2) cylMeasure := vD.integrable cD
  have iO : Integrable (O.indicator fun x => ‖η x‖ ^ 2) cylMeasure := iη.indicator hOm
  have hU : ∀ ζ, IsTestSection fun x => chi r hr ζ x • η x := fun ζ =>
    hη.smul_fun (contDiff_chi r hr ζ) (chi_per r hr ζ)
  have cχ : ∀ ζ, Continuous (chi r hr ζ) := fun ζ => (contDiff_chi r hr ζ).continuous
  have iu : ∀ ζ, Integrable (fun x => ‖chi r hr ζ x • η x‖ ^ 2) cylMeasure := fun ζ =>
    VanS.integrable (R := Rη) (fun s t hs => by simp [hRη s t hs])
      ((continuous_norm.comp ((cχ ζ).smul hη.continuous)).pow 2)
  have iχD : ∀ ζ, Integrable (fun x => chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2) cylMeasure := fun ζ =>
    VanS.integrable (R := Rη) (fun s t hs => by
      rw [show ‖crOp S η (s, t)‖ ^ 2 = 0 from vD s t hs, mul_zero]) (((cχ ζ).pow 2).mul cD)
  set Y := ∫ x, ‖crOp S η x‖ ^ 2 ∂cylMeasure
  set X := ∫ x, ‖η x‖ ^ 2 ∂cylMeasure
  set a := ∫ x, O.indicator (fun x => ‖η x‖ ^ 2) x ∂cylMeasure
  set u : ℝ × ℝ → ℝ := fun ζ => ∫ x, ‖chi r hr ζ x • η x‖ ^ 2 ∂cylMeasure
  set Dz : ℝ × ℝ → ℝ := fun ζ => ∫ x, ‖crOp S (fun x => chi r hr ζ x • η x) x‖ ^ 2 ∂cylMeasure
  set ℓ : ℝ × ℝ → ℝ := fun ζ => ∫ x, G x * (chi r hr ζ x * η x i₁) ∂cylMeasure
  have hY0 : 0 ≤ Y := integral_nonneg fun x => sq_nonneg _
  have hX0 : 0 ≤ X := integral_nonneg fun x => sq_nonneg _
  have ha0 : 0 ≤ a := integral_nonneg fun x => indicator_nonneg (fun x _ => sq_nonneg _) x
  -- (1) covering
  have hcover : X ≤ ∑ ζ ∈ Z, u ζ + a := by
    simp only [u]
    rw [← integral_finsetSum Z (fun ζ _ => iu ζ), ← integral_add (integrable_finset_sum Z
      (fun ζ _ => iu ζ)) iO]
    refine integral_mono iη ((integrable_finset_sum Z (fun ζ _ => iu ζ)).add iO) fun x => ?_
    have hs0 : 0 ≤ ∑ ζ ∈ Z, ‖chi r hr ζ x • η x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    by_cases hx : x ∈ O
    · simp only [indicator_of_mem hx]; linarith
    · simp only [indicator_of_notMem hx, add_zero]
      simp only [hO, mem_setOf_eq, not_forall, not_le] at hx
      obtain ⟨ζ, hζ, hlt⟩ := hx
      have h1 : chi r hr ζ x = 1 := chi_eq_one r hr hlt.le
      calc ‖η x‖ ^ 2 = ‖chi r hr ζ x • η x‖ ^ 2 := by rw [h1, one_smul]
        _ ≤ ∑ ζ ∈ Z, ‖chi r hr ζ x • η x‖ ^ 2 :=
          Finset.single_le_sum (f := fun ζ => ‖chi r hr ζ x • η x‖ ^ 2) (fun _ _ => sq_nonneg _) hζ
  -- (3) cut-off error
  have hcut : ∀ ζ ∈ Z, Dz ζ ≤ 2 * ∫ x, chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2 ∂cylMeasure + 2 * K * a := by
    intro ζ hζ
    have hχd : Differentiable ℝ (chi r hr ζ) := (contDiff_chi r hr ζ).differentiable (by simp)
    have iR : Integrable (fun x => 2 * (chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2) +
        2 * K * O.indicator (fun x => ‖η x‖ ^ 2) x) cylMeasure :=
      ((iχD ζ).const_mul 2).add (iO.const_mul _)
    have hle : Dz ζ ≤ ∫ x, (2 * (chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2) +
        2 * K * O.indicator (fun x => ‖η x‖ ^ 2) x) ∂cylMeasure := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) iR
        (Eventually.of_forall fun x => ?_)
      have h1 := crOp_smul_le S hχd hηd x
      have h2 := hgrad ζ hζ x
      have h3 : (pS (chi r hr ζ) x ^ 2 + pT (chi r hr ζ) x ^ 2) * ‖η x‖ ^ 2 ≤
          K * O.indicator (fun x => ‖η x‖ ^ 2) x := by
        by_cases hx : x ∈ O
        · simp only [indicator_of_mem hx] at h2 ⊢
          nlinarith [sq_nonneg ‖η x‖]
        · simp only [indicator_of_notMem hx, mul_zero] at h2 ⊢
          nlinarith [sq_nonneg ‖η x‖, sq_nonneg (pS (chi r hr ζ) x), sq_nonneg (pT (chi r hr ζ) x)]
      linarith
    rw [integral_add ((iχD ζ).const_mul 2) (iO.const_mul _), integral_const_mul,
      integral_const_mul] at hle
    exact hle
  -- (4) the cut-offs square-sum to at most one
  have hsum : ∑ ζ ∈ Z, ∫ x, chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2 ∂cylMeasure ≤ Y := by
    rw [← integral_finsetSum Z (fun ζ _ => iχD ζ)]
    refine integral_mono (integrable_finset_sum Z fun ζ _ => iχD ζ) iD fun x => ?_
    rw [← Finset.sum_mul]
    have := sum_chi_sq_le hβper hZ hzero hplusZ hminusZ hr x
    nlinarith [sq_nonneg ‖crOp S η x‖]
  -- (5) outside the inner discs
  have hglob : σ ^ 2 * (c₁ ^ 2 * a) ≤ Y + 4 * C' * σ * X := by
    have h1 := D0_global σ hσ0.le (hβ.of_le (by exact_mod_cast le_top)) hβper hC' hη
    have h2 : c₁ ^ 2 * a ≤ ∫ x, ‖β x‖ ^ 2 * ‖η x‖ ^ 2 ∂cylMeasure := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_) ?_
        (Eventually.of_forall fun x => ?_)
      · exact mul_nonneg (sq_nonneg _) (indicator_nonneg (fun x _ => sq_nonneg _) x)
      · exact VanS.integrable (R := Rη) (fun s t hs => by simp [hRη s t hs])
          (((continuous_norm.comp hβ.continuous).pow 2).mul cη)
      · by_cases hx : x ∈ O
        · simp only [indicator_of_mem hx]
          have := hlow x hx
          have : c₁ ^ 2 ≤ ‖β x‖ ^ 2 := pow_le_pow_left₀ hc₁.le this 2
          nlinarith [sq_nonneg ‖η x‖]
        · simp only [indicator_of_notMem hx, mul_zero]; positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 (sq_nonneg σ)]
  -- (2) local estimates, summed
  have hlocP : ∀ ζ ∈ Zplus, u ζ ≤ 8 / σ * Dz ζ + ℓ ζ ^ 2 / Nz ζ := fun ζ hζ =>
    local_plus σ hσ1 hβ hβper hplusZ hr (hr1 ζ (Finset.mem_union_left _ hζ)) hζ hη
  have hlocM : ∀ ζ ∈ Zminus, u ζ ≤ 8 / σ * Dz ζ := fun ζ hζ =>
    local_minus σ hσ1 hβ hβper hminusZ hr hζ hη
  set Sp := ∑ ζ ∈ Zplus, ℓ ζ ^ 2 / Nz ζ
  have hsu : ∑ ζ ∈ Z, u ζ ≤ 8 / σ * ∑ ζ ∈ Z, Dz ζ + Sp := by
    rw [hZdef, Finset.sum_union hdisj, Finset.sum_union hdisj, mul_add]
    have h1 : ∑ ζ ∈ Zplus, u ζ ≤ ∑ ζ ∈ Zplus, (8 / σ * Dz ζ + ℓ ζ ^ 2 / Nz ζ) :=
      Finset.sum_le_sum hlocP
    have h2 : ∑ ζ ∈ Zminus, u ζ ≤ ∑ ζ ∈ Zminus, 8 / σ * Dz ζ := Finset.sum_le_sum hlocM
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    rw [← Finset.mul_sum] at h2
    linarith
  have hsD : ∑ ζ ∈ Z, Dz ζ ≤ 2 * Y + 2 * K * Nn * a := by
    have h1 : ∑ ζ ∈ Z, Dz ζ ≤ ∑ ζ ∈ Z,
        (2 * ∫ x, chi r hr ζ x ^ 2 * ‖crOp S η x‖ ^ 2 ∂cylMeasure + 2 * K * a) :=
      Finset.sum_le_sum hcut
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h1
    have : (Z.card : ℝ) * (2 * K * a) = 2 * K * Nn * a := by simp only [Nn]; ring
    nlinarith
  have hX : X ≤ 8 / σ * (2 * Y + 2 * K * Nn * a) + Sp + a := by
    have h8 : 8 / σ * ∑ ζ ∈ Z, Dz ζ ≤ 8 / σ * (2 * Y + 2 * K * Nn * a) :=
      mul_le_mul_of_nonneg_left hsD (by positivity)
    linarith
  -- (6) the correction functionals
  have hΦ : ∀ ζ ∈ Zplus, (∫ x, ⟪(Real.sqrt (2 / Nz ζ) * G x * chi r hr ζ x) • e₁, η x⟫ ∂cylMeasure) ^ 2
      = 2 * (ℓ ζ ^ 2 / Nz ζ) := by
    intro ζ _
    have e : ∀ x, ⟪(Real.sqrt (2 / Nz ζ) * G x * chi r hr ζ x) • e₁, η x⟫ =
        Real.sqrt (2 / Nz ζ) * (G x * (chi r hr ζ x * η x i₁)) := by
      intro x
      rw [real_inner_smul_left, EuclideanSpace.inner_single_left]
      simp only [map_one, one_mul]
      ring
    simp only [e]
    rw [integral_const_mul, mul_pow, Real.sq_sqrt (by have := hNz ζ; positivity)]
    ring
  rw [Finset.sum_congr rfl hΦ, ← Finset.mul_sum]
  exact final_arith hσ1 hc₁ hX0 ha0 hY0 hσK hσC hX hglob

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z) :
    ∃ A σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ ≥ σ₀, ∃ Φ : ℝ × ℝ → ℝ × ℝ → Vec 1,
      (∀ ζ ∈ Zplus, IsTestSection (Φ ζ)) ∧
      ∀ η : ℝ × ℝ → Vec 1, IsTestSection η →
        ∫ x, ‖η x‖ ^ 2 ∂cylMeasure ≤
          A / σ * ∫ x, ‖crOp (fun x => σ • antilinearMat (β x)) η x‖ ^ 2 ∂cylMeasure +
            ∑ ζ ∈ Zplus, (∫ x, ⟪Φ ζ x, η x⟫ ∂cylMeasure) ^ 2 :=
  large_antilinear_coercive_estimate_aux β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ
