-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_kernel_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:27:48.496366+00:00
-- url     : https://prove2.me/submissions/aa92b892-42c4-4852-aa3d-86e3a8c5382c

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_CauchyRiemannIndex_large_antilinear_coercive_estimate
import Mathlib.MeasureTheory.Function.L2Space



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

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The triple `(u, ∂ₛu, ∂ₜu)` of a test section. -/
def testTriple {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : Triple n p :=
  ((hu.memLp (p := p)).toLp u, (hu.memLp_partialS (p := p)).toLp _, (hu.memLp_partialT (p := p)).toLp _)

lemma testTriple_mem {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    testTriple (p := p) hu ∈ testTriples n p :=
  ⟨u, hu, (hu.memLp (p := p)).coeFn_toLp, (hu.memLp_partialS (p := p)).coeFn_toLp,
    (hu.memLp_partialT (p := p)).coeFn_toLp⟩

lemma span_testTriples_subset :
    (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) ⊆ testTriples n p := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero =>
    refine ⟨0, isTestSection_zero, ?_, ?_, ?_⟩
    · exact Lp.coeFn_zero _ _ _
    · rw [partialS_zero]; exact Lp.coeFn_zero _ _ _
    · rw [partialT_zero]; exact Lp.coeFn_zero _ _ _
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    obtain ⟨v, hv, k1, k2, k3⟩ := hy
    refine ⟨u + v, hu.add hv, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_add x.1 y.1).trans (h1.add k1)
    · rw [partialS_add hu hv]; exact (Lp.coeFn_add x.2.1 y.2.1).trans (h2.add k2)
    · rw [partialT_add hu hv]; exact (Lp.coeFn_add x.2.2 y.2.2).trans (h3.add k3)
  | smul c x _ hx =>
    obtain ⟨u, hu, h1, h2, h3⟩ := hx
    refine ⟨c • u, hu.smul c, ?_, ?_, ?_⟩
    · exact (Lp.coeFn_smul c x.1).trans (h1.const_smul c)
    · rw [partialS_smul hu]; exact (Lp.coeFn_smul c x.2.1).trans (h2.const_smul c)
    · rw [partialT_smul hu]; exact (Lp.coeFn_smul c x.2.2).trans (h3.const_smul c)

lemma crApply_ae_crOp (S : ℝ × ℝ → Mat n) {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    crApply S w =ᵐ[cylMeasure] crOp S u := by
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  simp only [crApply, crOp, e1, e2, e3]

lemma ofReal_norm_le_w1pNorm {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    ENNReal.ofReal ‖w‖ ≤ w1pNorm p u := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  rw [Prod.norm_def, Prod.norm_def, ENNReal.ofReal_max, ENNReal.ofReal_max, e1, e2, e3]
  unfold w1pNorm
  refine max_le ?_ (max_le ?_ ?_)
  · exact le_add_right (le_add_right le_rfl)
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

lemma eLpNorm_const_mul_norm_le (g : LpCyl n p) {c : ℝ} (hc : 0 ≤ c) :
    eLpNorm (fun x => c * ‖g x‖) p cylMeasure ≤ ENNReal.ofReal c * ENNReal.ofReal ‖g‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) p
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc (norm_nonneg _))]

lemma eLpNorm_le_of_pointwise {F : ℝ × ℝ → Vec n} {w : Triple n p} {M MJ : ℝ}
    (hM : 0 ≤ M) (hMJ : 0 ≤ MJ)
    (hF : ∀ᵐ x ∂cylMeasure, ‖F x‖ ≤ 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) :
    eLpNorm F p cylMeasure ≤ ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
  have hp1 : 1 ≤ p := Fact.out
  have m1 : AEStronglyMeasurable (fun x => 1 * ‖w.2.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.1).norm.const_mul 1
  have m2 : AEStronglyMeasurable (fun x => MJ * ‖w.2.2 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.2.2).norm.const_mul MJ
  have m3 : AEStronglyMeasurable (fun x => M * ‖w.1 x‖) cylMeasure :=
    (Lp.aestronglyMeasurable w.1).norm.const_mul M
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  calc eLpNorm F p cylMeasure
      ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖ + MJ * ‖w.2.2 x‖ + M * ‖w.1 x‖) p cylMeasure :=
        eLpNorm_mono_ae_real hF
    _ ≤ eLpNorm (fun x => 1 * ‖w.2.1 x‖) p cylMeasure + eLpNorm (fun x => MJ * ‖w.2.2 x‖) p cylMeasure
          + eLpNorm (fun x => M * ‖w.1 x‖) p cylMeasure := by
        refine (eLpNorm_add_le (m1.add m2) m3 hp1).trans ?_
        gcongr
        exact eLpNorm_add_le m1 m2 hp1
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w.2.1‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w.2.2‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w.1‖ := by
        gcongr
        · exact eLpNorm_const_mul_norm_le _ zero_le_one
        · exact eLpNorm_const_mul_norm_le _ hMJ
        · exact eLpNorm_const_mul_norm_le _ hM
    _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal ‖w‖ + ENNReal.ofReal MJ * ENNReal.ofReal ‖w‖
          + ENNReal.ofReal M * ENNReal.ofReal ‖w‖ := by
        gcongr
    _ = ENNReal.ofReal (1 + MJ + M) * ENNReal.ofReal ‖w‖ := by
        rw [ENNReal.ofReal_add (by positivity) hM, ENNReal.ofReal_add zero_le_one hMJ]
        ring

lemma aestronglyMeasurable_crApply (Sinf : ℝ → Mat n) (hc : Continuous Sinf) (w : Triple n p) :
    AEStronglyMeasurable (crApply (fun x : ℝ × ℝ => Sinf x.2) w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (Sinf x.2) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp (hc.comp continuous_snd)).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

lemma crApply_sub_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w - w') =ᵐ[cylMeasure] crApply S w - crApply S w' := by
  filter_upwards [Lp.coeFn_sub w.1 w'.1, Lp.coeFn_sub w.2.1 w'.2.1,
    Lp.coeFn_sub w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 - w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 - w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 - w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.sub_apply, map_sub]
  abel

end

end CauchyRiemannIndex

/-!
# Wendl, Corollary 4.14 (`k = 1`): `D_S` is semi-Fredholm

`D_S` and the restriction `K : W^{1,p} → L^p([-R, R] × S¹)` are bounded operators on the Banach
space `W^{1,p}`. The global estimate (Lemma 4.13) extends from test sections to `W^{1,p}` by
density, `K` is compact by the Rellich milestone, and Lemma 4.12 gives a finite-dimensional
kernel and a closed range.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

lemma crs_per {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma crs_matbound : ∃ B : ℝ, 0 ≤ B ∧ ∀ D : Mat n, (∀ i j, |D i j| ≤ 1) → ‖matCLM n D‖ ≤ B := by
  have hK : IsCompact {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} := by
    have e : {D : Mat n | ∀ i j, D i j ∈ Set.Icc (-1 : ℝ) 1} =
        Set.univ.pi (fun _ => Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1) := by
      ext D
      exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
    rw [e]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_matCLM.continuousOn
  exact ⟨max B 0, le_max_right _ _, fun D hD =>
    (hB D fun i j => Set.mem_Icc.2 (abs_le.1 (hD i j))).trans (le_max_left _ _)⟩

/-- An asymptotic coefficient is bounded. -/
lemma crs_Sbound {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n} (hSp : IsSymLoop Splus)
    (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖ := by
  obtain ⟨Mp, hMp0, hMp⟩ := exists_bound_loop Splus hSp.1 hSp.2.1
  obtain ⟨Mm, hMm0, hMm⟩ := exists_bound_loop Sminus hSm.1 hSm.2.1
  obtain ⟨B, hB0, hB⟩ := crs_matbound (n := n)
  obtain ⟨R, hR⟩ := hS.2.2 1 one_pos
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      (continuous_matCLM.comp hS.1).continuousOn
  refine ⟨max C 0 + B + Mp + Mm, by positivity, fun x v => ?_⟩
  have hv := norm_nonneg v
  have hsplit : ∀ T : Mat n, Matrix.toEuclideanLin (S x) v =
      matCLM n (S x - T) v + Matrix.toEuclideanLin T v := by
    intro T
    rw [matCLM_apply, ← LinearMap.add_apply, ← map_add, sub_add_cancel]
  by_cases h1 : R ≤ x.1
  · rw [hsplit (Splus x.2)]
    have hD : ‖matCLM n (S x - Splus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).1 h1
    calc ‖matCLM n (S x - Splus x.2) v + Matrix.toEuclideanLin (Splus x.2) v‖
        ≤ ‖matCLM n (S x - Splus x.2)‖ * ‖v‖ + Mp * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMp _ v))
      _ ≤ B * ‖v‖ + Mp * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  by_cases h2 : x.1 ≤ -R
  · rw [hsplit (Sminus x.2)]
    have hD : ‖matCLM n (S x - Sminus x.2)‖ ≤ B :=
      hB _ fun i j => by simpa using (hR x.1 x.2 i j).2 h2
    calc ‖matCLM n (S x - Sminus x.2) v + Matrix.toEuclideanLin (Sminus x.2) v‖
        ≤ ‖matCLM n (S x - Sminus x.2)‖ * ‖v‖ + Mm * ‖v‖ :=
          (norm_add_le _ _).trans (add_le_add ((matCLM n _).le_opNorm v) (hMm _ v))
      _ ≤ B * ‖v‖ + Mm * ‖v‖ := by gcongr
      _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by
          nlinarith [le_max_right C 0]
  push_neg at h1 h2
  have hx : (x.1, Int.fract x.2) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 := by
    refine Set.mk_mem_prod ⟨?_, ?_⟩ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    · have := le_abs_self R; linarith
    · have := le_abs_self R; linarith
  have hCx := hC _ hx
  have e : S (x.1, Int.fract x.2) = S x := crs_per hS.2.1 x.1 x.2
  simp only [Function.comp, e] at hCx
  rw [← matCLM_apply]
  calc ‖matCLM n (S x) v‖ ≤ ‖matCLM n (S x)‖ * ‖v‖ := (matCLM n _).le_opNorm v
    _ ≤ max C 0 * ‖v‖ := by gcongr; exact hCx.trans (le_max_left _ _)
    _ ≤ (max C 0 + B + Mp + Mm) * ‖v‖ := by nlinarith

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma crs_aesm (S : ℝ × ℝ → Mat n) (hc : Continuous S) (w : Triple n p) :
    AEStronglyMeasurable (crApply S w) cylMeasure := by
  have hJ : AEStronglyMeasurable (fun x => matCLM n (J₀ n) (w.2.2 x)) cylMeasure :=
    (matCLM n (J₀ n)).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable w.2.2)
  have hS : AEStronglyMeasurable (fun x : ℝ × ℝ => matCLM n (S x) (w.1 x)) cylMeasure :=
    Continuous.comp_aestronglyMeasurable₂ (g := fun (A : Vec n →L[ℝ] Vec n) (v : Vec n) => A v)
      (continuous_fst.clm_apply continuous_snd)
      ((continuous_matCLM.comp hc).aestronglyMeasurable)
      (Lp.aestronglyMeasurable w.1)
  exact ((Lp.aestronglyMeasurable w.2.1).add hJ).add hS

/-- The operator-norm constant of `D_S` on triples. -/
def crsC (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) : ℝ :=
  1 + ‖matCLM n (J₀ n)‖ + hb.choose

lemma crsC_nonneg (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    0 ≤ crsC S hb := by
  unfold crsC
  have := hb.choose_spec.1
  positivity

lemma crs_eLpNorm_le (S : ℝ × ℝ → Mat n)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) :
    eLpNorm (crApply S w) p cylMeasure ≤ ENNReal.ofReal (crsC S hb) * ENNReal.ofReal ‖w‖ := by
  unfold crsC
  refine eLpNorm_le_of_pointwise hb.choose_spec.1 (norm_nonneg _) (Eventually.of_forall fun x => ?_)
  unfold crApply
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [one_mul]
  · rw [← matCLM_apply]; exact (matCLM n (J₀ n)).le_opNorm _
  · exact hb.choose_spec.2 x _

lemma crs_memLp (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : MemLp (crApply S w) p cylMeasure :=
  ⟨crs_aesm S hc w, (crs_eLpNorm_le S hb w).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)⟩

lemma crs_add_ae (S : ℝ × ℝ → Mat n) (w w' : Triple n p) :
    crApply S (w + w') =ᵐ[cylMeasure] crApply S w + crApply S w' := by
  filter_upwards [Lp.coeFn_add w.1 w'.1, Lp.coeFn_add w.2.1 w'.2.1,
    Lp.coeFn_add w.2.2 w'.2.2] with x e1 e2 e3
  change (⇑(w.2.1 + w'.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(w.1 + w'.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(w.2.2 + w'.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.add_apply, map_add]
  abel

lemma crs_smul_ae (S : ℝ × ℝ → Mat n) (c : ℝ) (w : Triple n p) :
    crApply S (c • w) =ᵐ[cylMeasure] c • crApply S w := by
  filter_upwards [Lp.coeFn_smul c w.1, Lp.coeFn_smul c w.2.1,
    Lp.coeFn_smul c w.2.2] with x e1 e2 e3
  change (⇑(c • w.2.1) x + _ + Matrix.toEuclideanLin (S x) (⇑(c • w.1) x)) = _
  change _ + Matrix.toEuclideanLin (J₀ n) (⇑(c • w.2.2) x) + _ = _
  rw [e1, e2, e3]
  simp only [crApply, Pi.smul_apply, map_smul, smul_add]

/-- `D_S` as a bounded operator `L^p × L^p × L^p → L^p`. -/
def crsT (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖) :
    Triple n p →L[ℝ] LpCyl n p :=
  LinearMap.mkContinuous
    { toFun := fun w => (crs_memLp S hc hb w).toLp _
      map_add' := fun w w' => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (w + w')),
          Lp.coeFn_add ((crs_memLp S hc hb w).toLp _) ((crs_memLp S hc hb w').toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), MemLp.coeFn_toLp (crs_memLp S hc hb w'),
          crs_add_ae S w w'] with x h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c w => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (crs_memLp S hc hb (c • w)),
          Lp.coeFn_smul c ((crs_memLp S hc hb w).toLp _),
          MemLp.coeFn_toLp (crs_memLp S hc hb w), crs_smul_ae S c w] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, h4, Pi.smul_apply] }
    (crsC S hb) (fun w => by
      change ‖(crs_memLp S hc hb w).toLp _‖ ≤ _
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (crsC_nonneg S hb) (norm_nonneg _)) ?_
      rw [ENNReal.ofReal_mul (crsC_nonneg S hb)]
      exact crs_eLpNorm_le S hb w)

lemma crsT_ae (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) : (crsT S hc hb w : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] crApply S w :=
  MemLp.coeFn_toLp (crs_memLp S hc hb w)

variable (n p) in
/-- The strip `[-R, R] × S¹` (as a subset of the fundamental domain). -/
abbrev crsμ (R : ℝ) : Measure (ℝ × ℝ) := cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)

variable (n p) in
/-- `(u, v, w) ↦ u|_{[-R, R] × S¹}`. -/
def crsK (R : ℝ) : Triple n p →L[ℝ] Lp (Vec n) p (crsμ R) :=
  (LpToLpRestrictCLM (ℝ × ℝ) (Vec n) ℝ cylMeasure p (Set.Icc (-R) R ×ˢ Set.univ)).comp
    (ContinuousLinearMap.fst ℝ (LpCyl n p) (LpCyl n p × LpCyl n p))

lemma crsK_ae (R : ℝ) (w : Triple n p) :
    (crsK n p R w : ℝ × ℝ → Vec n) =ᵐ[crsμ R] w.1 :=
  LpToLpRestrictCLM_coeFn ℝ _ w.1

/-- `w1pNorm u ≤ 3 ‖(u, ∂ₛu, ∂ₜu)‖`. -/
lemma crs_w1p_le {w : Triple n p} {u : ℝ × ℝ → Vec n}
    (h1 : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u)
    (h2 : (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u)
    (h3 : (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u) :
    w1pNorm p u ≤ ENNReal.ofReal (3 * ‖w‖) := by
  have e1 : ENNReal.ofReal ‖w.1‖ = eLpNorm u p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h1]
  have e2 : ENNReal.ofReal ‖w.2.1‖ = eLpNorm (partialS u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h2]
  have e3 : ENNReal.ofReal ‖w.2.2‖ = eLpNorm (partialT u) p cylMeasure := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), eLpNorm_congr_ae h3]
  have n1 : ‖w.2.1‖ ≤ ‖w‖ := (norm_fst_le w.2).trans (norm_snd_le w)
  have n2 : ‖w.2.2‖ ≤ ‖w‖ := (norm_snd_le w.2).trans (norm_snd_le w)
  have n3 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
  unfold w1pNorm
  rw [← e1, ← e2, ← e3, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
    ← ENNReal.ofReal_add (by positivity) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The global estimate on the closed span of test triples. -/
lemma crs_estimate (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (R : ℝ) (c : ℝ≥0)
    (hest : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure + c * eLpNorm u p (crsμ R)) :
    ∀ w ∈ W1p p n, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
  have htest : ∀ w ∈ testTriples n p, ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖ := by
    rintro w ⟨u, hu, h1, h2, h3⟩
    have eT : ENNReal.ofReal ‖crsT S hc hb w‖ = eLpNorm (crOp S u) p cylMeasure := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsT_ae S hc hb w).trans (crApply_ae_crOp S h1 h2 h3))]
    have eK : ENNReal.ofReal ‖crsK n p R w‖ = eLpNorm u p (crsμ R) := by
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
        eLpNorm_congr_ae ((crsK_ae R w).trans (ae_restrict_of_ae h1))]
    have h := (ofReal_norm_le_w1pNorm h1 h2 h3).trans (hest u hu)
    have h' : ENNReal.ofReal ‖w‖ ≤
        ENNReal.ofReal ((c : ℝ) * ‖crsT S hc hb w‖ + (c : ℝ) * ‖crsK n p R w‖) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul c.coe_nonneg,
        ENNReal.ofReal_mul c.coe_nonneg, eT, eK, ENNReal.ofReal_coe_nnreal]
      exact h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  have hcl : IsClosed {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} :=
    isClosed_le continuous_norm
      ((continuous_const.mul (crsT S hc hb).continuous.norm).add
        (continuous_const.mul (crsK n p R).continuous.norm))
  intro w hw
  have hsub : (W1p p n : Set (Triple n p)) ⊆
      {w : Triple n p | ‖w‖ ≤ c * ‖crsT S hc hb w‖ + c * ‖crsK n p R w‖} := by
    unfold W1p
    rw [Submodule.topologicalClosure_coe]
    exact closure_minimal (fun w hw => htest w (span_testTriples_subset hw)) hcl
  exact hsub hw

end

end CauchyRiemannIndex

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

/-! Large antilinear perturbations: `dim ker D_σ ≤ #Z⁺` for large `σ`. -/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set Real
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma lak_per_fract {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

lemma continuous_antilinearMat : Continuous antilinearMat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat, Matrix.fromBlocks] <;>
    fun_prop

lemma norm_antilinearMat_apply (β : ℂ) (v : Vec 1) :
    ‖Matrix.toEuclideanLin (antilinearMat β) v‖ = ‖β‖ * ‖v‖ := by
  have h : ‖Matrix.toEuclideanLin (antilinearMat β) v‖ ^ 2 = (‖β‖ * ‖v‖) ^ 2 := by
    rw [norm_sq_vec1, A_apply₁, A_apply₂, mul_pow, norm_sq_vec1, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- `β` is bounded. -/
lemma beta_bounded {β : ℝ × ℝ → ℂ} (hβc : Continuous β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ B, 0 ≤ B ∧ ∀ x, ‖β x‖ ≤ B := by
  obtain ⟨R, c, hc, hends⟩ := hβends
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    (s := Icc (-R) R)).exists_bound_of_continuousOn hβc.continuousOn
  refine ⟨max C 0 + 1 / c, by positivity, fun x => ?_⟩
  by_cases hx : R ≤ |x.1|
  · have := (hends x.1 x.2 hx).2
    have : 0 ≤ max C 0 := le_max_right _ _
    linarith
  · push_neg at hx
    rw [show x = (x.1, x.2) from rfl, ← lak_per_fract hβper]
    have := hC (x.1, Int.fract x.2) ⟨⟨by linarith [neg_abs_le x.1], by linarith [le_abs_self x.1]⟩,
      ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩⟩
    have : 0 < 1 / c := by positivity
    linarith [le_max_left C 0]

lemma L2_norm_sq_eq (f : LpCyl 1 2) {u : ℝ × ℝ → Vec 1} (h : (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] u) :
    ‖f‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂cylMeasure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (h.mono fun x hx => ?_)
  simp only [hx, real_inner_self_eq_norm_sq]

lemma L2_inner_eq (f g : LpCyl 1 2) {u v : ℝ × ℝ → Vec 1} (hf : (f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] u)
    (hg : (g : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] v) :
    ⟪f, g⟫ = ∫ x, ⟪u x, v x⟫ ∂cylMeasure := by
  rw [L2.inner_def]
  refine integral_congr_ae ((hf.and hg).mono fun x hx => ?_)
  simp only [hx.1, hx.2]

lemma crApply_add_coef (S Sa : ℝ × ℝ → Mat 1) (w : Triple 1 2) (x : ℝ × ℝ) :
    crApply (fun x => S x + Sa x) w x = crApply Sa w x + Matrix.toEuclideanLin (S x) (w.1 x) := by
  simp only [crApply, map_add, LinearMap.add_apply]
  abel

lemma crApply_eq_of_fst (S : ℝ × ℝ → Mat 1) (w : Triple 1 2) (x : ℝ × ℝ) (h : w.1 x = 0) :
    crApply S w x = w.2.1 x + Matrix.toEuclideanLin (J₀ 1) (w.2.2 x) := by
  simp [crApply, h]

theorem large_antilinear_kernel_le_aux (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ≤ Zplus.card := by
  obtain ⟨A, σ₁, hσ₁, hco⟩ := large_antilinear_coercive_estimate β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero
    r hr (fun ζ hζ z hz => (hplusZ ζ hζ z hz).1) (fun ζ hζ z hz => (hminusZ ζ hζ z hz).1)
  obtain ⟨M, hM0, hM⟩ := crs_Sbound hSplus hSminus hS
  obtain ⟨R, c, hest⟩ := global_estimate 1 2 (by norm_num) (by norm_num) Splus Sminus hSplus
    hSminus S hS hplus hminus
  obtain ⟨Bβ, hBβ0, hBβ⟩ := beta_bounded hβ.continuous hβper hβends
  obtain ⟨A0, hA0def⟩ : ∃ A0, A0 = max A 0 := ⟨_, rfl⟩
  refine ⟨max σ₁ (2 * A0 * M ^ 2 + 1), fun σ hσ => ?_⟩
  have hσ1 : σ₁ ≤ σ := (le_max_left _ _).trans hσ
  have hσ2 : 2 * A0 * M ^ 2 + 1 ≤ σ := (le_max_right _ _).trans hσ
  have hA0 : 0 ≤ A0 := hA0def ▸ le_max_right _ _
  have hAA0 : A ≤ A0 := hA0def ▸ le_max_left _ _
  have hσ0 : 0 < σ := by nlinarith [sq_nonneg M]
  obtain ⟨Φ, hΦt, hΦest⟩ := hco σ hσ1
  -- the operators
  obtain ⟨Sa, hSa⟩ : ∃ Sa : ℝ × ℝ → Mat 1, Sa = fun x => σ • antilinearMat (β x) := ⟨_, rfl⟩
  have cSa : Continuous Sa := hSa ▸ (continuous_antilinearMat.comp hβ.continuous).const_smul σ
  have bSa : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec 1), ‖Matrix.toEuclideanLin (Sa x) v‖ ≤ M * ‖v‖ := by
    refine ⟨σ * Bβ, by positivity, fun x v => ?_⟩
    rw [hSa]
    simp only
    rw [map_smul, LinearMap.smul_apply, norm_smul, norm_antilinearMat_apply, Real.norm_eq_abs,
      abs_of_pos hσ0]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hBβ x) (norm_nonneg v))
      hσ0.le).trans (le_of_eq (by ring))
  have hS'eq : (fun x => S x + σ • antilinearMat (β x)) = fun x => S x + Sa x := by rw [hSa]
  rw [hS'eq]
  obtain ⟨S', hS'⟩ : ∃ S' : ℝ × ℝ → Mat 1, S' = fun x => S x + Sa x := ⟨_, rfl⟩
  rw [← hS']
  have cS' : Continuous S' := hS' ▸ hS.1.add cSa
  have bS' : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec 1), ‖Matrix.toEuclideanLin (S' x) v‖ ≤ M * ‖v‖ := by
    obtain ⟨Ma, hMa0, hMa⟩ := bSa
    refine ⟨M + Ma, by positivity, fun x v => ?_⟩
    rw [hS', map_add, LinearMap.add_apply]
    calc _ ≤ ‖Matrix.toEuclideanLin (S x) v‖ + ‖Matrix.toEuclideanLin (Sa x) v‖ := norm_add_le _ _
      _ ≤ M * ‖v‖ + Ma * ‖v‖ := add_le_add (hM x v) (hMa x v)
      _ = (M + Ma) * ‖v‖ := by ring
  have hb := crs_Sbound hSplus hSminus hS
  obtain ⟨T₀, hT₀⟩ : ∃ T : Triple 1 2 →L[ℝ] LpCyl 1 2, T = crsT Sa cSa bSa := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : Triple 1 2 →L[ℝ] LpCyl 1 2, T = crsT S' cS' bS' := ⟨_, rfl⟩
  obtain ⟨TS, hTS'⟩ : ∃ T : Triple 1 2 →L[ℝ] LpCyl 1 2, T = crsT S hS.1 hb := ⟨_, rfl⟩
  have aT₀ : ∀ w, (T₀ w : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply Sa w := fun w =>
    hT₀ ▸ crsT_ae Sa cSa bSa w
  have aT' : ∀ w, (T' w : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply S' w := fun w =>
    hT' ▸ crsT_ae S' cS' bS' w
  have aTS : ∀ w, (TS w : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] crApply S w := fun w =>
    hTS' ▸ crsT_ae S hS.1 hb w
  have hestW : ∀ w ∈ W1p 2 1, ‖w‖ ≤ c * ‖TS w‖ + c * ‖crsK 1 2 R w‖ := by
    rw [hTS']; exact crs_estimate S hS.1 hb R c hest
  -- the correction functionals in `L²`
  have hΦL : ∀ ζ : Zplus, MemLp (Φ ζ) 2 cylMeasure := fun ζ => (hΦt ζ.1 ζ.2).memLp
  set ΦL : Zplus → LpCyl 1 2 := fun ζ => (hΦL ζ).toLp _
  -- the estimate on `W^{1,2}`
  have hW : ∀ w ∈ W1p 2 1, ‖w.1‖ ^ 2 ≤ A / σ * ‖T₀ w‖ ^ 2 + ∑ ζ : Zplus, ⟪ΦL ζ, w.1⟫ ^ 2 := by
    have htest : ∀ w ∈ testTriples 1 2,
        ‖w.1‖ ^ 2 ≤ A / σ * ‖T₀ w‖ ^ 2 + ∑ ζ : Zplus, ⟪ΦL ζ, w.1⟫ ^ 2 := by
      rintro w ⟨u, hu, h1, h2, h3⟩
      have e1 := L2_norm_sq_eq w.1 h1
      have e2 := L2_norm_sq_eq (T₀ w) ((aT₀ w).trans (crApply_ae_crOp Sa h1 h2 h3))
      have e3 : ∀ ζ : Zplus, ⟪ΦL ζ, w.1⟫ = ∫ x, ⟪Φ ζ x, u x⟫ ∂cylMeasure := fun ζ =>
        L2_inner_eq _ _ (MemLp.coeFn_toLp _) h1
      rw [e1, e2]
      simp only [e3]
      rw [Finset.sum_coe_sort Zplus (fun ζ => (∫ x, ⟪Φ ζ x, u x⟫ ∂cylMeasure) ^ 2)]
      rw [hSa]
      exact hΦest u hu
    have hcl : IsClosed {w : Triple 1 2 |
        ‖w.1‖ ^ 2 ≤ A / σ * ‖T₀ w‖ ^ 2 + ∑ ζ : Zplus, ⟪ΦL ζ, w.1⟫ ^ 2} := by
      refine isClosed_le (continuous_fst.norm.pow 2) ?_
      refine (continuous_const.mul (T₀.continuous.norm.pow 2)).add ?_
      exact continuous_finsetSum _ fun ζ _ => (continuous_const.inner continuous_fst).pow 2
    intro w hw
    have hsub : (W1p 2 1 : Set (Triple 1 2)) ⊆ {w : Triple 1 2 |
        ‖w.1‖ ^ 2 ≤ A / σ * ‖T₀ w‖ ^ 2 + ∑ ζ : Zplus, ⟪ΦL ζ, w.1⟫ ^ 2} := by
      unfold W1p
      rw [Submodule.topologicalClosure_coe]
      exact closure_minimal (fun w hw => htest w (span_testTriples_subset hw)) hcl
    exact hsub hw
  -- kernel elements
  have hker : ∀ y ∈ crKernel 2 S', y ∈ W1p 2 1 ∧ T' y = 0 := by
    have hle : crKernel 2 S' ≤ W1p 2 1 ⊓ LinearMap.ker (T' : Triple 1 2 →ₗ[ℝ] LpCyl 1 2) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨hw, hz⟩
      refine ⟨hw, ?_⟩
      show T' w = 0
      exact Lp.ext ((aT' w).trans (hz.trans (Lp.coeFn_zero _ _ _).symm))
    intro y hy
    exact ⟨(hle hy).1, (hle hy).2⟩
  -- `D_σ⁰ y = -S y` on the kernel
  have hT0 : ∀ y ∈ crKernel 2 S', ‖T₀ y‖ ≤ M * ‖y.1‖ := by
    intro y hy
    obtain ⟨-, hy0⟩ := hker y hy
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [aT₀ y, aT' y,
      show (T' y : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 by rw [hy0]; exact Lp.coeFn_zero _ _ _]
      with x h1 h2 h3
    rw [h1]
    have h4 := crApply_add_coef S Sa y x
    rw [← hS', ← h2, h3, Pi.zero_apply] at h4
    have : crApply Sa y x = -Matrix.toEuclideanLin (S x) (y.1 x) := by
      rw [eq_neg_iff_add_eq_zero, ← h4]
    rw [this, norm_neg]
    exact hM x _
  -- injectivity of the functionals on the kernel
  set Λ : crKernel 2 S' →ₗ[ℝ] (Zplus → ℝ) :=
    (LinearMap.pi fun ζ : Zplus =>
      ((innerSL ℝ (ΦL ζ)).comp (ContinuousLinearMap.fst ℝ (LpCyl 1 2)
        (LpCyl 1 2 × LpCyl 1 2))).toLinearMap).comp (crKernel 2 S').subtype
  have hinj : Function.Injective Λ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy0
    have hz : ∀ ζ : Zplus, ⟪ΦL ζ, (y : Triple 1 2).1⟫ = 0 := fun ζ => by
      have := congrFun hy0 ζ
      simpa [Λ] using this
    obtain ⟨hyW, hyT⟩ := hker y y.2
    have h1 := hW y hyW
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      add_zero] at h1
    have h2 := hT0 y y.2
    have hn : ‖(y : Triple 1 2).1‖ ^ 2 ≤ 0 := by
      have h3 : ‖T₀ y‖ ^ 2 ≤ M ^ 2 * ‖(y : Triple 1 2).1‖ ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h2 2
      have h4 : A / σ * ‖T₀ y‖ ^ 2 ≤ A0 / σ * (M ^ 2 * ‖(y : Triple 1 2).1‖ ^ 2) := by
        calc A / σ * ‖T₀ y‖ ^ 2 ≤ A0 / σ * ‖T₀ y‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAA0 hσ0.le) (sq_nonneg _)
          _ ≤ A0 / σ * (M ^ 2 * ‖(y : Triple 1 2).1‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : A0 / σ * M ^ 2 ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hσ0]; linarith
      have h6 := sq_nonneg ‖(y : Triple 1 2).1‖
      have h7 := mul_le_mul_of_nonneg_right h5 h6
      have h8 : A0 / σ * (M ^ 2 * ‖(y : Triple 1 2).1‖ ^ 2) =
          A0 / σ * M ^ 2 * ‖(y : Triple 1 2).1‖ ^ 2 := by ring
      linarith
    have hy1 : (y : Triple 1 2).1 = 0 := by
      have : ‖(y : Triple 1 2).1‖ ^ 2 = 0 := le_antisymm hn (sq_nonneg _)
      exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)
    -- now `y = 0` by the global estimate of `D_S`
    have hTSy : TS (y : Triple 1 2) = 0 := by
      apply Lp.ext
      filter_upwards [aTS (y : Triple 1 2), aT' (y : Triple 1 2),
        show (T' (y : Triple 1 2) : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 by
          rw [hyT]; exact Lp.coeFn_zero _ _ _,
        show ((y : Triple 1 2).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 by
          rw [hy1]; exact Lp.coeFn_zero _ _ _, Lp.coeFn_zero (Vec 1) 2 cylMeasure]
        with x h1 h2 h3 h4 h5
      rw [h1, h5, crApply_eq_of_fst S _ x h4, ← crApply_eq_of_fst S' _ x h4, ← h2, h3]
    have hK : crsK 1 2 R (y : Triple 1 2) = 0 := by
      apply Lp.ext
      filter_upwards [crsK_ae (n := 1) (p := 2) R (y : Triple 1 2),
        ae_restrict_of_ae (show ((y : Triple 1 2).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 by
          rw [hy1]; exact Lp.coeFn_zero _ _ _),
        Lp.coeFn_zero (Vec 1) 2 (crsμ R)] with x a b d
      rw [a, b, d]
    have := hestW (y : Triple 1 2) hyW
    rw [hTSy, hK] at this
    simp only [norm_zero, mul_zero, add_zero] at this
    exact Subtype.ext (norm_le_zero_iff.1 this)
  have hfin : FiniteDimensional ℝ (crKernel 2 S') := FiniteDimensional.of_injective Λ hinj
  refine ⟨hfin, ?_⟩
  calc Module.finrank ℝ (crKernel 2 S') ≤ Module.finrank ℝ (Zplus → ℝ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Zplus.card := by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (hplus : IsNondegenerate Splus) (hminus : IsNondegenerate Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hdisj : Disjoint Zplus Zminus)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hminusZ : ∀ ζ ∈ Zminus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = (starRingEnd ℂ) z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      Module.finrank ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ≤ Zplus.card :=
  large_antilinear_kernel_le_aux Splus Sminus hSplus hSminus hplus hminus S hS β hβ hβper hβC1 hβends Zplus Zminus hZ hdisj hzero r hr hplusZ hminusZ
