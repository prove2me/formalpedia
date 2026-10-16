-- Prove2me | solution 1 for CauchyRiemannIndex.global_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T18:27:53.308152+00:00
-- url     : https://prove2.me/submissions/1df53187-dc4a-4444-b9fc-d0478c5818be

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
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Theorems.Thm_CauchyRiemannIndex_local_estimate
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.MeanInequalitiesPow
import Theorems.Thm_CauchyRiemannIndex_asymptotic_estimate
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- ===== Scratch/CR411Bridge.lean =====
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

-- ===== Scratch/CRCylCalc.lean =====
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

-- ===== Scratch/CRDerivEst.lean =====
/-!
# `‖u‖_{W^{1,p}} ≤ c ‖D u‖_p + c ‖u‖_p` for the translation-invariant operator

Cut `u` off in `s` near a centre `a`, move the centre to the origin, apply the local estimate
(Wendl, Prop. 4.8) on `[-1, 1] × S¹` with one constant, and average the `p`-th powers over all
centres `a ∈ ℝ`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### Cut-off in `s` -/

lemma crd_hasFDerivAt {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => χ x.1) (deriv χ x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
  ((hχ.differentiable (by simp)) x.1).hasDerivAt.comp_hasFDerivAt x
    (hasFDerivAt_fst (𝕜 := ℝ) (p := x))

lemma crd_fderiv {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => χ x.1 • u x)
      (χ x.1 • fderiv ℝ u x +
        (deriv χ x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (u x)) x :=
  (crd_hasFDerivAt hχ x).smul ((hu.1.differentiable (by simp)) x).hasFDerivAt

lemma crd_isTestSection {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : IsTestSection (fun x : ℝ × ℝ => χ x.1 • u x) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨(hχ.comp contDiff_fst).smul hu.1, ?_, R, ?_⟩
  · intro s t; simp [hu.2.1]
  · intro s t hs; simp [hR s t hs]

lemma crd_partialS {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) (x : ℝ × ℝ) :
    partialS (fun x : ℝ × ℝ => χ x.1 • u x) x = χ x.1 • partialS u x + deriv χ x.1 • u x := by
  rw [partialS, (crd_fderiv hχ hu x).fderiv]
  simp [partialS]

lemma crd_partialT {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) (x : ℝ × ℝ) :
    partialT (fun x : ℝ × ℝ => χ x.1 • u x) x = χ x.1 • partialT u x := by
  rw [partialT, (crd_fderiv hχ hu x).fderiv]
  simp [partialT]

lemma crd_crOp {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (S : ℝ × ℝ → Mat n) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) (x : ℝ × ℝ) :
    crOp S (fun x : ℝ × ℝ => χ x.1 • u x) x = χ x.1 • crOp S u x + deriv χ x.1 • u x := by
  simp only [crOp, crd_partialS hχ hu, crd_partialT hχ hu, map_smul, smul_add]
  abel

/-! ### Translation in `s` -/

lemma crd_shift_isTestSection (a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    IsTestSection (fun x : ℝ × ℝ => u (x + (a, 0))) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨hu.1.comp (contDiff_id.add contDiff_const), ?_, R + |a|, ?_⟩
  · intro s t
    simp only [Prod.mk_add_mk, add_zero]
    exact hu.2.1 (s + a) t
  · intro s t hs
    simp only [Prod.mk_add_mk, add_zero]
    apply hR
    have h1 := abs_add_le (s + a) (-a)
    rw [abs_neg, add_neg_cancel_right] at h1
    linarith

lemma crd_shift_partialS (a : ℝ) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialS (fun x : ℝ × ℝ => u (x + (a, 0))) x = partialS u (x + (a, 0)) := by
  simp only [partialS]
  rw [fderiv_comp_add_right]

lemma crd_shift_partialT (a : ℝ) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialT (fun x : ℝ × ℝ => u (x + (a, 0))) x = partialT u (x + (a, 0)) := by
  simp only [partialT]
  rw [fderiv_comp_add_right]

lemma crd_shift_crOp (a : ℝ) (Sinf : ℝ → Mat n) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    crOp (fun x : ℝ × ℝ => Sinf x.2) (fun x : ℝ × ℝ => u (x + (a, 0))) x =
      crOp (fun x : ℝ × ℝ => Sinf x.2) u (x + (a, 0)) := by
  simp only [crOp, crd_shift_partialS, crd_shift_partialT, Prod.snd_add, add_zero]

lemma crd_mp (a : ℝ) :
    MeasurePreserving (fun x : ℝ × ℝ => x + (a, 0)) cylMeasure cylMeasure := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).prod
    (MeasurePreserving.id (volume.restrict (Set.Ico (0 : ℝ) 1)))
  rw [cylMeasure_eq_prod]
  convert h using 1
  funext x
  ext <;> simp

/-! ### Averaging over the centre -/

instance crd_sFinite : SFinite cylMeasure := by unfold cylMeasure; infer_instance

lemma crd_avg {r : ℝ} (hr : 0 ≤ r) {g : ℝ → ℝ} (hg : Continuous g) {F : ℝ × ℝ → Vec n}
    (hF : Continuous F) :
    ∫⁻ a, ∫⁻ x, ‖g x.1 • F (x + (a, 0))‖ₑ ^ r ∂cylMeasure =
      (∫⁻ y, ‖g y‖ₑ ^ r) * ∫⁻ x, ‖F x‖ₑ ^ r ∂cylMeasure := by
  have h1 : ∀ a : ℝ, ∫⁻ x, ‖g x.1 • F (x + (a, 0))‖ₑ ^ r ∂cylMeasure =
      ∫⁻ x, ‖g (x.1 - a)‖ₑ ^ r * ‖F x‖ₑ ^ r ∂cylMeasure := by
    intro a
    have hm : Measurable fun x : ℝ × ℝ => ‖g (x.1 - a)‖ₑ ^ r * ‖F x‖ₑ ^ r :=
      ((hg.measurable.comp (measurable_fst.sub_const a)).enorm.pow_const r).mul
        (hF.measurable.enorm.pow_const r)
    rw [← (crd_mp a).lintegral_comp hm]
    congr 1
    funext x
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hr]
    simp
  rw [show (fun a : ℝ => ∫⁻ x, ‖g x.1 • F (x + (a, 0))‖ₑ ^ r ∂cylMeasure) =
      fun a => ∫⁻ x, ‖g (x.1 - a)‖ₑ ^ r * ‖F x‖ₑ ^ r ∂cylMeasure from funext h1]
  rw [lintegral_lintegral_swap]
  · have h2 : ∀ x : ℝ × ℝ, ∫⁻ a, ‖g (x.1 - a)‖ₑ ^ r * ‖F x‖ₑ ^ r =
        (∫⁻ y, ‖g y‖ₑ ^ r) * ‖F x‖ₑ ^ r := by
      intro x
      rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hr enorm_ne_top)]
      rw [lintegral_sub_left_eq_self (fun y => ‖g y‖ₑ ^ r) x.1]
    simp_rw [h2]
    rw [lintegral_const_mul _ (hF.measurable.enorm.pow_const r)]
  · exact (((hg.measurable.comp (measurable_snd.fst.sub measurable_fst)).enorm.pow_const r).mul
      ((hF.measurable.comp measurable_snd).enorm.pow_const r)).aemeasurable

/-! ### Elementary inequalities -/

lemma crd_three {r : ℝ} (hr : 1 ≤ r) (A B C : ℝ≥0∞) :
    (A + B + C) ^ r ≤ 2 ^ (r - 1) * 2 ^ (r - 1) * (A ^ r + B ^ r + C ^ r) := by
  have h1 : (1 : ℝ≥0∞) ≤ 2 ^ (r - 1) := by
    have := ENNReal.rpow_le_rpow (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by linarith : (0 : ℝ) ≤ r - 1)
    rwa [ENNReal.one_rpow] at this
  calc (A + B + C) ^ r ≤ 2 ^ (r - 1) * ((A + B) ^ r + C ^ r) :=
        ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
    _ ≤ 2 ^ (r - 1) * (2 ^ (r - 1) * (A ^ r + B ^ r) + 2 ^ (r - 1) * C ^ r) := by
        gcongr
        · exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr
        · exact le_mul_of_one_le_left' h1
    _ = 2 ^ (r - 1) * 2 ^ (r - 1) * (A ^ r + B ^ r + C ^ r) := by ring

lemma crd_rpow_eLpNorm {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ⊤) {E : Type*} [NormedAddCommGroup E] (g : α → E) :
    eLpNorm g p μ ^ p.toReal = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, one_div,
    ENNReal.rpow_inv_rpow (ENNReal.toReal_ne_zero.mpr ⟨hp0, hpt⟩)]

lemma crd_continuous_crOp (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crOp (fun x : ℝ × ℝ => Sinf x.2) u) :=
  (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
    ((continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous)

/-! ### The local estimate with a cut-off, uniformly in the section -/

lemma crd_local (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat n) (hS : Continuous Sinf) (hper : Function.Periodic Sinf 1)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχ0 : ∀ y, 1 ≤ |y| → χ y = 0) :
    ∃ c : ℝ≥0, ∀ w : ℝ × ℝ → Vec n, IsTestSection w →
      eLpNorm (fun x => χ x.1 • partialS w x) p cylMeasure ≤
          (c + 1) * (eLpNorm (fun x => χ x.1 • crOp (fun x : ℝ × ℝ => Sinf x.2) w x) p cylMeasure +
            eLpNorm (fun x => deriv χ x.1 • w x) p cylMeasure +
            eLpNorm (fun x => χ x.1 • w x) p cylMeasure) ∧
      eLpNorm (fun x => χ x.1 • partialT w x) p cylMeasure ≤
          (c + 1) * (eLpNorm (fun x => χ x.1 • crOp (fun x : ℝ × ℝ => Sinf x.2) w x) p cylMeasure +
            eLpNorm (fun x => deriv χ x.1 • w x) p cylMeasure +
            eLpNorm (fun x => χ x.1 • w x) p cylMeasure) := by
  obtain ⟨c, hc⟩ := local_estimate n p hp hp' 1 (fun x : ℝ × ℝ => Sinf x.2)
    (hS.comp continuous_snd) (fun s t => hper t)
  refine ⟨c, fun w hw => ?_⟩
  have h1p : 1 ≤ p := hp.le
  set S : ℝ × ℝ → Mat n := fun x => Sinf x.2 with hSdef
  set v : ℝ × ℝ → Vec n := fun x => χ x.1 • w x with hv
  have hvt : IsTestSection v := crd_isTestSection hχ hw
  have hvan : ∀ s t, 1 ≤ |s| → v (s, t) = 0 := fun s t hs => by simp [hv, hχ0 s hs]
  have hcv := hc v hvt hvan
  set f₁ : ℝ × ℝ → Vec n := fun x => χ x.1 • crOp S w x with hf₁
  set f₂ : ℝ × ℝ → Vec n := fun x => deriv χ x.1 • w x with hf₂
  set A := eLpNorm f₁ p cylMeasure
  set B := eLpNorm f₂ p cylMeasure
  set C := eLpNorm v p cylMeasure
  have hcχ : Continuous fun x : ℝ × ℝ => χ x.1 := hχ.continuous.comp continuous_fst
  have hcχ' : Continuous fun x : ℝ × ℝ => deriv χ x.1 :=
    (hχ.continuous_deriv (by simp)).comp continuous_fst
  have hc1 : Continuous f₁ := hcχ.smul (crd_continuous_crOp Sinf hS hw)
  have hc2 : Continuous f₂ := hcχ'.smul hw.continuous
  have hDv : crOp S v = f₁ + f₂ := funext fun x => crd_crOp hχ S hw x
  have hD : eLpNorm (crOp S v) p cylMeasure ≤ A + B := by
    rw [hDv]; exact eLpNorm_add_le hc1.aestronglyMeasurable hc2.aestronglyMeasurable h1p
  have hW : w1pNorm p v ≤ c * (A + B) + c * C := hcv.trans (by gcongr)
  have hsS : eLpNorm (partialS v) p cylMeasure ≤ w1pNorm p v := by
    unfold w1pNorm; exact le_add_right le_add_self
  have hsT : eLpNorm (partialT v) p cylMeasure ≤ w1pNorm p v := by
    unfold w1pNorm; exact le_add_self
  have hfin : c * (A + B) + c * C + B ≤ ((c : ℝ≥0∞) + 1) * (A + B + C) := by
    rw [add_mul, one_mul, mul_add (c : ℝ≥0∞) (A + B) C]
    exact add_le_add le_rfl (le_add_right le_add_self)
  constructor
  · have heq : (fun x => χ x.1 • partialS w x) = partialS v - f₂ := by
      funext x; simp [hv, hf₂, crd_partialS hχ hw x]
    rw [heq]
    calc eLpNorm (partialS v - f₂) p cylMeasure
        ≤ eLpNorm (partialS v) p cylMeasure + B :=
          eLpNorm_sub_le hvt.continuous_partialS.aestronglyMeasurable hc2.aestronglyMeasurable h1p
      _ ≤ c * (A + B) + c * C + B := by gcongr; exact hsS.trans hW
      _ ≤ _ := hfin
  · have heq : (fun x => χ x.1 • partialT w x) = partialT v := by
      funext x; simp [hv, crd_partialT hχ hw x]
    rw [heq]
    calc eLpNorm (partialT v) p cylMeasure ≤ c * (A + B) + c * C := hsT.trans hW
      _ ≤ c * (A + B) + c * C + B := le_self_add
      _ ≤ _ := hfin

end

end CauchyRiemannIndex

-- ===== Scratch/CR413.lean =====
/-!
# Wendl, Lemma 4.13 (`k = 1`): the global estimate modulo `[-R, R] × S¹`

Split a test section with a partition of unity `β₋ + β₀ + β₊ = 1` in `s`, apply the asymptotic
estimate (Prop. 4.9) to `β±u` and the local estimate (Prop. 4.8) to `β₀u`; the cut-off derivative
terms and `‖β₀u‖_p` live on `[-R, R] × S¹`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- A function of `s` supported in `[-R, R]` and bounded by `M` multiplies `L^p` into
`L^p([-R, R] × S¹)` with norm `≤ M`. -/
lemma crg_region {p : ℝ≥0∞} (g : ℝ → ℝ) (M : ℝ≥0) (hM : ∀ s, |g s| ≤ M) (R : ℝ)
    (hg : ∀ s, R < |s| → g s = 0) (u : ℝ × ℝ → Vec n) :
    eLpNorm (fun x => g x.1 • u x) p cylMeasure ≤
      M * eLpNorm u p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) := by
  have hms : MeasurableSet (Set.Icc (-R) R ×ˢ (Set.univ : Set ℝ)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hms]
  have key : ∀ x : ℝ × ℝ, ‖g x.1 • u x‖₊ ≤
      M * ‖(Set.Icc (-R) R ×ˢ (Set.univ : Set ℝ)).indicator u x‖₊ := by
    intro x
    by_cases hx : x ∈ Set.Icc (-R) R ×ˢ (Set.univ : Set ℝ)
    · rw [Set.indicator_of_mem hx, nnnorm_smul]
      gcongr
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
      exact hM _
    · have hlt : R < |x.1| := by
        simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, and_true, not_and_or, not_le] at hx
        rcases hx with h | h
        · exact lt_abs.2 (Or.inr (by linarith))
        · exact lt_abs.2 (Or.inl h)
      simp [hg _ hlt]
  have := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (μ := cylMeasure)
    (Eventually.of_forall key) p
  rwa [ENNReal.smul_def, smul_eq_mul] at this

/-- A continuous function vanishing outside `[-R, R]` is bounded. -/
lemma crg_bound {g : ℝ → ℝ} (hg : Continuous g) (R : ℝ) (hz : ∀ s, R < |s| → g s = 0) :
    ∃ M : ℝ≥0, ∀ s, |g s| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun s => ?_⟩
  show |g s| ≤ max C 0
  by_cases hs : R < |s|
  · rw [hz s hs, abs_zero]; exact le_max_right _ _
  · have hmem : s ∈ Set.Icc (-R) R := abs_le.1 (not_lt.1 hs)
    have := hC s hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- A function that is constant on `(R, ∞)` and on `(-∞, -R)` has zero derivative there. -/
lemma crg_deriv_zero {f : ℝ → ℝ} {R a b : ℝ} (hr : ∀ y, R < y → f y = a)
    (hl : ∀ y, y < -R → f y = b) : ∀ s, R < |s| → deriv f s = 0 := by
  intro s hs
  rcases lt_abs.1 hs with h | h
  · have hev : f =ᶠ[𝓝 s] fun _ => a :=
      Filter.eventually_of_mem (Ioi_mem_nhds h) fun y hy => hr y hy
    rw [hev.deriv_eq]; simp
  · have hev : f =ᶠ[𝓝 s] fun _ => b :=
      Filter.eventually_of_mem (Iio_mem_nhds (by linarith : s < -R)) fun y hy => hl y hy
    rw [hev.deriv_eq]; simp

lemma crg_continuous_crOp (S : ℝ × ℝ → Mat n) (hc : Continuous S) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crOp S u) :=
  (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
    ((continuous_matCLM.comp hc).clm_apply hu.continuous)

lemma crg_w1p_add {p : ℝ≥0∞} (hp : 1 ≤ p) {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u)
    (hv : IsTestSection v) : w1pNorm p (u + v) ≤ w1pNorm p u + w1pNorm p v := by
  unfold w1pNorm
  rw [partialS_add hu hv, partialT_add hu hv]
  have h1 := eLpNorm_add_le (μ := cylMeasure) hu.continuous.aestronglyMeasurable
    hv.continuous.aestronglyMeasurable hp
  have h2 := eLpNorm_add_le (μ := cylMeasure) hu.continuous_partialS.aestronglyMeasurable
    hv.continuous_partialS.aestronglyMeasurable hp
  have h3 := eLpNorm_add_le (μ := cylMeasure) hu.continuous_partialT.aestronglyMeasurable
    hv.continuous_partialT.aestronglyMeasurable hp
  calc _ ≤ (eLpNorm u p cylMeasure + eLpNorm v p cylMeasure) +
        (eLpNorm (partialS u) p cylMeasure + eLpNorm (partialS v) p cylMeasure) +
        (eLpNorm (partialT u) p cylMeasure + eLpNorm (partialT v) p cylMeasure) :=
        add_le_add (add_le_add h1 h2) h3
    _ = _ := by ring

/-- `‖D_S(χu)‖_p ≤ ‖D_S u‖_p + M ‖u‖_{L^p([-R, R] × S¹)}` for a cut-off `χ` with `|χ| ≤ 1`
whose derivative is supported in `[-R, R]`. -/
lemma crg_piece {p : ℝ≥0∞} (hp : 1 ≤ p) (S : ℝ × ℝ → Mat n) (hS : Continuous S) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (h1 : ∀ s, |χ s| ≤ 1) (R : ℝ) (hz : ∀ s, R < |s| → deriv χ s = 0) :
    ∃ M : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm (crOp S (fun x => χ x.1 • u x)) p cylMeasure ≤
        eLpNorm (crOp S u) p cylMeasure +
          M * eLpNorm u p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) := by
  have hcd : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := crg_bound hcd R hz
  refine ⟨M, fun u hu => ?_⟩
  have heq : crOp S (fun x => χ x.1 • u x) =
      (fun x => χ x.1 • crOp S u x) + (fun x => deriv χ x.1 • u x) :=
    funext fun x => crd_crOp hχ S hu x
  have hcχ : Continuous fun x : ℝ × ℝ => χ x.1 := hχ.continuous.comp continuous_fst
  have hcχ' : Continuous fun x : ℝ × ℝ => deriv χ x.1 := hcd.comp continuous_fst
  rw [heq]
  refine (eLpNorm_add_le (hcχ.smul (crg_continuous_crOp S hS hu)).aestronglyMeasurable
    (hcχ'.smul hu.continuous).aestronglyMeasurable hp).trans (add_le_add ?_ ?_)
  · refine eLpNorm_mono fun x => ?_
    show ‖χ x.1 • crOp S u x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (h1 _)
  · exact crg_region _ M hM R hz u

theorem crg_main (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus) :
    ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure +
        c * eLpNorm u p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) := by
  have h1p : 1 ≤ p := hp.le
  obtain ⟨Rp, cp, hcp⟩ :=
    (asymptotic_estimate n p hp hp' Splus Sminus hSplus hSminus S hS).1 hplus
  obtain ⟨Rm, cm, hcm⟩ :=
    (asymptotic_estimate n p hp hp' Splus Sminus hSplus hSminus S hS).2 hminus
  set R₀ : ℝ := max (max Rp Rm) 0 with hR₀
  have hR0 : 0 ≤ R₀ := le_max_right _ _
  have hRp : Rp ≤ R₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hRm : Rm ≤ R₀ := (le_max_right _ _).trans (le_max_left _ _)
  set bp : ℝ → ℝ := fun s => Real.smoothTransition (s - R₀) with hbpdef
  set bm : ℝ → ℝ := fun s => Real.smoothTransition (-s - R₀) with hbmdef
  set b0 : ℝ → ℝ := fun s => 1 - bp s - bm s with hb0def
  have hbp : ContDiff ℝ ∞ bp :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hbm : ContDiff ℝ ∞ bm :=
    Real.smoothTransition.contDiff.comp (contDiff_id.neg.sub contDiff_const)
  have hb0 : ContDiff ℝ ∞ b0 := (contDiff_const.sub hbp).sub hbm
  have bp_r : ∀ y, R₀ + 1 < y → bp y = 1 := fun y hy =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have bp_l : ∀ y, y < -(R₀ + 1) → bp y = 0 := fun y hy =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have bm_r : ∀ y, R₀ + 1 < y → bm y = 0 := fun y hy =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have bm_l : ∀ y, y < -(R₀ + 1) → bm y = 1 := fun y hy =>
    Real.smoothTransition.one_of_one_le (by linarith)
  have b0_ge : ∀ y, R₀ + 1 ≤ |y| → b0 y = 0 := by
    intro y hy
    rcases le_abs.1 hy with h | h
    · simp only [hb0def, hbpdef, hbmdef]
      rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith)]
      ring
    · simp only [hb0def, hbpdef, hbmdef]
      rw [Real.smoothTransition.zero_of_nonpos (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith)]
      ring
  have b0_r : ∀ y, R₀ + 1 < y → b0 y = 0 := fun y hy => b0_ge y (le_abs.2 (Or.inl hy.le))
  have b0_l : ∀ y, y < -(R₀ + 1) → b0 y = 0 := fun y hy =>
    b0_ge y (le_abs.2 (Or.inr (by linarith)))
  have abp : ∀ s, |bp s| ≤ 1 := fun s =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (s - R₀)],
      Real.smoothTransition.le_one _⟩
  have abm : ∀ s, |bm s| ≤ 1 := fun s =>
    abs_le.2 ⟨by linarith [Real.smoothTransition.nonneg (-s - R₀)],
      Real.smoothTransition.le_one _⟩
  have ab0 : ∀ s, |b0 s| ≤ 1 := fun s => by
    have h1 := Real.smoothTransition.nonneg (s - R₀)
    have h2 := Real.smoothTransition.nonneg (-s - R₀)
    have h3 := Real.smoothTransition.le_one (s - R₀)
    have h4 := Real.smoothTransition.le_one (-s - R₀)
    simp only [hb0def, hbpdef, hbmdef]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  obtain ⟨Mp, hMp⟩ := crg_piece h1p S hS.1 hbp abp (R₀ + 1) (crg_deriv_zero bp_r bp_l)
  obtain ⟨Mm, hMm⟩ := crg_piece h1p S hS.1 hbm abm (R₀ + 1) (crg_deriv_zero bm_r bm_l)
  obtain ⟨M0, hM0⟩ := crg_piece h1p S hS.1 hb0 ab0 (R₀ + 1) (crg_deriv_zero b0_r b0_l)
  obtain ⟨c0, hc0⟩ := local_estimate n p hp hp' (R₀ + 1) S hS.1 hS.2.1
  refine ⟨R₀ + 1, (cp + cm + c0) * (Mp + Mm + M0 + 2), fun u hu => ?_⟩
  set vp : ℝ × ℝ → Vec n := fun x => bp x.1 • u x with hvp
  set vm : ℝ × ℝ → Vec n := fun x => bm x.1 • u x with hvm
  set v0 : ℝ × ℝ → Vec n := fun x => b0 x.1 • u x with hv0
  have tp : IsTestSection vp := crd_isTestSection hbp hu
  have tm : IsTestSection vm := crd_isTestSection hbm hu
  have t0 : IsTestSection v0 := crd_isTestSection hb0 hu
  have hsum : u = vm + v0 + vp := by
    funext x
    simp only [Pi.add_apply, hvp, hvm, hv0, hb0def]
    rw [sub_smul, sub_smul, one_smul]
    abel
  set A := eLpNorm (crOp S u) p cylMeasure with hA
  set B := eLpNorm u p (cylMeasure.restrict (Set.Icc (-(R₀ + 1)) (R₀ + 1) ×ˢ Set.univ)) with hB
  have eP : w1pNorm p vp ≤ cp * (A + Mp * B) := by
    refine (hcp vp tp fun s t hs => ?_).trans (by gcongr; exact hMp u hu)
    simp [hvp, hbpdef, Real.smoothTransition.zero_of_nonpos (by linarith : s - R₀ ≤ 0)]
  have eM : w1pNorm p vm ≤ cm * (A + Mm * B) := by
    refine (hcm vm tm fun s t hs => ?_).trans (by gcongr; exact hMm u hu)
    simp [hvm, hbmdef, Real.smoothTransition.zero_of_nonpos (by linarith : -s - R₀ ≤ 0)]
  have hv0B : eLpNorm v0 p cylMeasure ≤ B := by
    have := crg_region (p := p) b0 1 (fun s => by simpa using ab0 s) (R₀ + 1)
      (fun s hs => b0_ge s hs.le) u
    rwa [ENNReal.coe_one, one_mul] at this
  have e0 : w1pNorm p v0 ≤ c0 * (A + M0 * B) + c0 * B := by
    refine (hc0 v0 t0 fun s t hs => ?_).trans ?_
    · simp [hv0, b0_ge s hs]
    · gcongr
      exact hM0 u hu
  have hX : cm + c0 + cp ≤ (cp + cm + c0) * (Mp + Mm + M0 + 2) :=
    calc cm + c0 + cp ≤ (cm + c0 + cp) + (cp * Mp + cp * Mm + cp * M0 + cp + cm * Mp + cm * Mm +
          cm * M0 + cm + c0 * Mp + c0 * Mm + c0 * M0 + c0) := le_self_add
      _ = _ := by ring
  have hY : cm * Mm + c0 * M0 + c0 + cp * Mp ≤ (cp + cm + c0) * (Mp + Mm + M0 + 2) :=
    calc cm * Mm + c0 * M0 + c0 + cp * Mp ≤ (cm * Mm + c0 * M0 + c0 + cp * Mp) +
          (cp * Mm + cp * M0 + 2 * cp + cm * Mp + cm * M0 + 2 * cm + c0 * Mp + c0 * Mm + c0) :=
          le_self_add
      _ = _ := by ring
  calc w1pNorm p u = w1pNorm p (vm + v0 + vp) := by rw [← hsum]
    _ ≤ w1pNorm p vm + w1pNorm p v0 + w1pNorm p vp :=
        (crg_w1p_add h1p (tm.add t0) tp).trans (by gcongr; exact crg_w1p_add h1p tm t0)
    _ ≤ cm * (A + Mm * B) + (c0 * (A + M0 * B) + c0 * B) + cp * (A + Mp * B) := by
        gcongr
    _ = ((cm + c0 + cp : ℝ≥0) : ℝ≥0∞) * A +
          ((cm * Mm + c0 * M0 + c0 + cp * Mp : ℝ≥0) : ℝ≥0∞) * B := by
        push_cast; ring
    _ ≤ (((cp + cm + c0) * (Mp + Mm + M0 + 2) : ℝ≥0) : ℝ≥0∞) * A +
          (((cp + cm + c0) * (Mp + Mm + M0 + 2) : ℝ≥0) : ℝ≥0∞) * B := by
        gcongr
    _ = _ := by push_cast; ring

end

end CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus) :
    ∃ (R : ℝ) (c : ℝ≥0), ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      w1pNorm p u ≤ c * eLpNorm (crOp S u) p cylMeasure +
        c * eLpNorm u p (cylMeasure.restrict (Set.Icc (-R) R ×ˢ Set.univ)) :=
  crg_main n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus
