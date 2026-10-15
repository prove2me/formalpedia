-- Prove2me | solution 1 for CauchyRiemannIndex.weak_solution_graph_approx
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T09:43:02.695289+00:00
-- url     : https://prove2.me/submissions/597c9aef-bc75-4d07-ba9b-a42062e592ee

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Group.Prod
import Theorems.Thm_CauchyRiemannIndex_tendsto_eLpNorm_zero_of_dominated
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

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

-- ===== Scratch/CRSConvBase.lean =====
/-!
# Convolution in `s` on the cylinder: shifts, Tonelli, measurability

`G(s, t) = ∫ ρ(σ) g(s - σ, t) dσ`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma sca_cyl_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Set.Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

instance sca_sFinite : SFinite cylMeasure := by unfold cylMeasure; infer_instance

lemma sca_mp (a : ℝ) :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 - a, x.2)) cylMeasure cylMeasure := by
  have h := (measurePreserving_sub_right (volume : Measure ℝ) a).prod
    (MeasurePreserving.id (volume.restrict (Set.Ico (0 : ℝ) 1)))
  rw [sca_cyl_eq_prod]
  convert h using 1
  funext x
  rfl

lemma sca_me (a : ℝ) : MeasurableEmbedding (fun x : ℝ × ℝ => (x.1 - a, x.2)) :=
  ((MeasurableEquiv.subRight a).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding

lemma sca_meas_shift : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 - p.2, p.1.2)) := by
  fun_prop

/-- Tonelli for `s`-shifts on the cylinder. -/
lemma sca_tonelli {k : ℝ → ℝ≥0∞} (hk : Measurable k) {h : ℝ × ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ x, (∫⁻ σ, k σ * h (x.1 - σ, x.2)) ∂cylMeasure =
      (∫⁻ σ, k σ) * ∫⁻ x, h x ∂cylMeasure := by
  rw [lintegral_lintegral_swap ((hk.comp measurable_snd).mul (hh.comp sca_meas_shift)).aemeasurable]
  have h1 : ∀ σ : ℝ, ∫⁻ x, k σ * h (x.1 - σ, x.2) ∂cylMeasure = k σ * ∫⁻ x, h x ∂cylMeasure := by
    intro σ
    rw [lintegral_const_mul (k σ) (f := fun x : ℝ × ℝ => h (x.1 - σ, x.2))
      (hh.comp ((measurable_fst.sub_const σ).prodMk measurable_snd))]
    congr 1
    exact (sca_mp σ).lintegral_comp hh
  simp_rw [h1]
  rw [lintegral_mul_const _ hk]

lemma sca_sm {g : ℝ × ℝ → Vec n} (hg : StronglyMeasurable g) {ρ : ℝ → ℝ} (hρ : Continuous ρ) :
    StronglyMeasurable (fun x : ℝ × ℝ => ∫ σ, ρ σ • g (x.1 - σ, x.2)) := by
  have : StronglyMeasurable
      (Function.uncurry fun (x : ℝ × ℝ) (σ : ℝ) => ρ σ • g (x.1 - σ, x.2)) :=
    (hρ.measurable.comp measurable_snd).stronglyMeasurable.smul (hg.comp_measurable sca_meas_shift)
  exact this.integral_prod_right

lemma sca_enorm_le (g : ℝ × ℝ → Vec n) (ρ : ℝ → ℝ) (x : ℝ × ℝ) :
    ‖∫ σ, ρ σ • g (x.1 - σ, x.2)‖ₑ ≤ ∫⁻ σ, ‖ρ σ‖ₑ * ‖g (x.1 - σ, x.2)‖ₑ := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  congr 1
  funext σ
  rw [enorm_smul]

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

-- ===== Scratch/CR46Shift.lean =====
/-!
# Translations of the cylinder for `t`-periodic integrands

`∫_cyl H(x + y) = ∫_cyl H(x)` for `H` measurable and `1`-periodic in `t`, and the periodic
extension `perExt h (s, t) = h (s, fract t)`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- Periodic extension in `t` of a function on the strip. -/
def perExt {β : Type*} (h : ℝ × ℝ → β) : ℝ × ℝ → β := fun z => h (z.1, Int.fract z.2)

lemma perExt_per {β : Type*} (h : ℝ × ℝ → β) (s t : ℝ) : perExt h (s, t + 1) = perExt h (s, t) := by
  simp [perExt, Int.fract_add_one]

lemma perExt_of_mem {β : Type*} (h : ℝ × ℝ → β) {x : ℝ × ℝ} (hx : x.2 ∈ Set.Ico (0 : ℝ) 1) :
    perExt h x = h x := by
  simp only [perExt, Int.fract_eq_self.2 hx]

lemma perExt_ae {β : Type*} (h : ℝ × ℝ → β) : perExt h =ᵐ[cylMeasure] h := by
  unfold cylMeasure
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
  exact perExt_of_mem h hx.2

lemma measurable_perMap : Measurable fun z : ℝ × ℝ => (z.1, Int.fract z.2) :=
  measurable_fst.prodMk (measurable_fract.comp measurable_snd)

lemma perExt_stronglyMeasurable {β : Type*} [TopologicalSpace β] {h : ℝ × ℝ → β}
    (hh : StronglyMeasurable h) : StronglyMeasurable (perExt h) :=
  hh.comp_measurable measurable_perMap

/-- A `t`-periodic function only sees `fract t`. -/
lemma per_fract {β : Type*} {F : ℝ × ℝ → β} (hF : ∀ s t, F (s, t + 1) = F (s, t)) (s t : ℝ) :
    F (s, Int.fract t) = F (s, t) := by
  have hp : Function.Periodic (fun t => F (s, t)) 1 := fun t => hF s t
  have := hp.sub_int_mul_eq (x := t) ⌊t⌋
  rw [mul_one] at this
  exact this

/-- Periodic integrals over a period do not depend on the period interval. -/
lemma per_lintegral_Ioc {k : ℝ → ℝ≥0∞} (hk : Function.Periodic k 1) (c : ℝ) :
    ∫⁻ t in Set.Ioc c (c + 1), k t = ∫⁻ t in Set.Ioc (0 : ℝ) 1, k t := by
  have h1 := UnitAddCircle.lintegral_preimage c hk.lift
  have h2 := UnitAddCircle.lintegral_preimage 0 hk.lift
  rw [zero_add] at h2
  have e : ∀ a : ℝ, hk.lift (a : UnitAddCircle) = k a := fun a => hk.lift_coe a
  simp only [e] at h1 h2
  rw [h1, h2]

lemma per_lintegral_shift {k : ℝ → ℝ≥0∞} (hk : Function.Periodic k 1) (c : ℝ) :
    ∫⁻ t in Set.Ico (0 : ℝ) 1, k (t + c) = ∫⁻ t in Set.Ico (0 : ℝ) 1, k t := by
  rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
  have h := (measurePreserving_add_right (volume : Measure ℝ) c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_addRight c) k (Set.Ioc c (c + 1))
  simp only [Set.preimage_add_const_Ioc, sub_self, add_sub_cancel_left] at h
  exact h.trans (per_lintegral_Ioc hk c)

/-- `∫⁻ over the cylinder` is invariant under translations for `t`-periodic integrands. -/
lemma cyl_lintegral_shift {H : ℝ × ℝ → ℝ≥0∞} (hH : Measurable H)
    (hper : ∀ s t, H (s, t + 1) = H (s, t)) (y : ℝ × ℝ) :
    ∫⁻ x, H (x + y) ∂cylMeasure = ∫⁻ x, H x ∂cylMeasure := by
  rw [sca_cyl_eq_prod, lintegral_prod (fun x => H (x + y)) (hH.comp (measurable_id.add_const y)).aemeasurable,
    lintegral_prod _ hH.aemeasurable]
  have h1 : ∀ s : ℝ, ∫⁻ t in Set.Ico (0 : ℝ) 1, H ((s, t) + y) =
      ∫⁻ t in Set.Ico (0 : ℝ) 1, H (s + y.1, t) := by
    intro s
    have hp : Function.Periodic (fun t => H (s + y.1, t)) 1 := fun t => hper _ t
    exact per_lintegral_shift hp y.2
  simp_rw [h1]
  exact lintegral_add_right_eq_self (fun s => ∫⁻ t in Set.Ico (0 : ℝ) 1, H (s, t)) y.1

/-- The cylinder translation `x ↦ (x.1 + y.1, fract (x.2 + y.2))` preserves `cylMeasure`. -/
lemma cyl_mp (y : ℝ × ℝ) :
    MeasurePreserving (fun x : ℝ × ℝ => (x.1 + y.1, Int.fract (x.2 + y.2))) cylMeasure
      cylMeasure := by
  have hT : Measurable (fun x : ℝ × ℝ => (x.1 + y.1, Int.fract (x.2 + y.2))) :=
    measurable_perMap.comp (measurable_id.add_const y)
  refine ⟨hT, ?_⟩
  ext A hA
  rw [Measure.map_apply hT hA]
  have hI : Measurable (A.indicator (1 : ℝ × ℝ → ℝ≥0∞)) := measurable_one.indicator hA
  have key := cyl_lintegral_shift (H := fun z => A.indicator 1 (z.1, Int.fract z.2))
    (hI.comp measurable_perMap) (fun s t => by simp [Int.fract_add_one]) y
  rw [← lintegral_indicator_one (hT hA), ← lintegral_indicator_one hA]
  have e1 : ∀ x : ℝ × ℝ, ((fun x : ℝ × ℝ => (x.1 + y.1, Int.fract (x.2 + y.2))) ⁻¹' A).indicator
      (1 : ℝ × ℝ → ℝ≥0∞) x = A.indicator 1 ((x + y).1, Int.fract (x + y).2) := by
    intro x
    rfl
  simp_rw [e1]
  rw [key]
  refine lintegral_congr_ae ?_
  filter_upwards [perExt_ae (A.indicator (1 : ℝ × ℝ → ℝ≥0∞))] with x hx
  exact hx

/-- Bochner version of the translation invariance. -/
lemma cyl_integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × ℝ → E} (hF : StronglyMeasurable F) (hper : ∀ s t, F (s, t + 1) = F (s, t))
    (y : ℝ × ℝ) : ∫ x, F (x + y) ∂cylMeasure = ∫ x, F x ∂cylMeasure := by
  have hmp := cyl_mp y
  have e : ∀ x : ℝ × ℝ, F (x + y) = F (x.1 + y.1, Int.fract (x.2 + y.2)) := by
    intro x
    rw [per_fract hper]
    rfl
  simp_rw [e]
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map hmp.measurable.aemeasurable]
  rw [hmp.map_eq]
  exact hF.aestronglyMeasurable

end

end CauchyRiemannIndex

-- ===== Scratch/CR46Moll.lean =====
/-!
# Convolution of the periodic extension with a bump on `ℝ²`

`moll φ h = φ.normed ⋆ perExt h`: smooth, `t`-periodic, compactly supported in `s` when `h` is,
and `‖moll φ h‖_{L^p(cyl)} ≤ ‖h‖_{L^p(cyl)}`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

variable {n : ℕ}

instance c46_haar : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

lemma per_lintegral_Ioc_nat {k : ℝ → ℝ≥0∞} (hk : Function.Periodic k 1) (c : ℝ) (L : ℕ) :
    ∫⁻ t in Set.Ioc c (c + L), k t = L * ∫⁻ t in Set.Ioc (0 : ℝ) 1, k t := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hsplit : Set.Ioc c (c + ((L + 1 : ℕ) : ℝ)) =
        Set.Ioc c (c + L) ∪ Set.Ioc (c + L) (c + L + 1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (le_add_of_nonneg_right (Nat.cast_nonneg L)) (by linarith)]
      congr 1
      push_cast
      ring
    have hdisj : Disjoint (Set.Ioc c (c + L)) (Set.Ioc (c + L) (c + L + 1)) :=
      Set.disjoint_left.2 fun x h1 h2 => by linarith [h1.2, h2.1]
    rw [hsplit, lintegral_union measurableSet_Ioc hdisj, ih, per_lintegral_Ioc hk]
    push_cast
    ring

lemma perExt_locallyIntegrable {p : ℝ≥0∞} [Fact (1 ≤ p)] {h : ℝ × ℝ → Vec n}
    (hh : StronglyMeasurable h) (hm : MemLp h p cylMeasure) :
    LocallyIntegrable (perExt h) volume := by
  have hp1 : 1 ≤ p := Fact.out
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨N, hN⟩ := exists_nat_ge r
  set L : ℕ := 2 * N + 2
  have hsub : K ⊆ Set.Icc (-(N : ℝ)) N ×ˢ Set.Ioc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + L) := by
    intro x hx
    have h0 := hr hx
    rw [Metric.mem_closedBall, dist_zero_right] at h0
    have h1 : |x.1| ≤ N := by
      have := norm_fst_le x; rw [Real.norm_eq_abs] at this; linarith
    have h2 : |x.2| ≤ N := by
      have := norm_snd_le x; rw [Real.norm_eq_abs] at this; linarith
    refine ⟨⟨(abs_le.1 h1).1, (abs_le.1 h1).2⟩, ?_, ?_⟩
    · linarith [(abs_le.1 h2).1]
    · have : (L : ℝ) = 2 * N + 2 := by simp [L]
      linarith [(abs_le.1 h2).2]
  refine IntegrableOn.mono_set ?_ hsub
  have hEm : Measurable fun x => ‖perExt h x‖ₑ := (perExt_stronglyMeasurable hh).measurable.enorm
  refine ⟨(perExt_stronglyMeasurable hh).aestronglyMeasurable, ?_⟩
  show ∫⁻ x in _, ‖perExt h x‖ₑ < ⊤
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hEm.aemeasurable]
  have hinner : ∀ s : ℝ, ∫⁻ t in Set.Ioc (-(N : ℝ) - 1) (-(N : ℝ) - 1 + L), ‖perExt h (s, t)‖ₑ =
      L * ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖h (s, t)‖ₑ := by
    intro s
    rw [per_lintegral_Ioc_nat (k := fun t => ‖perExt h (s, t)‖ₑ)
      (fun t => by simp only [perExt_per])]
    congr 1
    rw [← Measure.restrict_congr_set Ico_ae_eq_Ioc]
    refine setLIntegral_congr_fun measurableSet_Ico (fun t ht => ?_)
    rw [perExt_of_mem h (x := (s, t)) ht]
  simp_rw [hinner]
  rw [lintegral_const_mul]
  · refine ENNReal.mul_lt_top (by simp) ?_
    have hset : MeasurableSet (Set.Icc (-(N : ℝ)) N ×ˢ (Set.univ : Set ℝ)) :=
      measurableSet_Icc.prod MeasurableSet.univ
    have hfin : cylMeasure (Set.Icc (-(N : ℝ)) N ×ˢ (Set.univ : Set ℝ)) ≠ ⊤ := by
      rw [sca_cyl_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    haveI : IsFiniteMeasure (cylMeasure.restrict (Set.Icc (-(N : ℝ)) N ×ˢ (Set.univ : Set ℝ))) :=
      isFiniteMeasure_restrict.2 hfin
    have hint := ((hm.restrict (Set.Icc (-(N : ℝ)) N ×ˢ (Set.univ : Set ℝ))).integrable hp1).2
    have e : ∫⁻ x in Set.Icc (-(N : ℝ)) N ×ˢ (Set.univ : Set ℝ), ‖h x‖ₑ ∂cylMeasure =
        ∫⁻ s in Set.Icc (-(N : ℝ)) N, ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖h (s, t)‖ₑ := by
      rw [sca_cyl_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
        lintegral_prod _ hh.measurable.enorm.aemeasurable]
    rw [← e]
    exact hint
  · exact Measurable.lintegral_prod_right' (f := fun x : ℝ × ℝ => ‖h x‖ₑ) hh.measurable.enorm

/-- The mollified periodic extension. -/
def moll (φ : ContDiffBump (0 : ℝ × ℝ)) (h : ℝ × ℝ → Vec n) : ℝ × ℝ → Vec n :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] perExt h

lemma moll_apply (φ : ContDiffBump (0 : ℝ × ℝ)) (h : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    moll φ h x = ∫ y, φ.normed volume y • perExt h (x - y) := by
  rw [moll, convolution_lsmul]

lemma moll_contDiff (φ : ContDiffBump (0 : ℝ × ℝ)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {h : ℝ × ℝ → Vec n} (hh : StronglyMeasurable h) (hm : MemLp h p cylMeasure) :
    ContDiff ℝ ∞ (moll φ h) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (perExt_locallyIntegrable hh hm)

lemma moll_per (φ : ContDiffBump (0 : ℝ × ℝ)) (h : ℝ × ℝ → Vec n) (s t : ℝ) :
    moll φ h (s, t + 1) = moll φ h (s, t) := by
  rw [moll_apply, moll_apply]
  congr 1
  funext y
  simp only [perExt, Prod.fst_sub, Prod.snd_sub]
  rw [show t + 1 - y.2 = (t - y.2) + 1 by ring, Int.fract_add_one]

lemma normed_eq_zero_of_le (φ : ContDiffBump (0 : ℝ × ℝ)) {y : ℝ × ℝ} (hy : φ.rOut ≤ ‖y‖) :
    φ.normed volume y = 0 := by
  have : y ∉ Function.support (φ.normed volume) := by
    rw [φ.support_normed_eq, Metric.mem_ball, dist_zero_right]
    exact not_lt.2 hy
  exact Function.notMem_support.1 this

lemma moll_vanish (φ : ContDiffBump (0 : ℝ × ℝ)) (hφ : φ.rOut ≤ 1) {h : ℝ × ℝ → Vec n} {R : ℝ}
    (hR : ∀ s t, R < |s| → h (s, t) = 0) : ∀ s t, R + 1 < |s| → moll φ h (s, t) = 0 := by
  intro s t hs
  rw [moll_apply]
  have hz : ∀ y : ℝ × ℝ, φ.normed volume y • perExt h ((s, t) - y) = 0 := by
    intro y
    by_cases hy : φ.rOut ≤ ‖y‖
    · rw [normed_eq_zero_of_le φ hy, zero_smul]
    · push_neg at hy
      have h1 : |y.1| < 1 := by
        have := norm_fst_le y; rw [Real.norm_eq_abs] at this; linarith
      have h2 : R < |s - y.1| := by
        have := abs_sub_abs_le_abs_sub s y.1
        linarith
      simp only [perExt, Prod.fst_sub, Prod.snd_sub]
      rw [hR _ _ h2, smul_zero]
  simp [hz]

lemma moll_isTestSection (φ : ContDiffBump (0 : ℝ × ℝ)) (hφ : φ.rOut ≤ 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {h : ℝ × ℝ → Vec n} (hh : StronglyMeasurable h) (hm : MemLp h p cylMeasure)
    {R : ℝ} (hR : ∀ s t, R < |s| → h (s, t) = 0) : IsTestSection (moll φ h) :=
  ⟨moll_contDiff φ hh hm, moll_per φ h, R + 1, moll_vanish φ hφ hR⟩

/-- Hölder with weight `a`: `(∫ a b)^q ≤ (∫ a)^{q-1} ∫ a b^q`, any measure. -/
lemma lint_jensen {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ} (hq : 1 ≤ q)
    {a b : α → ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) :
    (∫⁻ σ, a σ * b σ ∂μ) ^ q ≤ (∫⁻ σ, a σ ∂μ) ^ (q - 1) * ∫⁻ σ, a σ * b σ ^ q ∂μ := by
  have hq0 : 0 < q := by linarith
  have hi0 : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hi1 : 0 ≤ 1 - q⁻¹ := by
    have : q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
    linarith
  have key := ENNReal.lintegral_mul_norm_pow_le (μ := μ)
    (f := fun σ => a σ * b σ ^ q) (g := a) (ha.mul (hb.pow_const q)).aemeasurable
    ha.aemeasurable hi0 hi1 (by ring)
  have hpt : ∀ σ, (a σ * b σ ^ q) ^ q⁻¹ * a σ ^ (1 - q⁻¹) = a σ * b σ := by
    intro σ
    rw [ENNReal.mul_rpow_of_nonneg _ _ hi0, ENNReal.rpow_rpow_inv hq0.ne', mul_comm (a σ ^ q⁻¹),
      mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hi0 hi1,
      show q⁻¹ + (1 - q⁻¹) = (1 : ℝ) by ring, ENNReal.rpow_one, mul_comm]
  rw [show (fun σ => (a σ * b σ ^ q) ^ q⁻¹ * a σ ^ (1 - q⁻¹)) = fun σ => a σ * b σ from
    funext hpt] at key
  calc (∫⁻ σ, a σ * b σ ∂μ) ^ q
      ≤ ((∫⁻ σ, a σ * b σ ^ q ∂μ) ^ q⁻¹ * (∫⁻ σ, a σ ∂μ) ^ (1 - q⁻¹)) ^ q :=
        ENNReal.rpow_le_rpow key hq0.le
    _ = (∫⁻ σ, a σ ∂μ) ^ (q - 1) * ∫⁻ σ, a σ * b σ ^ q ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          inv_mul_cancel₀ hq0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        field_simp

lemma lintegral_enorm_normed (φ : ContDiffBump (0 : ℝ × ℝ)) :
    ∫⁻ y, ‖φ.normed volume y‖ₑ = 1 := by
  simp_rw [Real.enorm_eq_ofReal (φ.nonneg_normed _)]
  rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
    (ae_of_all _ φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]

lemma moll_lintegral_le (φ : ContDiffBump (0 : ℝ × ℝ)) {q : ℝ} (hq : 1 ≤ q)
    {h : ℝ × ℝ → Vec n} (hh : StronglyMeasurable h) :
    ∫⁻ x, ‖moll φ h x‖ₑ ^ q ∂cylMeasure ≤ ∫⁻ x, ‖h x‖ₑ ^ q ∂cylMeasure := by
  have hq0 : 0 ≤ q := by linarith
  set a : ℝ × ℝ → ℝ≥0∞ := fun y => ‖φ.normed volume y‖ₑ with ha_def
  set b : ℝ × ℝ → ℝ≥0∞ := fun z => ‖perExt h z‖ₑ with hb_def
  have ha : Measurable a := φ.continuous_normed.measurable.enorm
  have hb : Measurable b := (perExt_stronglyMeasurable hh).measurable.enorm
  have ha1 : ∫⁻ y, a y = 1 := lintegral_enorm_normed φ
  have hbper : ∀ s t, b (s, t + 1) ^ q = b (s, t) ^ q := by
    intro s t; simp only [hb_def, perExt_per]
  have hpt : ∀ x : ℝ × ℝ, ‖moll φ h x‖ₑ ^ q ≤ ∫⁻ y, a y * b (x - y) ^ q := by
    intro x
    have h1 : ‖moll φ h x‖ₑ ≤ ∫⁻ y, a y * b (x - y) := by
      rw [moll_apply]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      congr 1
      funext y
      rw [enorm_smul]
    calc ‖moll φ h x‖ₑ ^ q ≤ (∫⁻ y, a y * b (x - y)) ^ q := ENNReal.rpow_le_rpow h1 hq0
      _ ≤ (∫⁻ y, a y) ^ (q - 1) * ∫⁻ y, a y * b (x - y) ^ q :=
          lint_jensen hq ha (hb.comp (measurable_const.sub measurable_id))
      _ = ∫⁻ y, a y * b (x - y) ^ q := by rw [ha1, ENNReal.one_rpow, one_mul]
  have hmeas : Measurable fun p : (ℝ × ℝ) × (ℝ × ℝ) => a p.2 * b (p.1 - p.2) ^ q :=
    (ha.comp measurable_snd).mul ((hb.comp (measurable_fst.sub measurable_snd)).pow_const q)
  calc ∫⁻ x, ‖moll φ h x‖ₑ ^ q ∂cylMeasure
      ≤ ∫⁻ x, (∫⁻ y, a y * b (x - y) ^ q) ∂cylMeasure := lintegral_mono hpt
    _ = ∫⁻ y, (∫⁻ x, a y * b (x - y) ^ q ∂cylMeasure) := lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ y, a y * ∫⁻ x, b x ^ q ∂cylMeasure := by
        congr 1
        funext y
        rw [lintegral_const_mul _ (f := fun x => b (x - y) ^ q) ((hb.comp (measurable_id.sub_const y)).pow_const q)]
        congr 1
        have := cyl_lintegral_shift (H := fun z => b z ^ q) (hb.pow_const q) hbper (-y)
        simpa [sub_eq_add_neg] using this
    _ = ∫⁻ x, b x ^ q ∂cylMeasure := by rw [lintegral_mul_const _ ha, ha1, one_mul]
    _ = ∫⁻ x, ‖h x‖ₑ ^ q ∂cylMeasure := by
        refine lintegral_congr_ae ?_
        filter_upwards [perExt_ae h] with x hx
        simp only [hb_def, hx]

lemma moll_eLpNorm_le (φ : ContDiffBump (0 : ℝ × ℝ)) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    {h : ℝ × ℝ → Vec n} (hh : StronglyMeasurable h) :
    eLpNorm (moll φ h) p cylMeasure ≤ eLpNorm h p cylMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  have hqr : 1 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp hp1
    simpa using this
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp]
  exact ENNReal.rpow_le_rpow (moll_lintegral_le φ hqr hh) (by positivity)

end

end CauchyRiemannIndex

-- ===== Scratch/CR46Conv.lean =====
/-!
# `moll φₖ h → h` in `L^p` of the cylinder

For continuous compactly supported `c` by dominated convergence, in general by density and the
uniform bound `‖moll φ h‖_p ≤ ‖h‖_p`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

variable {n : ℕ}

/-- Bumps with `rOut = 1 / (k + 2)`. -/
def bumpSeq (k : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := 1 / (2 * ((k : ℝ) + 2))
  rOut := 1 / ((k : ℝ) + 2)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)])

lemma bumpSeq_rOut_le (k : ℕ) : (bumpSeq k).rOut ≤ 1 := by
  show 1 / ((k : ℝ) + 2) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]

lemma bumpSeq_tendsto : Tendsto (fun k => (bumpSeq k).rOut) atTop (𝓝 0) := by
  show Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
  exact Tendsto.div_atTop tendsto_const_nhds
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ))))

lemma c46_ae_strip : ∀ᵐ x ∂cylMeasure, x.2 ∈ Set.Ico (0 : ℝ) 1 := by
  unfold cylMeasure
  filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
  exact hx.2

lemma ae_cyl_Ioo : ∀ᵐ x ∂cylMeasure, x.2 ∈ Set.Ioo (0 : ℝ) 1 := by
  have h0 : cylMeasure {x : ℝ × ℝ | x.2 = 0} = 0 := by
    have : {x : ℝ × ℝ | x.2 = 0} = Set.univ ×ˢ {0} := by ext x; simp
    rw [this, sca_cyl_eq_prod, Measure.prod_prod]
    simp
  have h0' := measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [h0', c46_ae_strip] with x hx hx'
  exact ⟨lt_of_le_of_ne hx'.1 (fun h => hx h.symm), hx'.2⟩

lemma moll_tendsto_of_continuous {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {c : ℝ × ℝ → Vec n}
    (hc : Continuous c) (hcs : HasCompactSupport c) :
    Tendsto (fun k => eLpNorm (moll (bumpSeq k) c - c) p cylMeasure) atTop (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s t, R < |s| → c (s, t) = 0 := by
    obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun s t hs => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
    have h1 := hR _ hm
    have h2 := norm_fst_le (s, t)
    rw [Real.norm_eq_abs] at h2
    linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set K : Set (ℝ × ℝ) := Set.Icc (-(R + 1)) (R + 1) ×ˢ Set.univ with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hKf : cylMeasure K ≠ ⊤ := by
    rw [sca_cyl_eq_prod, hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  have hb : MemLp (K.indicator fun _ => 2 * M) p cylMeasure :=
    memLp_indicator_const p hKm (2 * M) (Or.inr hKf)
  have hmc : ∀ k, Continuous (moll (bumpSeq k) c) := fun k =>
    (moll_contDiff (bumpSeq k) (p := p) hc.stronglyMeasurable
      (memLp_of_vanish c hc R hR)).continuous
  refine tendsto_eLpNorm_zero_of_dominated hp0 hp hb
    (fun k => ((hmc k).sub hc).aestronglyMeasurable) (fun k => ae_of_all _ fun x => ?_) ?_
  · -- domination
    have hvan := moll_vanish (bumpSeq k) (bumpSeq_rOut_le k) hR
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have h1 : ‖moll (bumpSeq k) c x‖ ≤ M := by
        rw [moll_apply]
        refine (norm_integral_le_of_norm_le ((bumpSeq k).integrable_normed.mul_const M)
          (ae_of_all _ fun y => ?_)).trans ?_
        · rw [norm_smul, Real.norm_of_nonneg ((bumpSeq k).nonneg_normed y)]
          exact mul_le_mul_of_nonneg_left (hM _) ((bumpSeq k).nonneg_normed y)
        · rw [integral_mul_const, (bumpSeq k).integral_normed, one_mul]
      calc ‖moll (bumpSeq k) c x - c x‖ ≤ ‖moll (bumpSeq k) c x‖ + ‖c x‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add h1 (hM x)
        _ = 2 * M := by ring
    · rw [Set.indicator_of_notMem hx]
      have hs : R + 1 < |x.1| := by
        by_contra h
        push_neg at h
        exact hx ⟨abs_le.1 h, Set.mem_univ _⟩
      have hs' : R < |x.1| := by linarith
      have e1 : moll (bumpSeq k) c x = 0 := hvan x.1 x.2 hs
      have e2 : c x = 0 := hR x.1 x.2 hs'
      simp only [Pi.sub_apply, e1, e2, sub_zero, norm_zero, le_refl]
  · -- pointwise convergence
    filter_upwards [ae_cyl_Ioo] with x hx
    have hev : perExt c =ᶠ[𝓝 x] c := by
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hx] with z hz
      exact perExt_of_mem c ⟨hz.1.le, hz.2⟩
    have hca : ContinuousAt (perExt c) x := hc.continuousAt.congr hev.symm
    have ht := ContDiffBump.convolution_tendsto_right (μ := volume) (φ := bumpSeq)
      (g := fun _ => perExt c) (k := fun _ => x) bumpSeq_tendsto
      (Eventually.of_forall fun _ => (perExt_stronglyMeasurable hc.stronglyMeasurable).aestronglyMeasurable)
      (hca.tendsto.comp tendsto_snd) tendsto_const_nhds
    rw [perExt_of_mem c ⟨hx.1.le, hx.2⟩] at ht
    have := ht.sub_const (c x)
    rw [sub_self] at this
    exact this

/-- `moll φₖ h → h` in `L^p` of the cylinder. -/
lemma moll_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {h : ℝ × ℝ → Vec n}
    (hh : StronglyMeasurable h) (hm : MemLp h p cylMeasure) :
    Tendsto (fun k => eLpNorm (moll (bumpSeq k) h - h) p cylMeasure) atTop (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  have hδ : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  set S : Set (ℝ × ℝ) := Set.univ ×ˢ Set.Ico (0 : ℝ) 1 with hS
  have hSm : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ico
  have hmi : MemLp (S.indicator h) p volume := (memLp_indicator_iff_restrict hSm).2 hm
  obtain ⟨c, hcs, hcd, hc, -⟩ := hmi.exists_hasCompactSupport_eLpNorm_sub_le hp hδ
  have hhc : eLpNorm (h - c) p cylMeasure ≤ ε / 3 := by
    have e1 : eLpNorm (h - c) p cylMeasure = eLpNorm (S.indicator (h - c)) p volume :=
      (eLpNorm_indicator_eq_eLpNorm_restrict hSm).symm
    have e2 : S.indicator (h - c) = S.indicator (S.indicator h - c) := by
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, Pi.sub_apply]
      · simp only [Set.indicator_of_notMem hx]
    rw [e1, e2]
    exact (eLpNorm_indicator_le _).trans hcd
  have hcm : MemLp c p cylMeasure := by
    obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.exists_norm_le
    refine memLp_of_vanish c hc R fun s t hs => image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have h1 := hR _ hmem
    have h2 := norm_fst_le (s, t)
    rw [Real.norm_eq_abs] at h2
    linarith
  have hd : StronglyMeasurable (h - c) := hh.sub hc.stronglyMeasurable
  have hdm : MemLp (h - c) p cylMeasure := hm.sub hcm
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 (moll_tendsto_of_continuous hp hc hcs)) (ε / 3)
    (ENNReal.div_pos hε.ne' (by norm_num))
  refine ⟨N, fun k hk => ?_⟩
  have hsplit : moll (bumpSeq k) h - h =
      moll (bumpSeq k) (h - c) + (moll (bumpSeq k) c - c) + (c - h) := by
    have hE : perExt h = perExt (h - c) + perExt c := by
      funext x; simp only [perExt, Pi.add_apply, Pi.sub_apply, sub_add_cancel]
    have hlin : moll (bumpSeq k) h = moll (bumpSeq k) (h - c) + moll (bumpSeq k) c := by
      unfold moll
      rw [hE]
      exact ConvolutionExists.distrib_add
        ((bumpSeq k).hasCompactSupport_normed.convolutionExists_left _
          (bumpSeq k).continuous_normed (perExt_locallyIntegrable hd hdm))
        ((bumpSeq k).hasCompactSupport_normed.convolutionExists_left _
          (bumpSeq k).continuous_normed (perExt_locallyIntegrable hc.stronglyMeasurable hcm))
    rw [hlin]
    abel
  have hA : AEStronglyMeasurable (moll (bumpSeq k) (h - c)) cylMeasure :=
    (moll_contDiff (bumpSeq k) hd hdm).continuous.aestronglyMeasurable
  have hB : AEStronglyMeasurable (moll (bumpSeq k) c - c) cylMeasure :=
    ((moll_contDiff (bumpSeq k) hc.stronglyMeasurable hcm).continuous.sub hc).aestronglyMeasurable
  have hC : AEStronglyMeasurable (c - h) cylMeasure :=
    (hc.stronglyMeasurable.sub hh).aestronglyMeasurable
  rw [hsplit]
  calc eLpNorm (moll (bumpSeq k) (h - c) + (moll (bumpSeq k) c - c) + (c - h)) p cylMeasure
      ≤ eLpNorm (moll (bumpSeq k) (h - c)) p cylMeasure +
          eLpNorm (moll (bumpSeq k) c - c) p cylMeasure + eLpNorm (c - h) p cylMeasure :=
        (eLpNorm_add_le (hA.add hB) hC hp1).trans
          (add_le_add (eLpNorm_add_le hA hB hp1) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        refine add_le_add (add_le_add ((moll_eLpNorm_le (bumpSeq k) hp hd).trans hhc) (hN k hk)) ?_
        rw [eLpNorm_sub_comm]; exact hhc
    _ = ε := ENNReal.add_thirds ε

end

end CauchyRiemannIndex

-- ===== Scratch/CR46Weak.lean =====
/-!
# Weak solutions of `∂ₛη + J₀∂ₜη = g`: the mollified pair is a classical solution

`∫ ⟨Φ, moll φ h⟩ = ∫_y ρ(y) ∫ ⟨Φ(· + y), h⟩` (Fubini plus the cylinder shift), so translating the
test section transfers the weak identity to `(moll φ η, moll φ g)`; then the formal adjoint
identity identifies `D₀ (moll φ η)` with `moll φ g`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

variable {n : ℕ}

/-- `D₀^* ψ = -∂ₛψ + J₀ ∂ₜψ`. -/
def adj0 (ψ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  -partialS ψ x + Matrix.toEuclideanLin (J₀ n) (partialT ψ x)

/-- `∂ₛη + J₀∂ₜη = g` weakly on the cylinder. -/
def IsWeak0 (η g : ℝ × ℝ → Vec n) : Prop :=
  ∀ ψ : ℝ × ℝ → Vec n, IsTestSection ψ →
    ∫ x, inner ℝ (adj0 ψ x) (η x) ∂cylMeasure = ∫ x, inner ℝ (ψ x) (g x) ∂cylMeasure

lemma isTestSection_shift (y : ℝ × ℝ) {ψ : ℝ × ℝ → Vec n} (hψ : IsTestSection ψ) :
    IsTestSection (fun x : ℝ × ℝ => ψ (x + y)) := by
  obtain ⟨R, hR⟩ := hψ.2.2
  refine ⟨hψ.1.comp (contDiff_id.add contDiff_const), ?_, R + |y.1|, ?_⟩
  · intro s t
    show ψ (s + y.1, t + 1 + y.2) = ψ (s + y.1, t + y.2)
    rw [add_right_comm]
    exact hψ.2.1 _ _
  · intro s t hs
    show ψ (s + y.1, t + y.2) = 0
    apply hR
    have h1 := abs_add_le (s + y.1) (-y.1)
    rw [abs_neg, add_neg_cancel_right] at h1
    linarith

lemma partialS_shift (y : ℝ × ℝ) (ψ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialS (fun x : ℝ × ℝ => ψ (x + y)) x = partialS ψ (x + y) := by
  simp only [partialS]
  rw [fderiv_comp_add_right]

lemma partialT_shift (y : ℝ × ℝ) (ψ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    partialT (fun x : ℝ × ℝ => ψ (x + y)) x = partialT ψ (x + y) := by
  simp only [partialT]
  rw [fderiv_comp_add_right]

lemma adj0_shift (y : ℝ × ℝ) (ψ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) :
    adj0 (fun x : ℝ × ℝ => ψ (x + y)) x = adj0 ψ (x + y) := by
  simp only [adj0, partialS_shift, partialT_shift]

lemma shift_eq_of_per {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) :
    (fun x : ℝ × ℝ => ψ (x + (0, 1))) = ψ := by
  funext x
  show ψ (x.1 + 0, x.2 + 1) = ψ x
  rw [add_zero, hper]

lemma partialS_per {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) (s t : ℝ) :
    partialS ψ (s, t + 1) = partialS ψ (s, t) := by
  have := partialS_shift (0, 1) ψ (s, t)
  rw [shift_eq_of_per hper] at this
  rw [this]
  simp

lemma partialT_per {ψ : ℝ × ℝ → Vec n} (hper : ∀ s t, ψ (s, t + 1) = ψ (s, t)) (s t : ℝ) :
    partialT ψ (s, t + 1) = partialT ψ (s, t) := by
  have := partialT_shift (0, 1) ψ (s, t)
  rw [shift_eq_of_per hper] at this
  rw [this]
  simp

lemma adj0_continuous {ψ : ℝ × ℝ → Vec n} (hψ : IsTestSection ψ) : Continuous (adj0 ψ) :=
  hψ.continuous_partialS.neg.add ((matCLM n (J₀ n)).continuous.comp hψ.continuous_partialT)

lemma adj0_per {ψ : ℝ × ℝ → Vec n} (hψ : IsTestSection ψ) (s t : ℝ) :
    adj0 ψ (s, t + 1) = adj0 ψ (s, t) := by
  simp only [adj0, partialS_per hψ.2.1, partialT_per hψ.2.1]

lemma adj0_vanish {ψ : ℝ × ℝ → Vec n} {R : ℝ} (hR : ∀ s t, R < |s| → ψ (s, t) = 0) (s t : ℝ)
    (hs : R < |s|) : adj0 ψ (s, t) = 0 := by
  simp only [adj0, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, neg_zero, map_zero,
    add_zero]

lemma perExt_sub_per {β : Type*} (h : ℝ × ℝ → β) (y : ℝ × ℝ) (s t : ℝ) :
    perExt h ((s, t + 1) - y) = perExt h ((s, t) - y) := by
  simp only [perExt, Prod.fst_sub, Prod.snd_sub]
  rw [show t + 1 - y.2 = (t - y.2) + 1 by ring, Int.fract_add_one]

lemma c46_enorm_inner_le (a b : Vec n) : ‖inner ℝ a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm a b)

lemma exists_bound_per {E : Type*} [NormedAddCommGroup E] {Φ : ℝ × ℝ → E} (hΦ : Continuous Φ)
    (hΦper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) {R : ℝ} (hΦR : ∀ s t, R < |s| → Φ (s, t) = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hΦ.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : R < |x.1|
  · have : Φ x = 0 := hΦR x.1 x.2 hx
    rw [this, norm_zero]
    exact le_max_right _ _
  · push_neg at hx
    have e : Φ x = Φ (x.1, Int.fract x.2) := (per_fract hΦper x.1 x.2).symm
    rw [e]
    refine (hM _ (Set.mk_mem_prod (Set.mem_Icc.2 (abs_le.1 hx))
      (Set.mem_Icc.2 ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩))).trans
      (le_max_left _ _)

/-- Fubini and the cylinder shift for `⟨Φ, moll φ h⟩`. -/
lemma integral_inner_moll (φ : ContDiffBump (0 : ℝ × ℝ)) (hφ : φ.rOut ≤ 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {Φ : ℝ × ℝ → Vec n} (hΦ : Continuous Φ)
    (hΦper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) {R : ℝ} (hΦR : ∀ s t, R < |s| → Φ (s, t) = 0)
    {h : ℝ × ℝ → Vec n} (hh : StronglyMeasurable h) (hm : MemLp h p cylMeasure) :
    ∫ x, inner ℝ (Φ x) (moll φ h x) ∂cylMeasure =
      ∫ y, φ.normed volume y * ∫ x, inner ℝ (Φ (x + y)) (h x) ∂cylMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  set ρ := φ.normed volume with hρ
  have hρc : Continuous ρ := φ.continuous_normed (μ := volume)
  have hEs : StronglyMeasurable (perExt h) := perExt_stronglyMeasurable hh
  have hEl := perExt_locallyIntegrable hh hm
  have hconv := φ.hasCompactSupport_normed.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hρc hEl
  obtain ⟨M, hM0, hM⟩ := exists_bound_per hΦ hΦper hΦR
  set K' : Set (ℝ × ℝ) := Set.Icc (-(R + 1)) (R + 1) ×ˢ Set.univ with hK'
  have hK'm : MeasurableSet K' := measurableSet_Icc.prod MeasurableSet.univ
  set G : ℝ × ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal M * K'.indicator (fun x => ‖h x‖ₑ) x with hG
  have hGm : Measurable G := measurable_const.mul (hh.measurable.enorm.indicator hK'm)
  have hGf : ∫⁻ x, G x ∂cylMeasure < ⊤ := by
    have hK'f : cylMeasure K' ≠ ⊤ := by
      rw [sca_cyl_eq_prod, hK', Measure.prod_prod]
      exact ENNReal.mul_ne_top (by simp) (by simp)
    haveI : IsFiniteMeasure (cylMeasure.restrict K') := isFiniteMeasure_restrict.2 hK'f
    have hgi : ∫⁻ y in K', ‖h y‖ₑ ∂cylMeasure < ⊤ := ((hm.restrict K').integrable hp1).2
    rw [hG, lintegral_const_mul _ (hh.measurable.enorm.indicator hK'm), lintegral_indicator hK'm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgi
  -- pointwise bound after the shift
  have hptG : ∀ y : ℝ × ℝ, ρ y ≠ 0 → ∀ x, ‖Φ (x + y)‖ₑ * ‖h x‖ₑ ≤ G x := by
    intro y hy x
    have hy1 : |y.1| < 1 := by
      by_contra hc
      push_neg at hc
      have : φ.rOut ≤ ‖y‖ := by
        have := norm_fst_le y; rw [Real.norm_eq_abs] at this; linarith
      exact hy (normed_eq_zero_of_le φ this)
    by_cases hx : x ∈ K'
    · simp only [hG, Set.indicator_of_mem hx]
      gcongr
      rw [← ofReal_norm_eq_enorm]
      exact ENNReal.ofReal_le_ofReal (hM _)
    · have hxs : R + 1 < |x.1| := by
        by_contra hc
        push_neg at hc
        exact hx ⟨abs_le.1 hc, Set.mem_univ _⟩
      have hs : R < |(x + y).1| := by
        have := abs_sub_abs_le_abs_sub x.1 (-y.1)
        rw [abs_neg, sub_neg_eq_add] at this
        show R < |x.1 + y.1|
        linarith
      have : Φ (x + y) = 0 := hΦR _ (x + y).2 hs
      simp [this]
  -- the shifted lintegral identity
  have hshiftL : ∀ y : ℝ × ℝ, ∫⁻ x, ‖Φ x‖ₑ * ‖perExt h (x - y)‖ₑ ∂cylMeasure =
      ∫⁻ x, ‖Φ (x + y)‖ₑ * ‖h x‖ₑ ∂cylMeasure := by
    intro y
    have := cyl_lintegral_shift (H := fun z => ‖Φ z‖ₑ * ‖perExt h (z - y)‖ₑ)
      (hΦ.measurable.enorm.mul (hEs.measurable.enorm.comp (measurable_id.sub_const y)))
      (fun s t => by simp only [hΦper, perExt_sub_per]) y
    rw [← this]
    refine lintegral_congr_ae ?_
    filter_upwards [perExt_ae h] with x hx
    simp only [add_sub_cancel_right, hx]
  -- integrability on the product
  set Ξ : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q => ρ q.2 * inner ℝ (Φ q.1) (perExt h (q.1 - q.2))
    with hΞ
  have hΞm : StronglyMeasurable Ξ :=
    (hρc.comp continuous_snd).stronglyMeasurable.mul
      (StronglyMeasurable.inner (hΦ.comp continuous_fst).stronglyMeasurable
        (hEs.comp_measurable (measurable_fst.sub measurable_snd)))
  have hΞi : Integrable Ξ (cylMeasure.prod volume) := by
    refine ⟨hΞm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖Ξ q‖ₑ ∂(cylMeasure.prod volume) < ⊤
    have hb : ∀ q, ‖Ξ q‖ₑ ≤ ‖ρ q.2‖ₑ * (‖Φ q.1‖ₑ * ‖perExt h (q.1 - q.2)‖ₑ) := by
      intro q
      simp only [hΞ, enorm_mul]
      gcongr
      exact c46_enorm_inner_le _ _
    have hbm : Measurable fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
        ‖ρ q.2‖ₑ * (‖Φ q.1‖ₑ * ‖perExt h (q.1 - q.2)‖ₑ) :=
      (hρc.measurable.enorm.comp measurable_snd).mul
        ((hΦ.measurable.enorm.comp measurable_fst).mul
          (hEs.measurable.enorm.comp (measurable_fst.sub measurable_snd)))
    refine lt_of_le_of_lt (lintegral_mono hb) ?_
    rw [lintegral_prod _ hbm.aemeasurable, lintegral_lintegral_swap hbm.aemeasurable]
    have hy : ∀ y : ℝ × ℝ, ∫⁻ x, ‖ρ y‖ₑ * (‖Φ x‖ₑ * ‖perExt h (x - y)‖ₑ) ∂cylMeasure ≤
        ‖ρ y‖ₑ * ∫⁻ x, G x ∂cylMeasure := by
      intro y
      rw [lintegral_const_mul _ (f := fun x => ‖Φ x‖ₑ * ‖perExt h (x - y)‖ₑ)
        (hΦ.measurable.enorm.mul (hEs.measurable.enorm.comp (measurable_id.sub_const y))),
        hshiftL y]
      by_cases hy0 : ρ y = 0
      · simp [hy0]
      · exact mul_le_mul' le_rfl (lintegral_mono (hptG y hy0))
    refine lt_of_le_of_lt (lintegral_mono hy) ?_
    rw [lintegral_mul_const _ hρc.measurable.enorm, lintegral_enorm_normed φ, one_mul]
    exact hGf
  -- assemble
  have step1 : ∀ x, inner ℝ (Φ x) (moll φ h x) = ∫ y, Ξ (x, y) := by
    intro x
    rw [moll_apply]
    have hi : Integrable (fun y => ρ y • perExt h (x - y)) := hconv x
    rw [← integral_inner hi (Φ x)]
    congr 1
    funext y
    simp only [hΞ, real_inner_smul_right]
  simp_rw [step1]
  rw [integral_integral_swap hΞi]
  congr 1
  funext y
  simp only [hΞ]
  rw [integral_const_mul]
  congr 1
  have hF : StronglyMeasurable fun x : ℝ × ℝ => inner ℝ (Φ x) (perExt h (x - y)) :=
    StronglyMeasurable.inner hΦ.stronglyMeasurable
      (hEs.comp_measurable (measurable_id.sub_const y))
  rw [← cyl_integral_shift hF (fun s t => by simp only [hΦper, perExt_sub_per]) y]
  refine integral_congr_ae ?_
  filter_upwards [perExt_ae h] with x hx
  simp only [add_sub_cancel_right, hx]


lemma weak_moll (φ : ContDiffBump (0 : ℝ × ℝ)) (hφ : φ.rOut ≤ 1) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {η g : ℝ × ℝ → Vec n} (hη : StronglyMeasurable η) (hηm : MemLp η p cylMeasure)
    (hg : StronglyMeasurable g) (hgm : MemLp g p cylMeasure) (hw : IsWeak0 η g) :
    IsWeak0 (moll φ η) (moll φ g) := by
  intro ψ hψ
  obtain ⟨R, hR⟩ := hψ.2.2
  rw [integral_inner_moll φ hφ (adj0_continuous hψ) (adj0_per hψ) (adj0_vanish hR) hη hηm,
    integral_inner_moll φ hφ hψ.continuous hψ.2.1 hR hg hgm]
  congr 1
  funext y
  congr 1
  have := hw _ (isTestSection_shift y hψ)
  simp only [adj0_shift] at this
  exact this

lemma crOp_zero_eq (u : ℝ × ℝ → Vec n) :
    crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u =
      fun x => partialS u x + Matrix.toEuclideanLin (J₀ n) (partialT u x) := by
  funext x
  simp [crOp]

lemma IsTestSection.partialS_test {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    IsTestSection (partialS u) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨?_, partialS_per hu.2.1, R, fun s t hs => partialS_eq_zero R hR hs⟩
  exact (hu.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma IsTestSection.partialT_test {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    IsTestSection (partialT u) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨?_, partialT_per hu.2.1, R, fun s t hs => partialT_eq_zero R hR hs⟩
  exact (hu.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma IsTestSection.mat {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (A : Mat n) :
    IsTestSection (fun x => Matrix.toEuclideanLin A (u x)) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨(matCLM n A).contDiff.comp hu.1, fun s t => by simp only [hu.2.1], R,
    fun s t hs => by simp only [hR s t hs, map_zero]⟩

lemma integrable_inner_test {u v : ℝ × ℝ → Vec n} (hu : IsTestSection u) (hv : IsTestSection v) :
    Integrable (fun x => inner ℝ (u x) (v x)) cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  have hm : MemLp (fun x => inner ℝ (u x) (v x)) 1 cylMeasure :=
    memLp_of_vanish (p := 1) _ (hu.continuous.inner hv.continuous) R
      (fun s t hs => by simp only [hR s t hs, inner_zero_left])
  exact memLp_one_iff_integrable.1 hm

/-- The mollified pair is a classical solution: `D₀ (moll φ η) = moll φ g`. -/
lemma crOp_zero_moll_ae (φ : ContDiffBump (0 : ℝ × ℝ)) (hφ : φ.rOut ≤ 1) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {η g : ℝ × ℝ → Vec n} (hη : StronglyMeasurable η)
    (hηm : MemLp η p cylMeasure) (hg : StronglyMeasurable g) (hgm : MemLp g p cylMeasure)
    {R : ℝ} (hηR : ∀ s t, R < |s| → η (s, t) = 0) (hgR : ∀ s t, R < |s| → g (s, t) = 0)
    (hw : IsWeak0 η g) :
    crOp (fun _ : ℝ × ℝ => (0 : Mat n)) (moll φ η) =ᵐ[cylMeasure] moll φ g := by
  set u := moll φ η with hu_def
  set v := moll φ g with hv_def
  have hu : IsTestSection u := moll_isTestSection φ hφ hη hηm hηR
  have hv : IsTestSection v := moll_isTestSection φ hφ hg hgm hgR
  set D := crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u with hD
  have hDt : IsTestSection D := by
    rw [hD, crOp_zero_eq]
    exact hu.partialS_test.add (hu.partialT_test.mat (J₀ n))
  set F := D - v with hF
  have hFt : IsTestSection F := hDt.sub hv
  have hadj := crOp_formalAdjoint n (fun _ : ℝ × ℝ => (0 : Mat n)) continuous_const u F hu hFt
  have hadj' : ∀ x, -partialS F x + Matrix.toEuclideanLin (J₀ n) (partialT F x) +
      Matrix.toEuclideanLin ((fun _ : ℝ × ℝ => (0 : Mat n)) x)ᵀ (F x) = adj0 F x := by
    intro x
    simp [adj0]
  simp_rw [hadj'] at hadj
  have hwm := weak_moll φ hφ hη hηm hg hgm hw F hFt
  have h1 : ∫ x, inner ℝ (D x) (F x) ∂cylMeasure = ∫ x, inner ℝ (v x) (F x) ∂cylMeasure := by
    rw [hadj]
    have e1 : ∫ x, inner ℝ (u x) (adj0 F x) ∂cylMeasure = ∫ x, inner ℝ (adj0 F x) (u x) ∂cylMeasure := by
      congr 1; funext x; exact real_inner_comm _ _
    have e2 : ∫ x, inner ℝ (v x) (F x) ∂cylMeasure = ∫ x, inner ℝ (F x) (v x) ∂cylMeasure := by
      congr 1; funext x; exact real_inner_comm _ _
    rw [e1, e2]
    exact hwm
  have h2 : ∫ x, inner ℝ (F x) (F x) ∂cylMeasure = 0 := by
    have e : ∀ x, inner ℝ (F x) (F x) = inner ℝ (D x) (F x) - inner ℝ (v x) (F x) := by
      intro x
      simp only [hF, Pi.sub_apply, inner_sub_left]
    simp_rw [e]
    rw [integral_sub (integrable_inner_test hDt hFt) (integrable_inner_test hv hFt), h1, sub_self]
  have hnn : 0 ≤ᵐ[cylMeasure] fun x => inner ℝ (F x) (F x) :=
    ae_of_all _ fun x => real_inner_self_nonneg
  have h3 := (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_inner_test hFt hFt)).1 h2
  filter_upwards [h3] with x hx
  have hx' : F x = 0 := inner_self_eq_zero.1 hx
  have : D x - v x = 0 := hx'
  exact sub_eq_zero.1 this

end

end CauchyRiemannIndex

-- ===== Scratch/CR46Approx.lean =====
/-!
# Weak solutions of `∂ₛη + J₀∂ₜη = g` are graph-norm limits of test sections

Compactly supported pairs: mollify (`CR46Weak`, `CR46Conv`). General pairs: cut off in `s`
with `χ(s / R)`, which keeps the weak equation with right-hand side `χ g + χ' η / R`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

noncomputable section

variable {n : ℕ}

/-- `(η, g)` is a limit of `(u, D₀ u)` over test sections `u`, in `L^p × L^p`. -/
def IsGraphLimit (p : ℝ≥0∞) (η g : ℝ × ℝ → Vec n) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
    eLpNorm (u - η) p cylMeasure ≤ ε ∧
    eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - g) p cylMeasure ≤ ε

lemma continuous_crOp_zero {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    Continuous (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u) := by
  rw [crOp_zero_eq]
  exact hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)

lemma graphLimit_of_compact {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {η g : ℝ × ℝ → Vec n}
    (hη : StronglyMeasurable η) (hηm : MemLp η p cylMeasure) (hg : StronglyMeasurable g)
    (hgm : MemLp g p cylMeasure) {R : ℝ} (hηR : ∀ s t, R < |s| → η (s, t) = 0)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hw : IsWeak0 η g) : IsGraphLimit p η g := by
  intro ε hε
  obtain ⟨N1, hN1⟩ := ENNReal.tendsto_atTop_zero.1 (moll_tendsto hp hη hηm) ε hε
  obtain ⟨N2, hN2⟩ := ENNReal.tendsto_atTop_zero.1 (moll_tendsto hp hg hgm) ε hε
  set k := max N1 N2
  refine ⟨moll (bumpSeq k) η, moll_isTestSection _ (bumpSeq_rOut_le k) hη hηm hηR,
    hN1 k (le_max_left _ _), ?_⟩
  have hae := crOp_zero_moll_ae (bumpSeq k) (bumpSeq_rOut_le k) hη hηm hg hgm hηR hgR hw
  rw [eLpNorm_congr_ae (hae.sub (EventuallyEq.refl _ g))]
  exact hN2 k (le_max_right _ _)

lemma graphLimit_of_approx {p : ℝ≥0∞} [Fact (1 ≤ p)] {η g : ℝ × ℝ → Vec n}
    (hη : AEStronglyMeasurable η cylMeasure) (hg : AEStronglyMeasurable g cylMeasure)
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ η' g' : ℝ × ℝ → Vec n, IsGraphLimit p η' g' ∧
      AEStronglyMeasurable η' cylMeasure ∧ AEStronglyMeasurable g' cylMeasure ∧
      eLpNorm (η' - η) p cylMeasure ≤ ε ∧ eLpNorm (g' - g) p cylMeasure ≤ ε) :
    IsGraphLimit p η g := by
  have hp1 : 1 ≤ p := Fact.out
  intro ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨η', g', hl, hη', hg', h1, h2⟩ := h (ε / 2) hε2
  obtain ⟨u, hu, hu1, hu2⟩ := hl (ε / 2) hε2
  refine ⟨u, hu, ?_, ?_⟩
  · calc eLpNorm (u - η) p cylMeasure = eLpNorm ((u - η') + (η' - η)) p cylMeasure := by
          rw [sub_add_sub_cancel]
      _ ≤ eLpNorm (u - η') p cylMeasure + eLpNorm (η' - η) p cylMeasure :=
          eLpNorm_add_le (hu.continuous.aestronglyMeasurable.sub hη') (hη'.sub hη) hp1
      _ ≤ ε / 2 + ε / 2 := add_le_add hu1 h1
      _ = ε := ENNReal.add_halves ε
  · have hD := (continuous_crOp_zero hu).aestronglyMeasurable (μ := cylMeasure)
    calc eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - g) p cylMeasure
        = eLpNorm ((crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - g') + (g' - g)) p cylMeasure := by
          rw [sub_add_sub_cancel]
      _ ≤ eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - g') p cylMeasure +
            eLpNorm (g' - g) p cylMeasure :=
          eLpNorm_add_le (hD.sub hg') (hg'.sub hg) hp1
      _ ≤ ε / 2 + ε / 2 := add_le_add hu2 h2
      _ = ε := ENNReal.add_halves ε

/-! ### Cut-off in `s` -/

/-- `⟨Φ, h⟩` is integrable for `Φ` continuous, periodic, compactly supported in `s`. -/
lemma integrable_inner_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)] {Φ : ℝ × ℝ → Vec n} (hΦ : Continuous Φ)
    (hper : ∀ s t, Φ (s, t + 1) = Φ (s, t)) {R : ℝ} (hR : ∀ s t, R < |s| → Φ (s, t) = 0)
    {h : ℝ × ℝ → Vec n} (hh : AEStronglyMeasurable h cylMeasure) (hm : MemLp h p cylMeasure) :
    Integrable (fun x => inner ℝ (Φ x) (h x)) cylMeasure := by
  have hp1 : 1 ≤ p := Fact.out
  obtain ⟨M, hM0, hM⟩ := exists_bound_per hΦ hper hR
  set K : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.univ with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hKf : cylMeasure K ≠ ⊤ := by
    rw [sca_cyl_eq_prod, hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  haveI : IsFiniteMeasure (cylMeasure.restrict K) := isFiniteMeasure_restrict.2 hKf
  have hhK : IntegrableOn h K cylMeasure := (hm.restrict K).integrable hp1
  have hb : Integrable (K.indicator fun x => M * ‖h x‖) cylMeasure :=
    (show IntegrableOn (fun x => M * ‖h x‖) K cylMeasure from hhK.norm.const_mul M).integrable_indicator hKm
  refine hb.mono' (hΦ.aestronglyMeasurable.inner hh) (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _))
  · rw [Set.indicator_of_notMem hx]
    have hs : R < |x.1| := by
      by_contra hc
      push_neg at hc
      exact hx ⟨abs_le.1 hc, Set.mem_univ _⟩
    have : Φ x = 0 := hR x.1 x.2 hs
    simp [this]

lemma partial_cutoff {c c' : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ∀ s, HasDerivAt c (c' s) s)
    {ψ : ℝ × ℝ → Vec n} (hψ : IsTestSection ψ) (x : ℝ × ℝ) :
    partialS (fun y : ℝ × ℝ => c y.1 • ψ y) x = c' x.1 • ψ x + c x.1 • partialS ψ x ∧
      partialT (fun y : ℝ × ℝ => c y.1 • ψ y) x = c x.1 • partialT ψ x := by
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => c y.1) (c' x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hd x.1).comp_hasFDerivAt x (hasFDerivAt_fst)
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    ((hψ.1.differentiable (by simp)) x).hasFDerivAt
  have h3 := h1.smul h2
  have h4 : fderiv ℝ (fun y : ℝ × ℝ => c y.1 • ψ y) x =
      c x.1 • fderiv ℝ ψ x + (c' x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ψ x) := h3.fderiv
  constructor
  · simp only [partialS]
    rw [h4]
    simp [add_comm]
  · simp only [partialT]
    rw [h4]
    simp

lemma isTestSection_cutoff {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) {ψ : ℝ × ℝ → Vec n}
    (hψ : IsTestSection ψ) : IsTestSection (fun y : ℝ × ℝ => c y.1 • ψ y) := by
  obtain ⟨R, hR⟩ := hψ.2.2
  refine ⟨(hc.comp contDiff_fst).smul hψ.1, fun s t => by simp only [hψ.2.1], R,
    fun s t hs => by simp only [hR s t hs, smul_zero]⟩

lemma weak_cutoff {c c' : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hd : ∀ s, HasDerivAt c (c' s) s)
    (hc' : Continuous c') {p : ℝ≥0∞} [Fact (1 ≤ p)] {η g : ℝ × ℝ → Vec n}
    (hη : StronglyMeasurable η) (hηm : MemLp η p cylMeasure) (hg : StronglyMeasurable g)
    (hgm : MemLp g p cylMeasure) (hw : IsWeak0 η g) :
    IsWeak0 (fun x => c x.1 • η x) (fun x => c x.1 • g x + c' x.1 • η x) := by
  intro ψ hψ
  obtain ⟨R, hR⟩ := hψ.2.2
  set ψc := fun y : ℝ × ℝ => c y.1 • ψ y with hψc
  have hψct : IsTestSection ψc := isTestSection_cutoff hc hψ
  have hadj : ∀ x, c x.1 • adj0 ψ x = adj0 ψc x + c' x.1 • ψ x := by
    intro x
    obtain ⟨e1, e2⟩ := partial_cutoff hc hd hψ x
    simp only [adj0, hψc] at e1 e2 ⊢
    rw [e1, e2, map_smul]
    module
  have hpt : ∀ x, inner ℝ (adj0 ψ x) (c x.1 • η x) =
      inner ℝ (adj0 ψc x) (η x) + inner ℝ (c' x.1 • ψ x) (η x) := by
    intro x
    rw [real_inner_smul_right, ← real_inner_smul_left, hadj, inner_add_left]
  have hcψ_cont : Continuous fun x : ℝ × ℝ => c' x.1 • ψ x :=
    (hc'.comp continuous_fst).smul hψ.continuous
  have hcψ_per : ∀ s t, (fun x : ℝ × ℝ => c' x.1 • ψ x) (s, t + 1) =
      (fun x : ℝ × ℝ => c' x.1 • ψ x) (s, t) := fun s t => by simp only [hψ.2.1]
  have hcψ_van : ∀ s t, R < |s| → (fun x : ℝ × ℝ => c' x.1 • ψ x) (s, t) = 0 :=
    fun s t hs => by simp only [hR s t hs, smul_zero]
  obtain ⟨Rc, hRc⟩ := hψct.2.2
  have i1 := integrable_inner_Lp (adj0_continuous hψct) (adj0_per hψct) (adj0_vanish hRc)
    hη.aestronglyMeasurable hηm
  have i2 := integrable_inner_Lp hcψ_cont hcψ_per hcψ_van hη.aestronglyMeasurable hηm
  have i3 := integrable_inner_Lp hψct.continuous hψct.2.1 hRc hg.aestronglyMeasurable hgm
  have hrhs : ∀ x, inner ℝ (ψ x) (c x.1 • g x + c' x.1 • η x) =
      inner ℝ (ψc x) (g x) + inner ℝ (c' x.1 • ψ x) (η x) := by
    intro x
    simp only [hψc, inner_add_right, real_inner_smul_right, real_inner_smul_left]
  simp_rw [hpt, hrhs]
  rw [integral_add i1 i2, integral_add i3 i2, hw ψc hψct]


/-- The cut-off bump: `1` on `[-1, 1]`, `0` outside `(-2, 2)`. -/
def chiB : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- `χ(s / R)`. -/
def cutR (R : ℝ) (s : ℝ) : ℝ := chiB (s / R)

/-- `χ'(s / R) / R`. -/
def cutR' (R : ℝ) (s : ℝ) : ℝ := deriv chiB (s / R) / R

lemma contDiff_cutR (R : ℝ) : ContDiff ℝ ∞ (cutR R) :=
  chiB.contDiff.comp (contDiff_id.div_const R)

lemma hasDerivAt_cutR (R s : ℝ) : HasDerivAt (cutR R) (cutR' R s) s := by
  have h1 : HasDerivAt chiB (deriv chiB (s / R)) (s / R) :=
    ((chiB.contDiff (n := 1)).differentiable one_ne_zero (s / R)).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => s / R) (1 / R) s := (hasDerivAt_id s).div_const R
  have h3 := h1.comp s h2
  have e : cutR' R s = deriv chiB (s / R) * (1 / R) := by rw [cutR']; ring
  rw [e]
  exact h3

lemma continuous_deriv_chiB : Continuous (deriv (chiB : ℝ → ℝ)) :=
  (chiB.contDiff (n := 1)).continuous_deriv le_rfl

lemma continuous_cutR' (R : ℝ) : Continuous (cutR' R) :=
  (continuous_deriv_chiB.comp (continuous_id.div_const R)).div_const R

lemma exists_bound_deriv_chiB : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |deriv (chiB : ℝ → ℝ) y| ≤ C := by
  obtain ⟨C, hC⟩ := continuous_deriv_chiB.bounded_above_of_compact_support
    chiB.hasCompactSupport.deriv
  exact ⟨C, (norm_nonneg _).trans (hC 0), fun y => by simpa [Real.norm_eq_abs] using hC y⟩

lemma cutR_nonneg (R s : ℝ) : 0 ≤ cutR R s := chiB.nonneg
lemma cutR_le_one (R s : ℝ) : cutR R s ≤ 1 := chiB.le_one

lemma cutR_eq_one {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ R) : cutR R s = 1 := by
  refine chiB.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hR,
    div_le_iff₀ hR]
  show |s| ≤ 1 * R
  linarith

lemma cutR'_eq_zero {R s : ℝ} (hR : 0 < R) (hs : |s| < R) : cutR' R s = 0 := by
  have hy : |s / R| < 1 := by
    rw [abs_div, abs_of_pos hR, div_lt_one hR]; exact hs
  have hev : (chiB : ℝ → ℝ) =ᶠ[𝓝 (s / R)] fun _ => 1 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show s / R ∈ Metric.ball (0 : ℝ) 1 by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; exact hy)] with z hz
    exact chiB.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)
  rw [cutR', hev.deriv_eq, deriv_const, zero_div]

lemma cutR_vanish {R s : ℝ} (hR : 0 < R) (hs : 2 * R < |s|) : cutR R s = 0 := by
  refine chiB.zero_of_le_dist ?_
  rw [dist_zero_right, Real.norm_eq_abs, abs_div, abs_of_pos hR, le_div_iff₀ hR]
  show 2 * R ≤ |s|
  exact hs.le

lemma cutR'_vanish {R s : ℝ} (hR : 0 < R) (hs : 2 * R < |s|) : cutR' R s = 0 := by
  have hev : (chiB : ℝ → ℝ) =ᶠ[𝓝 (s / R)] fun _ => 0 := by
    have hlt : 2 < |s / R| := by
      rw [abs_div, abs_of_pos hR, lt_div_iff₀ hR]; exact hs
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hlt] with z hz
    refine chiB.zero_of_le_dist ?_
    rw [dist_zero_right, Real.norm_eq_abs]
    exact le_of_lt hz
  rw [cutR', hev.deriv_eq, deriv_const, zero_div]

/-- The cut-off pair converges to `(η, g)`. -/
lemma cutoff_tendsto {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {η g : ℝ × ℝ → Vec n}
    (hη : StronglyMeasurable η) (hηm : MemLp η p cylMeasure) (hg : StronglyMeasurable g)
    (hgm : MemLp g p cylMeasure) :
    Tendsto (fun k : ℕ => eLpNorm ((fun x => cutR (k + 1) x.1 • η x) - η) p cylMeasure) atTop
        (𝓝 0) ∧
      Tendsto (fun k : ℕ => eLpNorm ((fun x => cutR (k + 1) x.1 • g x + cutR' (k + 1) x.1 • η x)
        - g) p cylMeasure) atTop (𝓝 0) := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp1).ne'
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_chiB
  have hkpos : ∀ k : ℕ, (0 : ℝ) < k + 1 := fun k => by positivity
  have hcm : ∀ k : ℕ, StronglyMeasurable fun x : ℝ × ℝ => cutR (k + 1) x.1 :=
    fun k => ((contDiff_cutR _).continuous.comp continuous_fst).stronglyMeasurable
  have hcm' : ∀ k : ℕ, StronglyMeasurable fun x : ℝ × ℝ => cutR' (k + 1) x.1 :=
    fun k => ((continuous_cutR' _).comp continuous_fst).stronglyMeasurable
  have hev : ∀ x : ℝ × ℝ, ∀ᶠ k : ℕ in atTop, cutR (k + 1) x.1 = 1 ∧ cutR' (k + 1) x.1 = 0 := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge |x.1|
    filter_upwards [eventually_ge_atTop N] with k hk
    have hk' : |x.1| < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    exact ⟨cutR_eq_one (hkpos k) hk'.le, cutR'_eq_zero (hkpos k) hk'⟩
  constructor
  · refine tendsto_eLpNorm_zero_of_dominated hp0 hp hηm.norm
      (fun k => (((hcm k).smul hη).sub hη).aestronglyMeasurable)
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · show ‖cutR (k + 1) x.1 • η x - η x‖ ≤ ‖η x‖
      rw [show cutR (k + 1) x.1 • η x - η x = (cutR (k + 1) x.1 - 1) • η x by
        rw [sub_smul, one_smul], norm_smul, Real.norm_eq_abs]
      have h1 := cutR_nonneg (k + 1) x.1
      have h2 := cutR_le_one (k + 1) x.1
      have : |cutR (k + 1) x.1 - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |cutR (k + 1) x.1 - 1| * ‖η x‖ ≤ 1 * ‖η x‖ :=
            mul_le_mul_of_nonneg_right this (norm_nonneg _)
        _ = ‖η x‖ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with k hk
      show (0 : Vec n) = cutR (k + 1) x.1 • η x - η x
      rw [hk.1, one_smul, sub_self]
  · refine tendsto_eLpNorm_zero_of_dominated hp0 hp (hgm.norm.add (hηm.norm.const_mul C))
      (fun k => ((((hcm k).smul hg).add ((hcm' k).smul hη)).sub hg).aestronglyMeasurable)
      (fun k => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · show ‖cutR (k + 1) x.1 • g x + cutR' (k + 1) x.1 • η x - g x‖ ≤ ‖g x‖ + C * ‖η x‖
      have h1 := cutR_nonneg (k + 1) x.1
      have h2 := cutR_le_one (k + 1) x.1
      have ha : |cutR (k + 1) x.1 - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have hb : |cutR' (k + 1) x.1| ≤ C := by
        rw [cutR', abs_div, abs_of_pos (hkpos k)]
        rw [div_le_iff₀ (hkpos k)]
        have := hC ((x.1) / ((k : ℝ) + 1))
        have hk1 : (1 : ℝ) ≤ k + 1 := by
          have : (0 : ℝ) ≤ k := k.cast_nonneg
          linarith
        nlinarith
      have e : cutR (k + 1) x.1 • g x + cutR' (k + 1) x.1 • η x - g x =
          (cutR (k + 1) x.1 - 1) • g x + cutR' (k + 1) x.1 • η x := by
        rw [sub_smul, one_smul]; abel
      rw [e]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        calc |cutR (k + 1) x.1 - 1| * ‖g x‖ ≤ 1 * ‖g x‖ :=
              mul_le_mul_of_nonneg_right ha (norm_nonneg _)
          _ = ‖g x‖ := one_mul _
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with k hk
      show (0 : Vec n) = cutR (k + 1) x.1 • g x + cutR' (k + 1) x.1 • η x - g x
      rw [hk.1, hk.2, one_smul, zero_smul, add_zero, sub_self]

/-- Weak solutions of `∂ₛη + J₀∂ₜη = g` with `η, g ∈ L^p` are graph-norm limits of test
sections. -/
theorem graphLimit_of_weak {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) {η g : ℝ × ℝ → Vec n}
    (hη : StronglyMeasurable η) (hηm : MemLp η p cylMeasure) (hg : StronglyMeasurable g)
    (hgm : MemLp g p cylMeasure) (hw : IsWeak0 η g) : IsGraphLimit p η g := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_deriv_chiB
  obtain ⟨t1, t2⟩ := cutoff_tendsto hp hη hηm hg hgm
  refine graphLimit_of_approx hη.aestronglyMeasurable hg.aestronglyMeasurable fun ε hε => ?_
  obtain ⟨N1, hN1⟩ := ENNReal.tendsto_atTop_zero.1 t1 ε hε
  obtain ⟨N2, hN2⟩ := ENNReal.tendsto_atTop_zero.1 t2 ε hε
  set k := max N1 N2
  have hR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcs : StronglyMeasurable fun x : ℝ × ℝ => cutR ((k : ℝ) + 1) x.1 :=
    ((contDiff_cutR _).continuous.comp continuous_fst).stronglyMeasurable
  have hcs' : StronglyMeasurable fun x : ℝ × ℝ => cutR' ((k : ℝ) + 1) x.1 :=
    ((continuous_cutR' _).comp continuous_fst).stronglyMeasurable
  have hη's : StronglyMeasurable fun x : ℝ × ℝ => cutR ((k : ℝ) + 1) x.1 • η x := hcs.smul hη
  have hg's : StronglyMeasurable fun x : ℝ × ℝ =>
      cutR ((k : ℝ) + 1) x.1 • g x + cutR' ((k : ℝ) + 1) x.1 • η x :=
    (hcs.smul hg).add (hcs'.smul hη)
  have hη'm : MemLp (fun x : ℝ × ℝ => cutR ((k : ℝ) + 1) x.1 • η x) p cylMeasure := by
    refine hηm.of_le hη's.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    show ‖cutR ((k : ℝ) + 1) x.1 • η x‖ ≤ ‖η x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg _ x.1)]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutR_le_one _ x.1)
  have hg'm : MemLp (fun x : ℝ × ℝ =>
      cutR ((k : ℝ) + 1) x.1 • g x + cutR' ((k : ℝ) + 1) x.1 • η x) p cylMeasure := by
    refine MemLp.add (f := fun x : ℝ × ℝ => cutR ((k : ℝ) + 1) x.1 • g x)
      (g := fun x : ℝ × ℝ => cutR' ((k : ℝ) + 1) x.1 • η x) ?_ ?_
    · refine hgm.of_le (hcs.smul hg).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      show ‖cutR ((k : ℝ) + 1) x.1 • g x‖ ≤ ‖g x‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cutR_nonneg _ x.1)]
      exact mul_le_of_le_one_left (norm_nonneg _) (cutR_le_one _ x.1)
    · refine (hηm.const_smul C).of_le (hcs'.smul hη).aestronglyMeasurable (ae_of_all _ fun x => ?_)
      show ‖cutR' ((k : ℝ) + 1) x.1 • η x‖ ≤ ‖(C • η) x‖
      rw [Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hC0]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [cutR', abs_div, abs_of_pos hR, div_le_iff₀ hR]
      have := hC (x.1 / ((k : ℝ) + 1))
      have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        linarith
      nlinarith
  have hvη : ∀ s t, 2 * ((k : ℝ) + 1) < |s| →
      (fun x : ℝ × ℝ => cutR ((k : ℝ) + 1) x.1 • η x) (s, t) = 0 := fun s t hs => by
    simp only [cutR_vanish hR hs, zero_smul]
  have hvg : ∀ s t, 2 * ((k : ℝ) + 1) < |s| → (fun x : ℝ × ℝ =>
      cutR ((k : ℝ) + 1) x.1 • g x + cutR' ((k : ℝ) + 1) x.1 • η x) (s, t) = 0 :=
    fun s t hs => by simp only [cutR_vanish hR hs, cutR'_vanish hR hs, zero_smul, add_zero]
  have hw' := weak_cutoff (contDiff_cutR ((k : ℝ) + 1)) (hasDerivAt_cutR ((k : ℝ) + 1))
    (continuous_cutR' ((k : ℝ) + 1)) hη hηm hg hgm hw
  exact ⟨_, _, graphLimit_of_compact hp hη's hη'm hg's hg'm hvη hvg hw',
    hη's.aestronglyMeasurable, hg's.aestronglyMeasurable, hN1 k (le_max_left _ _),
    hN2 k (le_max_right _ _)⟩

/-- `L^p` version, with the weak equation written out. -/
theorem weak_solution_graph_approx_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x)) (η x)
          ∂cylMeasure = ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (u - ⇑η) p cylMeasure ≤ ε ∧
      eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - ⇑f) p cylMeasure ≤ ε :=
  graphLimit_of_weak hp' (Lp.stronglyMeasurable η) (Lp.memLp η) (Lp.stronglyMeasurable f)
    (Lp.memLp f) hweak

end

end CauchyRiemannIndex

-- ===== Scratch/CR46ApproxSol.lean =====
open MeasureTheory CauchyRiemannIndex
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp' : p ≠ ⊤)
    (η f : LpCyl n p)
    (hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x)) (η x)
          ∂cylMeasure = ∫ x, inner ℝ (φ x) (f x) ∂cylMeasure) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ u : ℝ × ℝ → Vec n, IsTestSection u ∧
      eLpNorm (u - ⇑η) p cylMeasure ≤ ε ∧
      eLpNorm (crOp (fun _ : ℝ × ℝ => (0 : Mat n)) u - ⇑f) p cylMeasure ≤ ε :=
  weak_solution_graph_approx_aux n p hp' η f hweak
