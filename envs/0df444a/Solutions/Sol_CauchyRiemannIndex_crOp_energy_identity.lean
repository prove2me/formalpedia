-- Prove2me | solution 1 for CauchyRiemannIndex.crOp_energy_identity
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T22:02:09.644121+00:00
-- url     : https://prove2.me/submissions/9d93a014-a179-4dd0-a88a-c04cd5e8b206

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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

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

-- ===== Scratch/CREnergy.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- `∫ g = 0` over the cylinder when `g = ∂ₛF` slice-wise, with `g` continuous and both `g` and
`F` vanishing for large `|s|`. -/
lemma integral_s_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
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

lemma fderiv_partialT_apply {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 2 u) (x : ℝ × ℝ) (h : ℝ × ℝ) :
    fderiv ℝ (partialT u) x h = fderiv ℝ (fderiv ℝ u) x h (0, 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have : partialT u = fun y => (fderiv ℝ u y) ((0 : ℝ), (1 : ℝ)) := rfl
  rw [this, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma fderiv_partialS_apply {u : ℝ × ℝ → Vec n} (hu : ContDiff ℝ 2 u) (x : ℝ × ℝ) (h : ℝ × ℝ) :
    fderiv ℝ (partialS u) x h = fderiv ℝ (fderiv ℝ u) x h (1, 0) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have : partialS u = fun y => (fderiv ℝ u y) ((1 : ℝ), (0 : ℝ)) := rfl
  rw [this, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma inner_J_swap (a b : Vec n) :
    ⟪a, Matrix.toEuclideanLin (J₀ n) b⟫ = -⟪b, Matrix.toEuclideanLin (J₀ n) a⟫ := by
  rw [real_inner_comm, inner_toEuclideanLin, Matrix.J_transpose, map_neg, LinearMap.neg_apply,
    inner_neg_right]

theorem crOp_energy_identity_aux (Sinf : ℝ → Mat n) (hc : Continuous Sinf)
    (hsymm : ∀ t, (Sinf t).IsSymm) (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    ∫ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure +
        ∫ x, ‖Matrix.toEuclideanLin (J₀ n) (partialT u x) +
          Matrix.toEuclideanLin (Sinf x.2) (u x)‖ ^ 2 ∂cylMeasure := by
  obtain ⟨R, hR⟩ := hu.2.2
  have hu2 : ContDiff ℝ 2 u := hu.1.of_le (by norm_cast)
  have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
  set J := Matrix.toEuclideanLin (J₀ n) with hJ
  have hdT : ContDiff ℝ 1 (partialT u) :=
    (hu.1.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
  have hdS : ContDiff ℝ 1 (partialS u) :=
    (hu.1.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
  have hJT : ContDiff ℝ 1 fun x => J (partialT u x) := (matCLM n (J₀ n)).contDiff.comp hdT
  have hJS : ContDiff ℝ 1 fun x => J (partialS u x) := (matCLM n (J₀ n)).contDiff.comp hdS
  set φ₁ : ℝ × ℝ → ℝ := fun x => ⟪u x, J (partialT u x)⟫ with hφ₁
  set φ₂ : ℝ × ℝ → ℝ := fun x => ⟪u x, J (partialS u x)⟫ with hφ₂
  have hφ₁c : ContDiff ℝ 1 φ₁ := (hu.1.of_le (by simp)).inner ℝ hJT
  have hφ₂c : ContDiff ℝ 1 φ₂ := (hu.1.of_le (by simp)).inner ℝ hJS
  set Sx : ℝ × ℝ → Vec n := fun x => Matrix.toEuclideanLin (Sinf x.2) (u x) with hSx
  set g : ℝ × ℝ → ℝ := fun x => 2 * ⟪partialS u x, Sx x⟫ with hg
  set F : ℝ × ℝ → ℝ := fun x => ⟪u x, Sx x⟫ with hF
  -- the two cross terms
  have hcross : ∀ x, fderiv ℝ φ₁ x (1, 0) - fderiv ℝ φ₂ x (0, 1) =
      2 * ⟪partialS u x, J (partialT u x)⟫ := by
    intro x
    rw [hφ₁, hφ₂, fderiv_inner_apply ℝ (hud x) (hJT.differentiable one_ne_zero x),
      fderiv_inner_apply ℝ (hud x) (hJS.differentiable one_ne_zero x),
      fderiv_matCLM_comp (J₀ n) (hdT.differentiable one_ne_zero x),
      fderiv_matCLM_comp (J₀ n) (hdS.differentiable one_ne_zero x),
      fderiv_partialT_apply hu2, fderiv_partialS_apply hu2,
      (hu2.contDiffAt.isSymmSndFDerivAt (by simp)) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))]
    have h1 : fderiv ℝ u x ((1 : ℝ), (0 : ℝ)) = partialS u x := rfl
    have h2 : fderiv ℝ u x ((0 : ℝ), (1 : ℝ)) = partialT u x := rfl
    rw [h1, h2, inner_J_swap (partialT u x)]
    ring
  have hsl : ∀ s t, HasDerivAt (fun r => u (r, t)) (partialS u (s, t)) s := fun s t =>
    (hud (s, t)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
  have hFd : ∀ s t, HasDerivAt (fun s => F (s, t)) (g (s, t)) s := by
    intro s t
    have hγ := hsl s t
    have hM : HasDerivAt (fun r => Matrix.toEuclideanLin (Sinf t) (u (r, t)))
        (Matrix.toEuclideanLin (Sinf t) (partialS u (s, t))) s :=
      (matCLM n (Sinf t)).hasFDerivAt.comp_hasDerivAt s hγ
    have := hγ.inner ℝ hM
    refine this.congr_deriv ?_
    show _ = 2 * ⟪partialS u (s, t), Matrix.toEuclideanLin (Sinf t) (u (s, t))⟫
    have e : ⟪u (s, t), Matrix.toEuclideanLin (Sinf t) (partialS u (s, t))⟫ =
        ⟪partialS u (s, t), Matrix.toEuclideanLin (Sinf t) (u (s, t))⟫ := by
      conv_lhs => rw [← (hsymm t).eq]
      rw [← inner_toEuclideanLin, real_inner_comm]
    rw [e]
    ring
  have hRS : ∀ s t, R < |s| → partialS u (s, t) = 0 := fun s t hs => partialS_eq_zero R hR hs
  have hRT : ∀ s t, R < |s| → partialT u (s, t) = 0 := fun s t hs => partialT_eq_zero R hR hs
  have hSc : Continuous Sx := (continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous
  have hint : ∀ {f : ℝ × ℝ → ℝ}, Continuous f → (∀ s t, R < |s| → f (s, t) = 0) →
      Integrable f cylMeasure := by
    intro f hf hfz
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish f hf R hfz
  have hgc : Continuous g := continuous_const.mul (hu.continuous_partialS.inner hSc)
  have hgz : ∀ s t, R < |s| → g (s, t) = 0 := fun s t hs => by simp [hg, hRS s t hs]
  have hFz : ∀ s t, R < |s| → F (s, t) = 0 := fun s t hs => by simp [hF, hR s t hs]
  have hφ₁z : ∀ s t, R < |s| → φ₁ (s, t) = 0 := fun s t hs => by simp [hφ₁, hR s t hs]
  have hφ₂z : ∀ s t, R < |s| → φ₂ (s, t) = 0 := fun s t hs => by simp [hφ₂, hR s t hs]
  have hφ₂p : ∀ s t, φ₂ (s, t + 1) = φ₂ (s, t) := fun s t => by
    have h1 : partialS u (s, t + 1) = partialS u (s, t) := by
      have : (fun r => u (r, t + 1)) = fun r => u (r, t) := funext fun r => hu.2.1 r t
      rw [← (hsl s (t + 1)).deriv, ← (hsl s t).deriv, this]
    simp [hφ₂, hu.2.1, h1]
  have hd1 : Integrable (fun x => fderiv ℝ φ₁ x (1, 0)) cylMeasure :=
    hint ((hφ₁c.continuous_fderiv (by simp)).clm_apply continuous_const) fun s t hs => by
      simp [fderiv_eq_zero_of_vanish _ hφ₁z hs]
  have hd2 : Integrable (fun x => fderiv ℝ φ₂ x (0, 1)) cylMeasure :=
    hint ((hφ₂c.continuous_fderiv (by simp)).clm_apply continuous_const) fun s t hs => by
      simp [fderiv_eq_zero_of_vanish _ hφ₂z hs]
  have hA : Continuous fun x => J (partialT u x) + Sx x :=
    ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT).add hSc
  have hI1 : Integrable (fun x => ‖partialS u x‖ ^ 2) cylMeasure :=
    hint (hu.continuous_partialS.norm.pow 2) fun s t hs => by simp [hRS s t hs]
  have hI2 : Integrable (fun x => ‖J (partialT u x) + Sx x‖ ^ 2) cylMeasure :=
    hint (hA.norm.pow 2) fun s t hs => by simp [hRT s t hs, hSx, hR s t hs]
  have hpt : ∀ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ ^ 2 =
      ‖partialS u x‖ ^ 2 + ‖J (partialT u x) + Sx x‖ ^ 2 +
        ((fderiv ℝ φ₁ x (1, 0) - fderiv ℝ φ₂ x (0, 1)) + g x) := by
    intro x
    rw [hcross]
    simp only [crOp, hg, hSx]
    rw [add_assoc, norm_add_sq_real, inner_add_right]
    ring
  simp_rw [hpt]
  have hcr : Integrable (fun x => fderiv ℝ φ₁ x (1, 0) - fderiv ℝ φ₂ x (0, 1)) cylMeasure :=
    hd1.sub hd2
  have hI12 : Integrable (fun x => ‖partialS u x‖ ^ 2 + ‖J (partialT u x) + Sx x‖ ^ 2)
      cylMeasure := hI1.add hI2
  have hcrg : Integrable (fun x => (fderiv ℝ φ₁ x (1, 0) - fderiv ℝ φ₂ x (0, 1)) + g x)
      cylMeasure := hcr.add (hint hgc hgz)
  rw [integral_add hI12 hcrg, integral_add hI1 hI2,
    integral_add hcr (hint hgc hgz), integral_sub hd1 hd2,
    integral_fderiv_s_eq_zero φ₁ hφ₁c R hφ₁z, integral_fderiv_t_eq_zero φ₂ hφ₂c hφ₂p R hφ₂z,
    integral_s_eq_zero_of_hasDerivAt g F hgc R hgz hFz hFd]
  simp [hSx]

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hc : Continuous Sinf)
    (hsymm : ∀ t, (Sinf t).IsSymm) (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    ∫ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure +
        ∫ x, ‖Matrix.toEuclideanLin (J₀ n) (partialT u x) +
          Matrix.toEuclideanLin (Sinf x.2) (u x)‖ ^ 2 ∂cylMeasure :=
  crOp_energy_identity_aux Sinf hc hsymm u hu
