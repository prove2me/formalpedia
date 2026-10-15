-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_slab_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T22:24:55.91579+00:00
-- url     : https://prove2.me/submissions/261c26f8-94f2-47e9-b9db-01d80f51217c

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
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_L2_bound

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

-- ===== Scratch/CRBox1.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### One-dimensional pieces -/

/-- A `C¹` curve: `|g x - g y| ≤ ∫_{[a,b]} |g'|` for `x, y ∈ [a, b]`. -/
lemma crbox_seg {g g' : ℝ → Vec n} (hg : ∀ r, HasDerivAt g (g' r) r) (hc : Continuous g')
    {a b x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g x - g y‖ₑ ≤ ∫⁻ r in Icc a b, ‖g' r‖ₑ := by
  have key : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x ≤ y →
      ‖g y - g x‖ₑ ≤ ∫⁻ r in Icc a b, ‖g' r‖ₑ := by
    intro x y hx hy hxy
    have hint : IntervalIntegrable g' volume x y := hc.intervalIntegrable x y
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hg r) hint
    rw [← hftc, intervalIntegral.integral_of_le hxy]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono_set ?_)
    intro r hr
    exact ⟨hx.1.trans hr.1.le, hr.2.trans hy.2⟩
  rcases le_total x y with h | h
  · rw [← enorm_neg, neg_sub]; exact key x y hx hy h
  · exact key y x hy hx h

/-- Jensen/Hölder on a finite measure: `(∫ f)^p ≤ μ(univ)^{p-1} ∫ f^p` for `p > 1`. -/
lemma crbox_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ} (hp : 1 < p)
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ a, f a ∂μ) ^ p ≤ μ univ ^ (p - 1) * ∫⁻ a, f a ^ p ∂μ := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := p.conjExponent with hq
  have hq0 : 0 < q := hpq.symm.pos
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hp0 : 0 < p := by linarith
  calc (∫⁻ a, f a ∂μ) ^ p
      ≤ ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * μ univ ^ (1 / q)) ^ p :=
        ENNReal.rpow_le_rpow h hp0.le
    _ = (∫⁻ a, f a ^ p ∂μ) * μ univ ^ (p - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        · rw [one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        · congr 1
          have := hpq.inv_add_inv_eq_one
          field_simp
          field_simp at this
          linarith
    _ = μ univ ^ (p - 1) * ∫⁻ a, f a ^ p ∂μ := mul_comm _ _

/-- Superadditivity of `x ↦ x^q`, `q ≥ 1`, over a finite sum. -/
lemma crbox_sum_rpow_le {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) {q : ℝ} (hq : 1 ≤ q) :
    ∑ i ∈ s, f i ^ q ≤ (∑ i ∈ s, f i) ^ q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < q)]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (ENNReal.add_rpow_le_rpow_add _ _ hq)

/-- Splitting `[0, k/N)` into the `k` grid intervals of length `1/N`. -/
lemma crbox_partition (f : ℝ → ℝ≥0∞) (h : ℝ) (hh : 0 ≤ h) (k : ℕ) :
    ∫⁻ t in Ico 0 (k * h), f t =
      ∑ j ∈ Finset.range k, ∫⁻ t in Ico (j * h) ((j + 1) * h), f t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    push_cast
    rw [← lintegral_union measurableSet_Ico (Ico_disjoint_Ico_same),
      Ico_union_Ico_eq_Ico (by positivity) (by nlinarith)]

/-- `∫⁻ r in [s, s+h], ψ r = ∫⁻ ρ in [0, h], ψ (ρ + s)`. -/
lemma crbox_shift (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) (s h : ℝ) :
    ∫⁻ r in Icc s (s + h), ψ r = ∫⁻ ρ in Icc 0 h, ψ (ρ + s) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) s
  rw [← hmp.setLIntegral_comp_preimage measurableSet_Icc hψ]
  congr 2
  ext ρ; simp only [mem_preimage, mem_Icc]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- `∫_s ∫_{[s, s+h]} ψ = h ∫ ψ`. -/
lemma crbox_shift_int (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ s, ∫⁻ r in Icc s (s + h), ψ r = ENNReal.ofReal h * ∫⁻ r, ψ r := by
  rw [show (fun s => ∫⁻ r in Icc s (s + h), ψ r) = fun s => ∫⁻ ρ in Icc 0 h, ψ (ρ + s) from
    funext fun s => crbox_shift ψ hψ s h]
  rw [lintegral_lintegral_swap]
  · simp_rw [lintegral_add_left_eq_self (μ := (volume : Measure ℝ)) ψ]
    rw [setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]
  · exact (hψ.comp (measurable_snd.add measurable_fst)).aemeasurable

end

end CauchyRiemannIndex

-- ===== Scratch/CRSlabW.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### The weight `ρ_ε(y) = (1 + (ε y)²)⁻¹` -/

/-- The weight `(1 + (ε y)²)⁻¹`. -/
def crw (ε y : ℝ) : ℝ := (1 + (ε * y) ^ 2)⁻¹

/-- Its derivative. -/
def crwd (ε y : ℝ) : ℝ := -(2 * (ε * y) * ε) / (1 + (ε * y) ^ 2) ^ 2

lemma crw_den_pos (ε y : ℝ) : 0 < 1 + (ε * y) ^ 2 := by positivity

lemma crw_pos (ε y : ℝ) : 0 < crw ε y := inv_pos.2 (crw_den_pos ε y)

lemma crw_le_one (ε y : ℝ) : crw ε y ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (ε * y)])

lemma crw_hasDerivAt (ε y : ℝ) : HasDerivAt (crw ε) (crwd ε y) y := by
  have h1 : HasDerivAt (fun y => 1 + (ε * y) ^ 2) (2 * (ε * y) * ε) y := by
    have := ((hasDerivAt_id y).const_mul ε).pow 2
    simpa [mul_comm, mul_left_comm, mul_assoc] using this.const_add 1
  exact h1.inv (crw_den_pos ε y).ne'

lemma crw_contDiff (ε : ℝ) : ContDiff ℝ ∞ (crw ε) := by
  unfold crw
  exact (contDiff_const.add ((contDiff_const.mul contDiff_id).pow 2)).inv
    fun y => (crw_den_pos ε y).ne'

lemma crw_continuous (ε : ℝ) : Continuous (crw ε) := (crw_contDiff ε).continuous

lemma crwd_abs_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) : |crwd ε y| ≤ ε * crw ε y := by
  have hD := crw_den_pos ε y
  rw [crwd, crw, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (1 + (ε * y) ^ 2) ^ 2),
    ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) hD]
  have h2 : |2 * (ε * y) * ε| = 2 * ε ^ 2 * |y| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hε]; norm_num; ring
  rw [h2]
  have hy : (ε * y) ^ 2 = ε ^ 2 * |y| ^ 2 := by rw [mul_pow, sq_abs]
  rw [hy]
  have key := mul_nonneg (mul_nonneg hε.le (by positivity : (0 : ℝ) ≤ 1 + ε ^ 2 * |y| ^ 2))
    (sq_nonneg (ε * |y| - 1))
  nlinarith [key]

lemma crw_lower (ε : ℝ) {y : ℝ} (hy : |y| ≤ 1) : 1 ≤ (1 + ε ^ 2) * crw ε y := by
  rw [crw, ← div_eq_mul_inv, le_div_iff₀ (crw_den_pos ε y), one_mul, mul_pow]
  have : y ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg y]
  nlinarith [sq_nonneg ε]

lemma crw_even (ε y : ℝ) : crw ε (-y) = crw ε y := by simp [crw]

lemma crw_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (crw ε) := by
  have := integrable_inv_one_add_sq.comp_mul_left' hε.ne'
  exact this

/-- `W = ∫ ρ_ε² < ∞`. -/
lemma crw_lintegral_lt_top {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ y, ‖crw ε y‖ₑ ^ (2 : ℝ) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (crw_integrable hε).2
  refine ENNReal.rpow_le_self_of_le_one ?_ (by norm_num)
  rw [Real.enorm_of_nonneg (crw_pos ε y).le]
  exact ENNReal.ofReal_le_one.2 (crw_le_one ε y)

/-- Translation invariance of `W`. -/
lemma crw_lintegral_shift (ε s : ℝ) :
    ∫⁻ a, ‖crw ε (s - a)‖ₑ ^ (2 : ℝ) = ∫⁻ y, ‖crw ε y‖ₑ ^ (2 : ℝ) := by
  have : (fun a => ‖crw ε (s - a)‖ₑ ^ (2 : ℝ)) = fun a => ‖crw ε (a - s)‖ₑ ^ (2 : ℝ) := by
    funext a; rw [← crw_even, neg_sub]
  rw [this, lintegral_sub_right_eq_self (fun y => ‖crw ε y‖ₑ ^ (2 : ℝ)) s]

/-! ### Weighted test sections -/

lemma crw_hasFDerivAt (ε a : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => crw ε (x.1 - a))
      (crwd ε (x.1 - a) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  have := (crw_hasDerivAt ε (x.1 - a)).comp_hasFDerivAt x ((hasFDerivAt_sub_const_iff a).2 (hasFDerivAt_fst (𝕜 := ℝ) (p := x)))
  exact this

lemma crw_weighted_fderiv (ε a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => crw ε (x.1 - a) • u x)
      (crw ε (x.1 - a) • fderiv ℝ u x +
        (crwd ε (x.1 - a) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (u x)) x :=
  (crw_hasFDerivAt ε a x).smul ((hu.1.differentiable (by simp)) x).hasFDerivAt

lemma crw_isTestSection (ε a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    IsTestSection (fun x : ℝ × ℝ => crw ε (x.1 - a) • u x) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨((crw_contDiff ε).comp (contDiff_fst.sub contDiff_const)).smul hu.1, ?_, R, ?_⟩
  · intro s t; simp [hu.2.1]
  · intro s t hs; simp [hR s t hs]

lemma crw_partialS (ε a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (x : ℝ × ℝ) :
    partialS (fun x : ℝ × ℝ => crw ε (x.1 - a) • u x) x =
      crw ε (x.1 - a) • partialS u x + crwd ε (x.1 - a) • u x := by
  rw [partialS, (crw_weighted_fderiv ε a hu x).fderiv]
  simp [partialS]

lemma crw_partialT (ε a : ℝ) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) (x : ℝ × ℝ) :
    partialT (fun x : ℝ × ℝ => crw ε (x.1 - a) • u x) x = crw ε (x.1 - a) • partialT u x := by
  rw [partialT, (crw_weighted_fderiv ε a hu x).fderiv]
  simp [partialT]

lemma crw_crOp (ε a : ℝ) (S : ℝ × ℝ → Mat n) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u)
    (x : ℝ × ℝ) :
    crOp S (fun x : ℝ × ℝ => crw ε (x.1 - a) • u x) x =
      crw ε (x.1 - a) • crOp S u x + crwd ε (x.1 - a) • u x := by
  simp only [crOp, crw_partialS ε a hu, crw_partialT ε a hu, map_smul, smul_add]
  abel

/-! ### Weighted Jensen -/

lemma crw_jensen {α : Type*} [MeasurableSpace α] (μ : Measure α) {w F : α → ℝ≥0∞}
    (hw : Measurable w) (hF : Measurable F) {q : ℝ} (hq : 1 ≤ q) :
    (∫⁻ x, w x * F x ∂μ) ^ q ≤ (∫⁻ x, w x ∂μ) ^ (q - 1) * ∫⁻ x, w x * F x ^ q ∂μ := by
  rcases hq.eq_or_lt with h | h
  · subst h; simp
  have hj := crbox_jensen (μ.withDensity w) h hF.aemeasurable
  rw [lintegral_withDensity_eq_lintegral_mul μ hw hF,
    lintegral_withDensity_eq_lintegral_mul μ hw (hF.pow_const q),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hj
  exact hj

end

end CauchyRiemannIndex

-- ===== Scratch/CRSlabParent.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma crs_eLpNorm_sq (g : ℝ × ℝ → Vec n) :
    eLpNorm g 2 cylMeasure ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [ENNReal.rpow_inv_rpow (by norm_num)]

lemma crs_continuous_crOp (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crOp (fun x : ℝ × ℝ => Sinf x.2) u) :=
  (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
    ((continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous)

lemma crwd_continuous (ε : ℝ) : Continuous (crwd ε) := by
  rw [show crwd ε = deriv (crw ε) from funext fun y => (crw_hasDerivAt ε y).deriv.symm]
  exact (crw_contDiff ε).continuous_deriv (by simp)

/-- The weighted `L²` bound `‖ρ_a u‖₂² ≤ K₀ ‖ρ_a D u‖₂²`, uniformly in the centre `a`. -/
lemma crs_weighted (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K₀ : ℝ≥0∞, K₀ ≠ ⊤ ∧ ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ a : ℝ,
      ∫⁻ x, ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) ∂cylMeasure ≤
        K₀ * ∫⁻ x, ‖crw ε (x.1 - a) • crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ₑ ^ (2 : ℝ)
          ∂cylMeasure := by
  obtain ⟨C, hC⟩ := translationInvariant_L2_bound n Sinf hS hnd
  set ε : ℝ := 1 / (2 * ((C : ℝ) + 1)) with hεdef
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  have hε : 0 < ε := by positivity
  have hCε : (C : ℝ) * ε ≤ 1 / 2 := by
    rw [hεdef, mul_one_div, div_le_iff₀ (by positivity)]
    nlinarith
  refine ⟨ε, hε, ENNReal.ofReal (2 * C) ^ (2 : ℝ),
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top, fun u hu a => ?_⟩
  obtain ⟨R, hR⟩ := hu.2.2
  set v : ℝ × ℝ → Vec n := fun x => crw ε (x.1 - a) • u x with hv
  have hvt : IsTestSection v := crw_isTestSection ε a hu
  set D := crOp (fun x : ℝ × ℝ => Sinf x.2) u with hD
  set f₁ : ℝ × ℝ → Vec n := fun x => crw ε (x.1 - a) • D x with hf₁
  set f₂ : ℝ × ℝ → Vec n := fun x => crwd ε (x.1 - a) • u x with hf₂
  have hDv : crOp (fun x : ℝ × ℝ => Sinf x.2) v = f₁ + f₂ :=
    funext fun x => crw_crOp ε a _ hu x
  have hcρ : Continuous fun x : ℝ × ℝ => x.1 - a := continuous_fst.sub continuous_const
  have hc1 : Continuous f₁ :=
    ((crw_continuous ε).comp hcρ).smul (crs_continuous_crOp Sinf hS.1 hu)
  have hc2 : Continuous f₂ := ((crwd_continuous ε).comp hcρ).smul hu.continuous
  set X := eLpNorm v 2 cylMeasure with hXdef
  set Y := eLpNorm f₁ 2 cylMeasure with hYdef
  have hX : X ≠ ⊤ := (hvt.memLp (p := 2)).eLpNorm_lt_top.ne
  have hY : Y ≠ ⊤ := by
    refine (memLp_of_vanish (p := 2) f₁ hc1 R fun s t hs => ?_).eLpNorm_lt_top.ne
    simp [hf₁, hD, crOp, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, hR s t hs]
  have h1 : X ≤ C * eLpNorm (f₁ + f₂) 2 cylMeasure := hDv ▸ hC v hvt
  have h2 : eLpNorm (f₁ + f₂) 2 cylMeasure ≤ Y + eLpNorm f₂ 2 cylMeasure :=
    eLpNorm_add_le hc1.aestronglyMeasurable hc2.aestronglyMeasurable (by norm_num)
  have h3 : eLpNorm f₂ 2 cylMeasure ≤ ‖ε‖ₑ * X := by
    rw [hXdef, ← eLpNorm_const_smul]
    refine eLpNorm_mono fun x => ?_
    simp only [hf₂, hv, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos hε, abs_of_pos (crw_pos _ _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (crwd_abs_le hε _) (norm_nonneg _)
  have hall : X ≤ C * (Y + ‖ε‖ₑ * X) := h1.trans (by gcongr; exact h2.trans (by gcongr))
  have hεX : ‖ε‖ₑ * X ≠ ⊤ := ENNReal.mul_ne_top enorm_ne_top hX
  have hfin : (C : ℝ≥0∞) * (Y + ‖ε‖ₑ * X) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.add_ne_top.2 ⟨hY, hεX⟩)
  have hr := ENNReal.toReal_mono hfin hall
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hY hεX, ENNReal.toReal_mul, toReal_enorm,
    Real.norm_of_nonneg hε.le, ENNReal.coe_toReal] at hr
  have hx0 : 0 ≤ X.toReal := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
  have hxx := mul_le_mul_of_nonneg_right hCε hx0
  have hx : X.toReal ≤ 2 * C * Y.toReal := by nlinarith
  have hXle : X ≤ ENNReal.ofReal (2 * C) * Y := by
    rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hY, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hx
  rw [← crs_eLpNorm_sq v, ← crs_eLpNorm_sq f₁, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  exact ENNReal.rpow_le_rpow hXle (by norm_num)

theorem translationInvariant_slab_L2_bound_aux (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ K : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) ≤
        K * ∫⁻ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ₑ ^ p ∂cylMeasure := by
  obtain ⟨ε, hε, K₀, hK₀, hW⟩ := crs_weighted Sinf hS hnd
  have hq : 1 ≤ p / 2 := by linarith
  have hq0 : (0 : ℝ) ≤ p / 2 := by linarith
  set W := ∫⁻ y, ‖crw ε y‖ₑ ^ (2 : ℝ) with hWdef
  have hWt : W ≠ ⊤ := (crw_lintegral_lt_top hε).ne
  set L : ℝ≥0∞ := ENNReal.ofReal (1 + ε ^ 2) ^ (2 : ℝ) with hL
  have hLt : L ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  set M : ℝ≥0∞ := (L * K₀) ^ (p / 2) * W ^ (p / 2 - 1) * W with hMdef
  have hA : (L * K₀) ^ (p / 2) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hq0 (ENNReal.mul_ne_top hLt hK₀)
  have hB : W ^ (p / 2 - 1) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) hWt
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hA hB) hWt
  haveI : SFinite cylMeasure := by unfold cylMeasure; infer_instance
  refine ⟨M.toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal hM]
  set D := crOp (fun x : ℝ × ℝ => Sinf x.2) u with hD
  have hcD : Continuous D := crs_continuous_crOp Sinf hS.1 hu
  have hcw : ∀ a : ℝ, Continuous fun x : ℝ × ℝ => crw ε (x.1 - a) := fun a =>
    (crw_continuous ε).comp (continuous_fst.sub continuous_const)
  -- slab ≤ L · weighted norm
  have hslab : ∀ a : ℝ, (∫⁻ x in Set.Icc a (a + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ≤
      L * ∫⁻ x, ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
    intro a
    have hm : Measurable fun x : ℝ × ℝ => L * ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) :=
      ((((hcw a).smul hu.continuous).measurable.enorm.pow_const _).const_mul L)
    calc (∫⁻ x in Set.Icc a (a + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ))
        ≤ ∫⁻ x in Set.Icc a (a + 1) ×ˢ Set.Ico (0 : ℝ) 1,
            L * ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) := by
          refine setLIntegral_mono hm fun x hx => ?_
          have h1 : |x.1 - a| ≤ 1 := abs_le.2 ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
          have hreal : ‖u x‖ ≤ (1 + ε ^ 2) * ‖crw ε (x.1 - a) • u x‖ := by
            rw [norm_smul, Real.norm_of_nonneg (crw_pos _ _).le, ← mul_assoc]
            exact le_mul_of_one_le_left (norm_nonneg _) (crw_lower ε h1)
          have he : ‖u x‖ₑ ≤ ENNReal.ofReal (1 + ε ^ 2) * ‖crw ε (x.1 - a) • u x‖ₑ := by
            rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hreal
          calc ‖u x‖ₑ ^ (2 : ℝ)
              ≤ (ENNReal.ofReal (1 + ε ^ 2) * ‖crw ε (x.1 - a) • u x‖ₑ) ^ (2 : ℝ) :=
                ENNReal.rpow_le_rpow he (by norm_num)
            _ = L * ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) :=
                ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ ∫⁻ x in Set.univ ×ˢ Set.Ico (0 : ℝ) 1, L * ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) :=
          lintegral_mono_set (Set.prod_mono (Set.subset_univ _) le_rfl)
      _ = L * ∫⁻ x, ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
          rw [lintegral_const_mul' _ _ hLt]
          rfl
  -- weights and the integrand
  set w : ℝ → ℝ × ℝ → ℝ≥0∞ := fun a x => ‖crw ε (x.1 - a)‖ₑ ^ (2 : ℝ) with hw
  set F : ℝ × ℝ → ℝ≥0∞ := fun x => ‖D x‖ₑ ^ (2 : ℝ) with hF
  have hmw : ∀ a, Measurable (w a) := fun a => (hcw a).measurable.enorm.pow_const _
  have hmF : Measurable F := hcD.measurable.enorm.pow_const _
  have hsplit : ∀ a x, ‖crw ε (x.1 - a) • D x‖ₑ ^ (2 : ℝ) = w a x * F x := by
    intro a x
    rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hwint : ∀ a, ∫⁻ x, w a x ∂cylMeasure = W := by
    intro a
    rw [cylMeasure_eq_prod, lintegral_prod _ (hmw a).aemeasurable]
    simp only [hw, setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    exact lintegral_sub_right_eq_self (fun y => ‖crw ε y‖ₑ ^ (2 : ℝ)) a
  have hper : ∀ a : ℝ,
      (∫⁻ x in Set.Icc a (a + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2) ≤
        (L * K₀) ^ (p / 2) * (W ^ (p / 2 - 1) * ∫⁻ x, w a x * F x ^ (p / 2) ∂cylMeasure) := by
    intro a
    have hb : (∫⁻ x in Set.Icc a (a + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ≤
        L * K₀ * ∫⁻ x, w a x * F x ∂cylMeasure := by
      calc _ ≤ L * ∫⁻ x, ‖crw ε (x.1 - a) • u x‖ₑ ^ (2 : ℝ) ∂cylMeasure := hslab a
        _ ≤ L * (K₀ * ∫⁻ x, ‖crw ε (x.1 - a) • D x‖ₑ ^ (2 : ℝ) ∂cylMeasure) := by
            gcongr; exact hW u hu a
        _ = L * K₀ * ∫⁻ x, w a x * F x ∂cylMeasure := by
            simp_rw [hsplit]; rw [mul_assoc]
    calc _ ≤ (L * K₀ * ∫⁻ x, w a x * F x ∂cylMeasure) ^ (p / 2) := ENNReal.rpow_le_rpow hb hq0
      _ = (L * K₀) ^ (p / 2) * (∫⁻ x, w a x * F x ∂cylMeasure) ^ (p / 2) :=
          ENNReal.mul_rpow_of_nonneg _ _ hq0
      _ ≤ _ := by
          gcongr
          rw [← hwint a]
          exact crw_jensen cylMeasure (hmw a) hmF hq
  have hFq : ∀ x, F x ^ (p / 2) = ‖D x‖ₑ ^ p := by
    intro x
    rw [hF, ← ENNReal.rpow_mul]
    congr 1; ring
  have hmeas2 : AEMeasurable (Function.uncurry fun (a : ℝ) (x : ℝ × ℝ) => w a x * F x ^ (p / 2))
      ((volume : Measure ℝ).prod cylMeasure) := by
    have h1 : Measurable fun z : ℝ × (ℝ × ℝ) => ‖crw ε (z.2.1 - z.1)‖ₑ ^ (2 : ℝ) :=
      ((crw_continuous ε).comp (continuous_snd.fst.sub continuous_fst)).measurable.enorm.pow_const _
    exact (h1.mul ((hmF.pow_const _).comp measurable_snd)).aemeasurable
  calc (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2))
      ≤ ∫⁻ a : ℝ, (L * K₀) ^ (p / 2) * (W ^ (p / 2 - 1) *
          ∫⁻ x, w a x * F x ^ (p / 2) ∂cylMeasure) := lintegral_mono hper
    _ = (L * K₀) ^ (p / 2) * W ^ (p / 2 - 1) *
          ∫⁻ a : ℝ, ∫⁻ x, w a x * F x ^ (p / 2) ∂cylMeasure := by
        rw [lintegral_const_mul' _ _ hA, lintegral_const_mul' _ _ hB, mul_assoc]
    _ = (L * K₀) ^ (p / 2) * W ^ (p / 2 - 1) *
          ∫⁻ x, (∫⁻ a : ℝ, w a x * F x ^ (p / 2)) ∂cylMeasure := by
        rw [lintegral_lintegral_swap hmeas2]
    _ = (L * K₀) ^ (p / 2) * W ^ (p / 2 - 1) * ∫⁻ x, W * ‖D x‖ₑ ^ p ∂cylMeasure := by
        congr 1
        refine lintegral_congr fun x => ?_
        rw [lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0
          (ENNReal.rpow_ne_top_of_nonneg (by norm_num) enorm_ne_top)), hFq]
        simp only [hw]
        rw [crw_lintegral_shift]
    _ = M * ∫⁻ x, ‖D x‖ₑ ^ p ∂cylMeasure := by
        rw [lintegral_const_mul' _ _ hWt, hMdef]
        ring

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ K : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      (∫⁻ s : ℝ, (∫⁻ x in Set.Icc s (s + 1) ×ˢ Set.Ico (0 : ℝ) 1, ‖u x‖ₑ ^ (2 : ℝ)) ^ (p / 2)) ≤
        K * ∫⁻ x, ‖crOp (fun x : ℝ × ℝ => Sinf x.2) u x‖ₑ ^ p ∂cylMeasure :=
  translationInvariant_slab_L2_bound_aux n p hp Sinf hS hnd
