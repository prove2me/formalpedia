-- Prove2me | solution 1 for CauchyRiemannIndex.translationInvariant_L2_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T22:11:26.477992+00:00
-- url     : https://prove2.me/submissions/4f71e833-b86a-4a2f-bd4a-16ceb86d7ea2

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
import Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity
import Theorems.Thm_CauchyRiemannIndex_periodic_weak_solution_bound
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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

-- ===== Scratch/CRL2Bound.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

lemma crl2_inner_J_swap (a b : Vec n) :
    ⟪a, Matrix.toEuclideanLin (J₀ n) b⟫ = -⟪b, Matrix.toEuclideanLin (J₀ n) a⟫ := by
  rw [real_inner_comm, inner_toEuclideanLin, Matrix.J_transpose, map_neg, LinearMap.neg_apply,
    inner_neg_right]

lemma crl2_enorm_rpow_two (v : Vec n) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

/-- The asymptotic-operator part `J₀ ∂ₜu + S∞(t) u`. -/
def crl2A (Sinf : ℝ → Mat n) (u : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  Matrix.toEuclideanLin (J₀ n) (partialT u x) + Matrix.toEuclideanLin (Sinf x.2) (u x)

lemma crl2_continuous_A (Sinf : ℝ → Mat n) (hc : Continuous Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) : Continuous (crl2A Sinf u) :=
  ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT).add
    ((continuous_matCLM.comp (hc.comp continuous_snd)).clm_apply hu.continuous)

/-- Each slice `t ↦ u(s, t)` is a weak periodic solution with right-hand side `crl2A`. -/
lemma crl2_slice_weak (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) {u : ℝ × ℝ → Vec n}
    (hu : IsTestSection u) (s : ℝ) (ψ : ℝ → Vec n) (hψ : ContDiff ℝ ∞ ψ)
    (hψp : Function.Periodic ψ 1) :
    ∫ t in Set.Ico (0 : ℝ) 1, ⟪Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t), u (s, t)⟫ =
      ∫ t in Set.Ico (0 : ℝ) 1, ⟪ψ t, crl2A Sinf u (s, t)⟫ := by
  set J := Matrix.toEuclideanLin (J₀ n) with hJ
  have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hη : ∀ t, HasDerivAt (fun r => u (s, r)) (partialT u (s, t)) t := fun t =>
    (hud (s, t)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))
  have hJη : ∀ t, HasDerivAt (fun r => J (u (s, r))) (J (partialT u (s, t))) t := fun t =>
    (matCLM n (J₀ n)).hasFDerivAt.comp_hasDerivAt t (hη t)
  set h : ℝ → ℝ := fun t => ⟪ψ t, J (u (s, t))⟫ with hh
  set dh : ℝ → ℝ := fun t => ⟪ψ t, J (partialT u (s, t))⟫ + ⟪deriv ψ t, J (u (s, t))⟫ with hdh
  have hhd : ∀ t, HasDerivAt h (dh t) t := fun t => (hψd t).hasDerivAt.inner ℝ (hJη t)
  have hcψ' : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hcη : Continuous fun t => u (s, t) := hu.continuous.comp (continuous_const.prodMk continuous_id)
  have hcηT : Continuous fun t => partialT u (s, t) :=
    hu.continuous_partialT.comp (continuous_const.prodMk continuous_id)
  have hcJ : Continuous J := (matCLM n (J₀ n)).continuous
  have hcS : Continuous fun t => matCLM n (Sinf t) :=
    continuous_matCLM.comp hS.1
  have hdhc : Continuous dh :=
    (hψ.continuous.inner (hcJ.comp hcηT)).add (hcψ'.inner (hcJ.comp hcη))
  have hpt : ∀ t, ⟪J (deriv ψ t) + Matrix.toEuclideanLin (Sinf t) (ψ t), u (s, t)⟫ -
      ⟪ψ t, crl2A Sinf u (s, t)⟫ = -dh t := by
    intro t
    simp only [crl2A, hdh, inner_add_left, inner_add_right]
    rw [← hJ, real_inner_comm (u (s, t)) (J (deriv ψ t)), hJ,
      crl2_inner_J_swap (u (s, t)) (deriv ψ t), inner_toEuclideanLin (Sinf t) (ψ t) (u (s, t)),
      (hS.2.2 t).eq]
    ring
  have hL : Continuous fun t => ⟪J (deriv ψ t) + Matrix.toEuclideanLin (Sinf t) (ψ t), u (s, t)⟫ :=
    ((hcJ.comp hcψ').add (hcS.clm_apply hψ.continuous)).inner hcη
  have hR : Continuous fun t => ⟪ψ t, crl2A Sinf u (s, t)⟫ :=
    hψ.continuous.inner ((crl2_continuous_A Sinf hS.1 hu).comp (continuous_const.prodMk continuous_id))
  rw [← sub_eq_zero, ← integral_sub (hL.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
    (hR.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)]
  simp_rw [hpt]
  rw [integral_neg, neg_eq_zero, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hhd t) (hdhc.intervalIntegrable _ _)]
  simp only [hh, zero_add]
  rw [show (1 : ℝ) = 0 + 1 by norm_num, hψp 0, hu.2.1 s 0]
  simp

/-- The slice bound: `∫_{[0,1)} |u(s, ·)|² ≤ c² ∫_{[0,1)} |A u(s, ·)|²`. -/
lemma crl2_slice_bound (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf) (hnd : IsNondegenerate Sinf) :
    ∃ c : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ s : ℝ,
      ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖u (s, t)‖ₑ ^ (2 : ℝ) ≤
        (c : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖crl2A Sinf u (s, t)‖ₑ ^ (2 : ℝ) := by
  obtain ⟨C, hC⟩ := periodic_weak_solution_bound n Sinf hS hnd
  refine ⟨C.toNNReal, fun u hu s => ?_⟩
  set f : ℝ → Vec n := fun t => crl2A Sinf u (s, t) with hf
  have hcη : Continuous fun t => u (s, t) := hu.continuous.comp (continuous_const.prodMk continuous_id)
  have hcf : Continuous f :=
    (crl2_continuous_A Sinf hS.1 hu).comp (continuous_const.prodMk continuous_id)
  have hfi : IntegrableOn f (Set.Ico 0 1) := hcf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  have hb := hC (fun t => u (s, t)) f (hcη.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self) hfi
    (fun ψ hψ hψp => crl2_slice_weak Sinf hS hu s ψ hψ hψp)
  set I := ∫ t in Set.Ico (0 : ℝ) 1, ‖f t‖ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hIe : ENNReal.ofReal I = ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖f t‖ₑ :=
    ofReal_integral_norm_eq_lintegral_enorm hfi
  have hμ : (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ = 1 := by simp
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)),
      ‖u (s, t)‖ₑ ^ (2 : ℝ) ≤ ((C.toNNReal : ℝ≥0∞) * ENNReal.ofReal I) ^ (2 : ℝ) := by
    filter_upwards [hb] with t ht
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← ofReal_norm, ENNReal.ofReal_coe_nnreal.symm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (ht.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) hI0))
  calc ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖u (s, t)‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ t in Set.Ico (0 : ℝ) 1, ((C.toNNReal : ℝ≥0∞) * ENNReal.ofReal I) ^ (2 : ℝ) :=
        lintegral_mono_ae hpt
    _ = (C.toNNReal : ℝ≥0∞) ^ (2 : ℝ) * (∫⁻ t in Set.Ico (0 : ℝ) 1, ‖f t‖ₑ) ^ (2 : ℝ) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hIe]
    _ ≤ (C.toNNReal : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖f t‖ₑ ^ (2 : ℝ) := by
        gcongr
        have := crbox_jensen (volume.restrict (Set.Ico (0 : ℝ) 1)) (p := 2) (by norm_num)
          (f := fun t => ‖f t‖ₑ) hcf.enorm.aemeasurable
        rwa [hμ, ENNReal.one_rpow, one_mul] at this

theorem translationInvariant_L2_bound_aux (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u 2 cylMeasure ≤ C * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) 2 cylMeasure := by
  obtain ⟨c, hc⟩ := crl2_slice_bound Sinf hS hnd
  refine ⟨c, fun u hu => ?_⟩
  obtain ⟨R, hR⟩ := hu.2.2
  set D := crOp (fun x : ℝ × ℝ => Sinf x.2) u with hD
  have hcD : Continuous D :=
    (hu.continuous_partialS.add ((matCLM n (J₀ n)).continuous.comp hu.continuous_partialT)).add
      ((continuous_matCLM.comp (hS.1.comp continuous_snd)).clm_apply hu.continuous)
  have hcA := crl2_continuous_A Sinf hS.1 hu
  have hint : ∀ {f : ℝ × ℝ → ℝ}, Continuous f → (∀ s t, R < |s| → f (s, t) = 0) →
      Integrable f cylMeasure := by
    intro f hf hfz
    rw [← memLp_one_iff_integrable]
    exact memLp_of_vanish f hf R hfz
  -- `∫ |A u|² ≤ ∫ |D u|²`
  have hE := crOp_energy_identity n Sinf hS.1 hS.2.2 u hu
  have hAi : Integrable (fun x => ‖crl2A Sinf u x‖ ^ 2) cylMeasure :=
    hint (hcA.norm.pow 2) fun s t hs => by
      simp [crl2A, partialT_eq_zero R hR hs, hR s t hs]
  have hDi : Integrable (fun x => ‖D x‖ ^ 2) cylMeasure :=
    hint (hcD.norm.pow 2) fun s t hs => by
      simp [hD, crOp, partialT_eq_zero R hR hs, partialS_eq_zero R hR hs, hR s t hs]
  have hAD : ∫⁻ x, ‖crl2A Sinf u x‖ₑ ^ (2 : ℝ) ∂cylMeasure ≤ ∫⁻ x, ‖D x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
    simp_rw [crl2_enorm_rpow_two]
    rw [← ofReal_integral_eq_lintegral_ofReal hAi (ae_of_all _ fun _ => by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hDi (ae_of_all _ fun _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hE]
    have : 0 ≤ ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure := integral_nonneg fun _ => by positivity
    simp only [crl2A] at this ⊢
    linarith
  -- integrate the slice bound over `s`
  have hmeas : ∀ {g : ℝ × ℝ → Vec n}, Continuous g →
      ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂cylMeasure =
        ∫⁻ s, ∫⁻ t in Set.Ico (0 : ℝ) 1, ‖g (s, t)‖ₑ ^ (2 : ℝ) := by
    intro g hg
    rw [cylMeasure_eq_prod, lintegral_prod _ (hg.measurable.enorm.pow_const _).aemeasurable]
  have hU : ∫⁻ x, ‖u x‖ₑ ^ (2 : ℝ) ∂cylMeasure ≤
      (c : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ x, ‖D x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
    rw [hmeas hu.continuous]
    refine le_trans ?_ (by gcongr : (c : ℝ≥0∞) ^ (2 : ℝ) * ∫⁻ x, ‖crl2A Sinf u x‖ₑ ^ (2 : ℝ) ∂cylMeasure ≤ _)
    rw [hmeas hcA, ← lintegral_const_mul' _ _ (by simp)]
    exact lintegral_mono fun s => hc u hu s
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [← ENNReal.rpow_le_rpow_iff h2, ENNReal.mul_rpow_of_nonneg _ _ h2.le]
  have hconv : ∀ g : ℝ × ℝ → Vec n,
      eLpNorm g 2 cylMeasure ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂cylMeasure := by
    intro g
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [ENNReal.rpow_inv_rpow (by norm_num)]
  rw [hconv, hconv]
  exact hU

end

end CauchyRiemannIndex

open CauchyRiemannIndex MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    ∃ C : ℝ≥0, ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      eLpNorm u 2 cylMeasure ≤ C * eLpNorm (crOp (fun x : ℝ × ℝ => Sinf x.2) u) 2 cylMeasure :=
  translationInvariant_L2_bound_aux n Sinf hS hnd
