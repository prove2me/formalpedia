-- Prove2me | solution 1 for FiniteEnergyPlane.crApply_slope_injective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:39:01.519248+00:00
-- url     : https://prove2.me/submissions/a26893ae-ee4f-47fe-a5a6-cb6c7327fad1

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isNondegenerate_const_smul_one
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Theorems.Thm_CauchyRiemannIndex_finrank_quotient_eq_finrank_annihilator
import Theorems.Thm_CauchyRiemannIndex_memW1p_of_weak_solution
import Theorems.Thm_CauchyRiemannIndex_semiFredholm
import Theorems.Thm_CauchyRiemannIndex_crOp_formalAdjoint
import Theorems.Thm_CauchyRiemannIndex_eLpNorm_two_mul_le_w1pNorm
import Theorems.Thm_CauchyRiemannIndex_memLp_of_le_of_le
import Theorems.Thm_FiniteEnergyPlane_ode_weak_ae_eq
import Theorems.Thm_CauchyRiemannIndex_translationInvariant_bijective
import Theorems.Thm_FiniteEnergyPlane_ae_eq_zero_of_fourier_eq_zero
import Definitions.Def_FiniteEnergyPlane_Winding



/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-- `χ` is smooth with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`. -/
def IsSlopeWeight (χ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ s ≤ -1, deriv χ s = a) ∧ ∀ s ≥ 1, deriv χ s = b

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# The slope coefficient `χ'(s) • 1` is asymptotic to constant loops (local helper)
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Tg-As: the slope coefficient is asymptotic to constant loops -/

lemma deriv_slope_bdd {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ K, ∀ s, |deriv χ s| ≤ K := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max B (max |a| |b|), fun s => ?_⟩
  rcases le_or_gt s (-1) with h | h
  · rw [hχ.2.1 s h]; exact (le_max_left _ _).trans (le_max_right _ _)
  rcases le_or_gt 1 s with h' | h'
  · rw [hχ.2.2 s h']; exact (le_max_right _ _).trans (le_max_right _ _)
  · have := hB s ⟨h.le, h'.le⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- The homotopy `(1 - τ) χ'(s) + τ c`. -/
def slopeHom (χ : ℝ → ℝ) (c : ℝ) (τ : unitInterval) (x : ℝ × ℝ) : Mat 1 :=
  ((1 - (τ : ℝ)) * deriv χ x.1 + (τ : ℝ) * c) • (1 : Mat 1)

lemma slopeHom_isAsymptoticTo {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (c : ℝ)
    (τ : unitInterval) :
    IsAsymptoticTo (slopeHom χ c τ) (fun _ => ((1 - (τ : ℝ)) * b + (τ : ℝ) * c) • (1 : Mat 1))
      (fun _ => ((1 - (τ : ℝ)) * a + (τ : ℝ) * c) • (1 : Mat 1)) := by
  have hc : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  refine ⟨?_, fun s t => rfl, fun ε hε => ⟨1, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩⟩
  · unfold slopeHom
    exact ((continuous_const.mul (hc.comp continuous_fst)).add continuous_const).smul
      continuous_const
  · simp only [slopeHom, hχ.2.2 s hs, sub_self, abs_zero]; exact hε.le
  · simp only [slopeHom, hχ.2.1 s hs, sub_self, abs_zero]; exact hε.le

lemma convex_mem {a c : ℝ} (ha : a ∈ Ioo 0 (2 * π)) (hc : c ∈ Ioo 0 (2 * π))
    (τ : unitInterval) : (1 - (τ : ℝ)) * a + (τ : ℝ) * c ∈ Ioo 0 (2 * π) := by
  have h0 : 0 ≤ (τ : ℝ) := τ.2.1
  have h1 : (τ : ℝ) ≤ 1 := τ.2.2
  have hm : 0 < min a c := lt_min ha.1 hc.1
  have hM : max a c < 2 * π := max_lt ha.2 hc.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (min_le_right a c))]
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left a c)),
      mul_nonneg h0 (sub_nonneg.2 (le_max_right a c))]

end

end FiniteEnergyPlane

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal

noncomputable section

section Pairing

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

lemma cka_integrable (f : Lp E p μ) (g : Lp E q μ) :
    Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  have h := MemLp.of_bilin (r := 1) (fun a b => inner ℝ a b) 1 (Lp.memLp f) (Lp.memLp g)
    ((Lp.aestronglyMeasurable f).inner (Lp.aestronglyMeasurable g))
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  exact memLp_one_iff_integrable.1 h

/-- The pairing `∫ ⟨f, g⟩` as a bilinear map. -/
def ckaPair : Lp E p μ →ₗ[ℝ] Lp E q μ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun f g => ∫ x, inner ℝ (f x) (g x) ∂μ)
    (fun f f' g => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f' g)]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add f f'] with x hx
      rw [hx, Pi.add_apply, inner_add_left])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_left])
    (fun f g g' => by
      rw [← integral_add (cka_integrable f g) (cka_integrable f g')]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_add g g'] with x hx
      rw [hx, Pi.add_apply, inner_add_right])
    (fun c f g => by
      rw [smul_eq_mul, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_smul c g] with x hx
      rw [hx, Pi.smul_apply, real_inner_smul_right])

lemma ckaPair_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPair f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

omit [p.HolderConjugate q] in
/-- An `L^q` function orthogonal to all of `L^p` vanishes. -/
lemma cka_sep [SigmaFinite μ] [CompleteSpace E] (hp' : p ≠ ⊤) (hq' : q ≠ ⊤) (g : Lp E q μ)
    (hg : ∀ f : Lp E p μ, ∫ x, inner ℝ (f x) (g x) ∂μ = 0) : g = 0 := by
  have hq0 : q ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ q)).ne'
  have hint : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn (g : α → E) s μ := by
    intro s hs hμs
    haveI : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
    exact ((Lp.memLp g).restrict s).integrable Fact.out
  have hae := ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite (f := (g : α → E)) hint
    (fun s hs hμs => by
      rw [← inner_self_eq_zero (𝕜 := ℝ)]
      set e := ∫ x in s, (g : α → E) x ∂μ
      rw [← hg (indicatorConstLp p hs hμs.ne e)]
      calc inner ℝ e e = ∫ x in s, inner ℝ e ((g : α → E) x) ∂μ := by
            have := (innerSL ℝ e).integral_comp_comm (hint s hs hμs)
            simp only [innerSL_apply_apply] at this
            exact this.symm
        _ = ∫ x, s.indicator (fun x => inner ℝ e ((g : α → E) x)) x ∂μ :=
            (integral_indicator hs).symm
        _ = _ := by
            refine integral_congr_ae ?_
            filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := e)]
              with x hx
            rw [hx]
            by_cases hxs : x ∈ s
            · simp [Set.indicator_of_mem hxs]
            · simp [Set.indicator_of_notMem hxs])
  exact (Lp.eq_zero_iff_ae_eq_zero).2 hae


/-- Hölder's inequality for the pairing. -/
lemma cka_bound (f : Lp E p μ) (g : Lp E q μ) : ‖ckaPair f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [ckaPair_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hb := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := p) (q := q) (r := 1) (Lp.aestronglyMeasurable f)
    (Lp.aestronglyMeasurable g) (fun a b => inner ℝ a b) 1
    (Filter.Eventually.of_forall fun x => by
      rw [one_mul, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
      exact norm_inner_le_norm _ _)
  simp only [ENNReal.coe_one, one_mul] at hb
  have hi := cka_integrable f g
  rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm,
    Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) hb

/-- The pairing as a continuous bilinear map. -/
def ckaPairL : Lp E p μ →L[ℝ] Lp E q μ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ ckaPair 1 fun f g => by
    rw [one_mul, Real.norm_eq_abs, ← Real.norm_eq_abs]; exact cka_bound f g

lemma ckaPairL_apply (f : Lp E p μ) (g : Lp E q μ) :
    ckaPairL f g = ∫ x, inner ℝ (f x) (g x) ∂μ := rfl

end Pairing

end

end CauchyRiemannIndex

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

/-!
# Complex conjugation and the conjugated coefficient `S̄ = -C Sᵀ C`
-/

namespace CauchyRiemannIndex

open Matrix

noncomputable section

variable {n : ℕ}

/-- `A ↦ -C Aᵀ C`. -/
def cBar (A : Mat n) : Mat n := -(conjMat n * Aᵀ * conjMat n)

/-- The diagonal of `C`. -/
def cDiag (n : ℕ) : Fin n ⊕ Fin n → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)

lemma cDiag_mul_self (i : Fin n ⊕ Fin n) : cDiag n i * cDiag n i = 1 := by
  cases i <;> simp [cDiag]

lemma abs_cDiag (i : Fin n ⊕ Fin n) : |cDiag n i| = 1 := by
  cases i <;> simp [cDiag]

lemma conjMat_eq_diagonal : conjMat n = diagonal (cDiag n) := by
  unfold conjMat cDiag
  rw [← fromBlocks_diagonal, diagonal_one]
  congr 1
  rw [← diagonal_one, ← diagonal_neg]

lemma conjMat_mul_self : conjMat n * conjMat n = 1 := by
  rw [conjMat_eq_diagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  exact cDiag_mul_self i

lemma conjMat_transpose : (conjMat n)ᵀ = conjMat n := by
  rw [conjMat_eq_diagonal, diagonal_transpose]

lemma conjMat_mul_J : conjMat n * J₀ n = -(J₀ n * conjMat n) := by
  simp [conjMat, J₀, Matrix.J, fromBlocks_multiply, fromBlocks_neg]

lemma conj_entry (A : Mat n) (i j : Fin n ⊕ Fin n) :
    (conjMat n * A * conjMat n) i j = cDiag n i * A i j * cDiag n j := by
  rw [conjMat_eq_diagonal, mul_diagonal, diagonal_mul]

lemma cBar_entry (A : Mat n) (i j : Fin n ⊕ Fin n) :
    cBar A i j = -(cDiag n i * A j i * cDiag n j) := by
  rw [cBar, neg_apply, conj_entry, transpose_apply]

lemma abs_cBar_sub (A B : Mat n) (i j : Fin n ⊕ Fin n) :
    |cBar A i j - cBar B i j| = |A j i - B j i| := by
  rw [cBar_entry, cBar_entry, show -(cDiag n i * A j i * cDiag n j) - -(cDiag n i * B j i * cDiag n j)
    = -(cDiag n i * (A j i - B j i) * cDiag n j) by ring, abs_neg, abs_mul, abs_mul, abs_cDiag,
    abs_cDiag, one_mul, mul_one]

lemma cBar_transpose (A : Mat n) : (cBar A)ᵀ = -(conjMat n * A * conjMat n) := by
  rw [cBar, transpose_neg, transpose_mul, transpose_mul, transpose_transpose, conjMat_transpose,
    mul_assoc]

lemma continuous_cBar : Continuous (cBar : Mat n → Mat n) :=
  ((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).neg

lemma isSymLoop_cBar {T : ℝ → Mat n} (h : IsSymLoop T) : IsSymLoop (fun t => cBar (T t)) := by
  refine ⟨continuous_cBar.comp h.1, fun t => by simp only [h.2.1 t], fun t => ?_⟩
  show (cBar (T t))ᵀ = cBar (T t)
  rw [cBar_transpose, cBar, (h.2.2 t).eq]

lemma isAsymptoticTo_cBar {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n}
    (h : IsAsymptoticTo S Splus Sminus) :
    IsAsymptoticTo (fun x => cBar (S x)) (fun t => cBar (Splus t)) (fun t => cBar (Sminus t)) := by
  refine ⟨continuous_cBar.comp h.1, fun s t => by simp only [h.2.1 s t], fun ε hε => ?_⟩
  obtain ⟨R, hR⟩ := h.2.2 ε hε
  refine ⟨R, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [abs_cBar_sub]; exact (hR s t j i).1 hs
  · rw [abs_cBar_sub]; exact (hR s t j i).2 hs

lemma isNondegenerate_cBar {T : ℝ → Mat n} (hT : IsSymLoop T) (h : IsNondegenerate T) :
    IsNondegenerate (fun t => cBar (T t)) := by
  intro Ψ hΨ
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  set C := conjMat n
  have hCC : C * C = 1 := conjMat_mul_self
  have hfund : IsFundamentalSolution T (fun t => C * Ψ t * C) := by
    refine ⟨by simp [hΨ.1, hCC], fun t => ?_⟩
    have hsym : (T t)ᵀ = T t := (hT.2.2 t).eq
    have hCJ : C * J₀ n = -(J₀ n * C) := conjMat_mul_J
    have hd := ((hΨ.2 t).const_mul C).mul_const C
    have hb : cBar (T t) = -(C * T t * C) := by
      unfold cBar; rw [hsym]
    refine hd.congr_deriv ?_
    simp only []
    rw [hb]
    calc C * (J₀ n * -(C * T t * C) * Ψ t) * C = -(C * J₀ n * C * T t * C * Ψ t * C) := by
          noncomm_ring
      _ = J₀ n * (C * C) * T t * (C * Ψ t * C) := by
          rw [hCJ]; noncomm_ring
      _ = J₀ n * T t * (C * Ψ t * C) := by rw [hCC, mul_one]
  have hdet := h _ hfund
  intro h0
  apply hdet
  have : (1 : Mat n) - C * Ψ 1 * C = C * (1 - Ψ 1) * C := by
    rw [mul_sub, sub_mul, mul_one, hCC]
  rw [this, det_mul, det_mul, h0, mul_zero, zero_mul]

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

/-!
# Wendl, Lemma 4.17 / Proposition 4.18 / Theorem 4.20 on the cylinder

The `L^q` annihilator of `im D_S` is `C · ker D_{S̄}`, and the codimension of the closed range
equals the dimension of that annihilator.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### Pointwise algebra -/

lemma ckp_toEL_mul (A B : Mat n) (x : Vec n) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B x) = Matrix.toEuclideanLin (A * B) x := by
  simp [toEuclideanLin_apply, mulVec_mulVec]

lemma ckp_toEL_neg (A : Mat n) (x : Vec n) :
    Matrix.toEuclideanLin (-A) x = -Matrix.toEuclideanLin A x := by
  rw [map_neg, LinearMap.neg_apply]

lemma ckp_inner_conj (x y : Vec n) :
    inner ℝ (Matrix.toEuclideanLin (conjMat n) x) y =
      inner ℝ x (Matrix.toEuclideanLin (conjMat n) y) := by
  rw [inner_toEuclideanLin, conjMat_transpose]

lemma ckp_conj_conj (x : Vec n) :
    Matrix.toEuclideanLin (conjMat n) (Matrix.toEuclideanLin (conjMat n) x) = x := by
  rw [ckp_toEL_mul, conjMat_mul_self]
  simp [toEuclideanLin_apply]

/-- `C (-a + J₀ b + S̄ᵀ c) = -(C a + J₀ C b + A C c)`. -/
lemma ckp_key1 (A : Mat n) (a b c : Vec n) :
    Matrix.toEuclideanLin (conjMat n) (-a + Matrix.toEuclideanLin (J₀ n) b +
        Matrix.toEuclideanLin (cBar A)ᵀ c) =
      -(Matrix.toEuclideanLin (conjMat n) a +
        Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (conjMat n) b) +
        Matrix.toEuclideanLin A (Matrix.toEuclideanLin (conjMat n) c)) := by
  have e1 : conjMat n * J₀ n = -(J₀ n * conjMat n) := conjMat_mul_J
  have e2 : conjMat n * (cBar A)ᵀ = -(A * conjMat n) := by
    rw [cBar_transpose, mul_neg, ← mul_assoc, ← mul_assoc, conjMat_mul_self, one_mul]
  rw [map_add, map_add, map_neg, ckp_toEL_mul, ckp_toEL_mul, e1, e2, ckp_toEL_neg, ckp_toEL_neg,
    ← ckp_toEL_mul, ← ckp_toEL_mul]
  abel

/-- `-C a + J₀ C b + Aᵀ C c = -C (a + J₀ b + S̄ c)`. -/
lemma ckp_key2 (A : Mat n) (a b c : Vec n) :
    -Matrix.toEuclideanLin (conjMat n) a +
        Matrix.toEuclideanLin (J₀ n) (Matrix.toEuclideanLin (conjMat n) b) +
        Matrix.toEuclideanLin Aᵀ (Matrix.toEuclideanLin (conjMat n) c) =
      -Matrix.toEuclideanLin (conjMat n) (a + Matrix.toEuclideanLin (J₀ n) b +
        Matrix.toEuclideanLin (cBar A) c) := by
  have e1 : conjMat n * J₀ n = -(J₀ n * conjMat n) := conjMat_mul_J
  have e2 : conjMat n * cBar A = -(Aᵀ * conjMat n) := by
    rw [cBar, mul_neg, ← mul_assoc, ← mul_assoc, conjMat_mul_self, one_mul]
  symm
  rw [map_add, map_add, ckp_toEL_mul (conjMat n) (J₀ n), ckp_toEL_mul (conjMat n) (cBar A), e1, e2,
    ckp_toEL_neg, ckp_toEL_neg, ← ckp_toEL_mul, ← ckp_toEL_mul]
  abel

/-! ### Conjugated test sections -/

lemma IsTestSection.ckp_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) :
    IsTestSection (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) := by
  obtain ⟨R, hR⟩ := hφ.2.2
  refine ⟨(matCLM n (conjMat n)).contDiff.comp hφ.1, fun s t => by simp only [hφ.2.1], R,
    fun s t hs => by simp [hR s t hs]⟩

lemma ckp_partialS_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (x : ℝ × ℝ) :
    partialS (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) x =
      Matrix.toEuclideanLin (conjMat n) (partialS φ x) :=
  fderiv_matCLM_comp (conjMat n) (hφ.1.differentiable (by simp) x) (1, 0)

lemma ckp_partialT_conj {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) (x : ℝ × ℝ) :
    partialT (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) x =
      Matrix.toEuclideanLin (conjMat n) (partialT φ x) :=
  fderiv_matCLM_comp (conjMat n) (hφ.1.differentiable (by simp) x) (0, 1)

/-! ### Test triples -/

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma ckp_tt_mem {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) : testTriple (p := p) hu ∈ W1p p n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span (testTriple_mem hu))

lemma ckp_tt_ae (S : ℝ × ℝ → Mat n) {u : ℝ × ℝ → Vec n} (hu : IsTestSection u) :
    crApply S (testTriple (p := p) hu) =ᵐ[cylMeasure] crOp S u :=
  crApply_ae_crOp S (hu.memLp (p := p)).coeFn_toLp (hu.memLp_partialS (p := p)).coeFn_toLp
    (hu.memLp_partialT (p := p)).coeFn_toLp

/-- A continuous linear functional on triples vanishing on test triples vanishes on `W^{1,p}`. -/
lemma ckp_W1p_le_ker (Λ : Triple n p →L[ℝ] ℝ)
    (h : ∀ u : ℝ × ℝ → Vec n, ∀ hu : IsTestSection u, ∀ w ∈ testTriples n p,
      (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (w.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (w.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → Λ w = 0) :
    ∀ w ∈ W1p p n, Λ w = 0 := by
  have hle : W1p p n ≤ LinearMap.ker (Λ : Triple n p →ₗ[ℝ] ℝ) := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · refine Submodule.span_le.2 fun w hw => ?_
      obtain ⟨u, hu, h1, h2, h3⟩ := id hw
      exact h u hu w hw h1 h2 h3
    · exact Λ.isClosed_ker
  exact fun w hw => hle hw

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- The formal adjoint `D_S^* φ = -∂ₛφ + J₀ ∂ₜφ + Sᵀ φ`. -/
def ipkAdj (S : ℝ × ℝ → Mat n) (φ : ℝ × ℝ → Vec n) (x : ℝ × ℝ) : Vec n :=
  -partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
    Matrix.toEuclideanLin (S x)ᵀ (φ x)

lemma ipkAdj_continuous (S : ℝ × ℝ → Mat n) (hc : Continuous S) {φ : ℝ × ℝ → Vec n}
    (hφ : IsTestSection φ) : Continuous (ipkAdj S φ) := by
  have h3 : Continuous fun x => matCLM n (S x)ᵀ (φ x) :=
    (continuous_matCLM.comp hc.matrix_transpose).clm_apply hφ.continuous
  exact (hφ.continuous_partialS.neg.add
    ((matCLM n (J₀ n)).continuous.comp hφ.continuous_partialT)).add h3

lemma ipkAdj_vanish (S : ℝ × ℝ → Mat n) {φ : ℝ × ℝ → Vec n} (R : ℝ)
    (hR : ∀ s t, R < |s| → φ (s, t) = 0) :
    ∀ s t, R < |s| → ipkAdj S φ (s, t) = 0 := by
  intro s t hs
  simp [ipkAdj, partialS_eq_zero R hR hs, partialT_eq_zero R hR hs, hR s t hs]

lemma ipkAdj_memLp {q : ℝ≥0∞} [Fact (1 ≤ q)] (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) : MemLp (ipkAdj S φ) q cylMeasure := by
  obtain ⟨R, hR⟩ := hφ.2.2
  exact memLp_of_vanish _ (ipkAdj_continuous S hc hφ) R (ipkAdj_vanish S R hR)

/-- Elements of `ker D_S ⊆ W^{1,p}` are weak solutions of `D_S η = 0`. -/
lemma ipk_weak {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crsT S hc hb w = 0)
    (φ : ℝ × ℝ → Vec n) (hφ : IsTestSection φ) :
    ∫ x, inner ℝ (ipkAdj S φ x) (w.1 x) ∂cylMeasure = 0 := by
  set T : Triple n p →L[ℝ] LpCyl n p := crsT S hc hb
  set P := ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := q)
  set g1 : LpCyl n q := (hφ.memLp (p := q)).toLp φ
  set g2 : LpCyl n q := (ipkAdj_memLp (q := q) S hc hφ).toLp _
  let Λ : Triple n p →L[ℝ] ℝ :=
    (P.flip g1).comp T - (P.flip g2).comp (ContinuousLinearMap.fst ℝ _ _)
  have hΛ : ∀ v : Triple n p, Λ v = P (T v) g1 - P v.1 g2 := fun v => rfl
  have hW := ckp_W1p_le_ker Λ fun u hu v _ h1 h2 h3 => by
    have hA := crOp_formalAdjoint n S hc u φ hu hφ
    rw [hΛ, ckaPairL_apply, ckaPairL_apply, sub_eq_zero]
    have e1 : ∫ x, inner ℝ (T v x) (g1 x) ∂cylMeasure =
        ∫ x, inner ℝ (crOp S u x) (φ x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [crsT_ae S hc hb v, crApply_ae_crOp S h1 h2 h3,
        (hφ.memLp (p := q)).coeFn_toLp] with x e1 e2 e3
      rw [e1, e2, e3]
    have e2 : ∫ x, inner ℝ (v.1 x) (g2 x) ∂cylMeasure =
        ∫ x, inner ℝ (u x) (ipkAdj S φ x) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [h1, (ipkAdj_memLp (q := q) S hc hφ).coeFn_toLp] with x e1 e2
      rw [e1, e2]
    rw [e1, e2, hA]
    rfl
  have h := hW w hw
  rw [hΛ, show T w = 0 from h0, map_zero, ContinuousLinearMap.zero_apply, zero_sub,
    neg_eq_zero, ckaPairL_apply] at h
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [(ipkAdj_memLp (q := q) S hc hφ).coeFn_toLp] with x e
  rw [e, real_inner_comm]

/-- A kernel element whose first component lies in `L^r` gives a kernel element at exponent `r`. -/
lemma ipk_transfer {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1 < r) (hr' : r ≠ ⊤)
    {Splus Sminus : ℝ → Mat n} (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    {S : ℝ × ℝ → Mat n} (hS : IsAsymptoticTo S Splus Sminus)
    (w : Triple n p) (hw : w ∈ W1p p n) (h0 : crApply S w =ᵐ[cylMeasure] 0)
    (hmem : MemLp (w.1 : ℝ × ℝ → Vec n) r cylMeasure) :
    ∃ w' ∈ W1p r n, (w'.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] w.1 ∧
      crApply S w' =ᵐ[cylMeasure] 0 := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hb := crs_Sbound hSplus hSminus hS
  have hT0 : crsT S hS.1 hb w = 0 :=
    Lp.ext ((crsT_ae S hS.1 hb w).trans (h0.trans (Lp.coeFn_zero _ _ _).symm))
  have hweak : ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (S x)ᵀ (φ x)) (hmem.toLp _ x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) ((0 : LpCyl n r) x) ∂cylMeasure := by
    intro φ hφ
    have h := ipk_weak (q := p.conjExponent) S hS.1 hb w hw hT0 φ hφ
    have hR : ∫ x, inner ℝ (φ x) ((0 : LpCyl n r) x) ∂cylMeasure = 0 := by
      rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
      · simp
      filter_upwards [Lp.coeFn_zero (Vec n) r cylMeasure] with x hx
      rw [hx]; simp
    rw [hR, ← h]
    refine integral_congr_ae ?_
    filter_upwards [hmem.coeFn_toLp] with x e
    rw [e]; rfl
  obtain ⟨w', hw', hw1, hw0⟩ := memW1p_of_weak_solution n r hr hr' _ _ hSplus hSminus S hS
    (hmem.toLp _) 0 hweak
  refine ⟨w', hw', ?_, hw0.trans (Lp.coeFn_zero _ _ _)⟩
  rw [hw1]
  exact hmem.coeFn_toLp

/-- `W^{1,p}` functions are in `L^{2p}`. -/
lemma ipk_up {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (w : Triple n p) (hw : w ∈ W1p p n) :
    MemLp (w.1 : ℝ × ℝ → Vec n) (2 * p) cylMeasure := by
  obtain ⟨C, hC⟩ := eLpNorm_two_mul_le_w1pNorm n p hp hp'
  have hcl : w ∈ closure (Submodule.span ℝ (testTriples n p) : Set (Triple n p)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hw
  obtain ⟨a, ha, hlim⟩ := mem_closure_iff_seq_limit.1 hcl
  have ha' : ∀ j, a j ∈ testTriples n p := fun j => span_testTriples_subset (ha j)
  choose u hu h1 h2 h3 using ha'
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto a hlim)
  have hbd : ∀ j, eLpNorm ((a j).1 : ℝ × ℝ → Vec n) (2 * p) cylMeasure ≤
      C * ENNReal.ofReal (3 * B) := by
    intro j
    rw [eLpNorm_congr_ae (h1 j)]
    refine (hC (u j) (hu j)).trans ?_
    gcongr
    refine (crs_w1p_le (h1 j) (h2 j) (h3 j)).trans (ENNReal.ofReal_le_ofReal ?_)
    have := hB (a j) ⟨j, rfl⟩
    linarith
  have hl1 : Tendsto (fun j => (a j).1) atTop (𝓝 w.1) :=
    ((continuous_fst).tendsto w).comp hlim
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hl1).exists_seq_tendsto_ae
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2 * p)
    (fun i => Lp.aestronglyMeasurable (a (ns i)).1) _ hae
  refine ⟨Lp.aestronglyMeasurable _, lt_of_le_of_lt (hfat.trans
    (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun i => hbd (ns i)))) ?_⟩
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top

end

end CauchyRiemannIndex

namespace FiniteEnergyPlane.TgInj

open Metric Set

lemma exists_R_of_hasCompactSupport {ψ : ℝ → ℝ} (hψ : HasCompactSupport ψ) :
    ∃ R : ℝ, 0 < R ∧ ∀ s, R < |s| → ψ s = 0 := by
  obtain ⟨R, hR⟩ := hψ.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 1, by positivity, fun s hs => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun h => ?_
  have := hR h
  rw [mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_max_left R 1]

end FiniteEnergyPlane.TgInj

/-!
# Tg-Inj layer 3 (local, NOT published): Fourier-mode test sections

`modeVec k v t = cos(2πkt) v + sin(2πkt) J₀ v` and `modeSec ρ k v (s, t) = ρ(s) modeVec k v t`.
For `S = χ'(s) • 1`, the formal adjoint maps the mode section to
`(-ρ' + (χ' - 2πk) ρ)(s) • modeVec k v t`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Filter Topology Set CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- `J₀` on `ℝ²`. -/
abbrev Jv (v : Vec 1) : Vec 1 := Matrix.toEuclideanLin (J₀ 1) v

lemma Jv_Jv (v : Vec 1) : Jv (Jv v) = -v := by
  simp only [Jv]
  rw [ckp_toEL_mul, Matrix.J_squared, ckp_toEL_neg]
  simp

lemma toEL_smul_one (c : ℝ) (v : Vec 1) :
    Matrix.toEuclideanLin (c • (1 : Mat 1)) v = c • v := by
  simp

/-- `cos(2πkt) v + sin(2πkt) J₀ v`. -/
def modeVec (k : ℤ) (v : Vec 1) (t : ℝ) : Vec 1 :=
  Real.cos (2 * π * k * t) • v + Real.sin (2 * π * k * t) • Jv v

/-- Its `t`-derivative. -/
def modeVec' (k : ℤ) (v : Vec 1) (t : ℝ) : Vec 1 :=
  (-Real.sin (2 * π * k * t) * (2 * π * k)) • v + (Real.cos (2 * π * k * t) * (2 * π * k)) • Jv v

lemma hasDerivAt_modeVec (k : ℤ) (v : Vec 1) (t : ℝ) :
    HasDerivAt (modeVec k v) (modeVec' k v t) t := by
  have hl : HasDerivAt (fun t : ℝ => 2 * π * k * t) (2 * π * k) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π * k)
  have h1 := (hl.cos).smul_const v
  have h2 := (hl.sin).smul_const (Jv v)
  exact (h1.add h2).congr_deriv (by simp only [modeVec', neg_mul])

lemma contDiff_modeVec (k : ℤ) (v : Vec 1) : ContDiff ℝ ∞ (modeVec k v) := by
  unfold modeVec
  have hl : ContDiff ℝ ∞ (fun t : ℝ => 2 * π * k * t) := contDiff_const.mul contDiff_id
  exact ((Real.contDiff_cos.comp hl).smul contDiff_const).add
    ((Real.contDiff_sin.comp hl).smul contDiff_const)

lemma modeVec_periodic (k : ℤ) (v : Vec 1) (t : ℝ) : modeVec k v (t + 1) = modeVec k v t := by
  have e : 2 * π * k * (t + 1) = 2 * π * k * t + k * (2 * π) := by ring
  simp only [modeVec, e, Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

lemma Jv_modeVec' (k : ℤ) (v : Vec 1) (t : ℝ) :
    Jv (modeVec' k v t) = -((2 * π * k) • modeVec k v t) := by
  simp only [modeVec', modeVec, map_add, map_smul, Jv_Jv, smul_neg, smul_add, smul_smul]
  module

/-- The mode section `ρ(s) modeVec k v t`. -/
def modeSec (ρ : ℝ → ℝ) (k : ℤ) (v : Vec 1) (x : ℝ × ℝ) : Vec 1 := ρ x.1 • modeVec k v x.2

lemma hasFDerivAt_modeSec {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ) (k : ℤ) (v : Vec 1)
    (x : ℝ × ℝ) :
    HasFDerivAt (modeSec ρ k v)
      (ρ x.1 • ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (modeVec' k v x.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) +
        (deriv ρ x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (modeVec k v x.2)) x := by
  have hc : HasFDerivAt (fun y : ℝ × ℝ => ρ y.1) (deriv ρ x.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) x :=
    (hρ x.1).hasDerivAt.comp_hasFDerivAt x hasFDerivAt_fst
  have hm : HasFDerivAt (fun y : ℝ × ℝ => modeVec k v y.2)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (modeVec' k v x.2)).comp
        (ContinuousLinearMap.snd ℝ ℝ ℝ)) x :=
    (hasDerivAt_modeVec k v x.2).hasFDerivAt.comp x hasFDerivAt_snd
  exact hc.smul hm

lemma partialS_modeSec {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ) (k : ℤ) (v : Vec 1) (x : ℝ × ℝ) :
    partialS (modeSec ρ k v) x = deriv ρ x.1 • modeVec k v x.2 := by
  simp [partialS, (hasFDerivAt_modeSec hρ k v x).fderiv]

lemma partialT_modeSec {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ) (k : ℤ) (v : Vec 1) (x : ℝ × ℝ) :
    partialT (modeSec ρ k v) x = ρ x.1 • modeVec' k v x.2 := by
  simp [partialT, (hasFDerivAt_modeSec hρ k v x).fderiv]

lemma isTestSection_modeSec {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (k : ℤ) (v : Vec 1) : IsTestSection (modeSec ρ k v) := by
  obtain ⟨R, -, hR⟩ := TgInj.exists_R_of_hasCompactSupport hρc
  refine ⟨(hρ.comp contDiff_fst).smul ((contDiff_modeVec k v).comp contDiff_snd),
    fun s t => by simp only [modeSec, modeVec_periodic], R, fun s t hs => by
      simp [modeSec, hR s hs]⟩

/-- The formal adjoint on a mode section. -/
lemma ipkAdj_modeSec (χ : ℝ → ℝ) {ρ : ℝ → ℝ} (hρ : Differentiable ℝ ρ) (k : ℤ) (v : Vec 1)
    (x : ℝ × ℝ) :
    ipkAdj (fun y : ℝ × ℝ => deriv χ y.1 • (1 : Mat 1)) (modeSec ρ k v) x =
      (-deriv ρ x.1 + (deriv χ x.1 - 2 * π * k) * ρ x.1) • modeVec k v x.2 := by
  have e : Matrix.toEuclideanLin (J₀ 1) (ρ x.1 • modeVec' k v x.2) =
      ρ x.1 • Jv (modeVec' k v x.2) := map_smul _ _ _
  simp only [ipkAdj, partialS_modeSec hρ, partialT_modeSec hρ, Matrix.transpose_smul,
    Matrix.transpose_one, toEL_smul_one, modeSec, e, Jv_modeVec']
  module

end

end FiniteEnergyPlane

/-!
# Tg-Inj layer 4 (local, NOT published): every Fourier mode of a kernel element vanishes

`modeCoef W k v s = ∫₀¹ ⟨modeVec k v t, W(s, t)⟩ dt`. For `w` in the kernel of
`∂ₛ + J₀ ∂ₜ + χ'(s)` on `W^{1,p}` (slopes in `(0, 2π)`), `modeCoef w.1 k v = 0` a.e.
-/

namespace FiniteEnergyPlane

open MeasureTheory Filter Topology Set CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

lemma tg_cyl_eq_prod :
    cylMeasure = (volume : Measure ℝ).prod (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [cylMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma tg_cyl_restrict (K : Set ℝ) :
    cylMeasure.restrict (K ×ˢ univ) =
      (volume.restrict K).prod (volume.restrict (Ico (0 : ℝ) 1)) := by
  rw [tg_cyl_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

lemma tg_cyl_box (K : Set ℝ) (hK : MeasurableSet K) :
    cylMeasure (K ×ˢ univ) = volume K := by
  rw [tg_cyl_eq_prod, Measure.prod_prod, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]

lemma norm_modeVec_le (k : ℤ) (v : Vec 1) (t : ℝ) : ‖modeVec k v t‖ ≤ ‖v‖ + ‖Jv v‖ := by
  unfold modeVec
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul, Real.norm_eq_abs]
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- The `k`-th Fourier pairing of `W` in direction `v`, as a function of `s`. -/
def modeCoef (W : ℝ × ℝ → Vec 1) (k : ℤ) (v : Vec 1) (s : ℝ) : ℝ :=
  ∫ t in Ico (0 : ℝ) 1, inner ℝ (modeVec k v t) (W (s, t))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {W : ℝ × ℝ → Vec 1}

lemma integrableOn_strip (hW : MemLp W p cylMeasure) (K : Set ℝ) (hK : MeasurableSet K)
    (hKf : volume K ≠ ⊤) : IntegrableOn W (K ×ˢ univ) cylMeasure := by
  haveI : IsFiniteMeasure (cylMeasure.restrict (K ×ˢ univ)) :=
    isFiniteMeasure_restrict.2 (by rw [tg_cyl_box K hK]; exact hKf)
  exact (hW.restrict _).integrable Fact.out

lemma aesm_pair (hW : MemLp W p cylMeasure) (k : ℤ) (v : Vec 1) {μ : Measure (ℝ × ℝ)}
    (hμ : μ ≪ cylMeasure) :
    AEStronglyMeasurable (fun x : ℝ × ℝ => inner ℝ (modeVec k v x.2) (W x)) μ :=
  (((contDiff_modeVec k v).continuous.comp continuous_snd).aestronglyMeasurable).inner
    (hW.1.mono_ac hμ)

lemma integrable_pair_box (hW : MemLp W p cylMeasure) (k : ℤ) (v : Vec 1) (K : Set ℝ)
    (hK : MeasurableSet K) (hKf : volume K ≠ ⊤) :
    Integrable (fun x : ℝ × ℝ => inner ℝ (modeVec k v x.2) (W x))
      ((volume.restrict K).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
  rw [← tg_cyl_restrict]
  refine Integrable.mono' ((integrableOn_strip hW K hK hKf).norm.const_mul (‖v‖ + ‖Jv v‖))
    (aesm_pair hW k v Measure.restrict_le_self.absolutelyContinuous)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_modeVec_le k v x.2) (norm_nonneg _))

lemma locallyIntegrable_modeCoef (hW : MemLp W p cylMeasure) (k : ℤ) (v : Vec 1) :
    LocallyIntegrable (modeCoef W k v) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (integrable_pair_box hW k v K hK.measurableSet hK.measure_lt_top.ne).integral_prod_left

/-- Fubini for a compactly supported `s`-weight. -/
lemma integral_weight_pair (hW : MemLp W p cylMeasure) (k : ℤ) (v : Vec 1) {η : ℝ → ℝ}
    (hη : Continuous η) {R : ℝ} (hR : ∀ s, R < |s| → η s = 0) :
    ∫ x, η x.1 * inner ℝ (modeVec k v x.2) (W x) ∂cylMeasure =
      ∫ s, η s * modeCoef W k v s := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hη.continuousOn
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hint : Integrable (fun x : ℝ × ℝ => η x.1 * inner ℝ (modeVec k v x.2) (W x))
      cylMeasure := by
    have hI := (integrableOn_strip hW (Icc (-R) R) measurableSet_Icc
      (by simp)).norm.const_mul (max M 0 * (‖v‖ + ‖Jv v‖))
    refine Integrable.mono' (IntegrableOn.integrable_indicator hI
      (measurableSet_Icc.prod MeasurableSet.univ))
      (((hη.comp continuous_fst).aestronglyMeasurable).mul (aesm_pair hW k v
        (Measure.AbsolutelyContinuous.refl _))) (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Icc (-R) R ×ˢ (univ : Set ℝ)
    · rw [indicator_of_mem hx, norm_mul]
      have h1 : ‖η x.1‖ ≤ max M 0 := (hM x.1 hx.1).trans (le_max_left _ _)
      have h2 : ‖inner ℝ (modeVec k v x.2) (W x)‖ ≤ (‖v‖ + ‖Jv v‖) * ‖W x‖ := by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (norm_modeVec_le k v x.2) (norm_nonneg _))
      calc ‖η x.1‖ * ‖inner ℝ (modeVec k v x.2) (W x)‖
          ≤ max M 0 * ((‖v‖ + ‖Jv v‖) * ‖W x‖) := by gcongr
        _ = _ := by ring
    · rw [indicator_of_notMem hx]
      have : R < |x.1| := by
        simp only [mem_prod, mem_Icc, mem_univ, and_true, not_and_or, not_le] at hx
        rcases hx with h | h
        · linarith [neg_abs_le x.1]
        · linarith [le_abs_self x.1]
      simp [hR x.1 this]
  rw [tg_cyl_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [modeCoef]
  exact integral_const_mul _ _

/-! ### The weak ODE of each mode -/

lemma deriv_eq_zero_of_vanish {ρ : ℝ → ℝ} {R : ℝ} (hR : ∀ s, R < |s| → ρ s = 0) {s : ℝ}
    (hs : R < |s|) : deriv ρ s = 0 := by
  have hev : ρ =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hs] with y hy
    exact hR y hy
  rw [hev.deriv_eq, deriv_const]

lemma deriv_lam {χ : ℝ → ℝ} (hχ : Differentiable ℝ χ) (k : ℤ) (s : ℝ) :
    deriv (fun s => χ s - 2 * π * k * s) s = deriv χ s - 2 * π * k := by
  have h := (hχ s).hasDerivAt.sub ((hasDerivAt_id s).const_mul (2 * π * k))
  rw [mul_one] at h
  exact h.deriv

lemma slope_bound {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (x : ℝ × ℝ) (v : Vec 1),
      ‖Matrix.toEuclideanLin ((fun y : ℝ × ℝ => deriv χ y.1 • (1 : Mat 1)) x) v‖ ≤ M * ‖v‖ := by
  obtain ⟨K, hK⟩ := deriv_slope_bdd hχ
  refine ⟨K, (abs_nonneg _).trans (hK 0), fun x v => ?_⟩
  simp only [toEL_smul_one, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)

/-- Each mode satisfies the weak ODE `-η' + Λ' η` with `Λ = χ - 2πk s`. -/
lemma modeCoef_weak {a b : ℝ} {χ : ℝ → ℝ} (hχ : IsSlopeWeight χ a b) (w : Triple 1 p)
    (hw : w ∈ W1p p 1)
    (h0 : crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0) (k : ℤ) (v : Vec 1)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∫ s, (-deriv ρ s + deriv (fun s => χ s - 2 * π * k * s) s * ρ s) •
      modeCoef (w.1 : ℝ × ℝ → Vec 1) k v s = 0 := by
  have hc : Continuous (fun y : ℝ × ℝ => deriv χ y.1 • (1 : Mat 1)) :=
    ((hχ.1.continuous_deriv (by simp)).comp continuous_fst).smul continuous_const
  have hb := slope_bound hχ
  have hT0 : crsT _ hc hb w = 0 :=
    Lp.ext ((crsT_ae _ hc hb w).trans (h0.trans (Lp.coeFn_zero _ _ _).symm))
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by simp)
  have h := ipk_weak (q := p.conjExponent) _ hc hb w hw hT0 (modeSec ρ k v)
    (isTestSection_modeSec hρ hρc k v)
  simp only [ipkAdj_modeSec χ hρd k v, real_inner_smul_left] at h
  obtain ⟨R, -, hR⟩ := TgInj.exists_R_of_hasCompactSupport hρc
  have hηc : Continuous fun s => -deriv ρ s + (deriv χ s - 2 * π * k) * ρ s :=
    (hρ.continuous_deriv (by simp)).neg.add
      (((hχ.1.continuous_deriv (by simp)).sub continuous_const).mul hρ.continuous)
  rw [integral_weight_pair (Lp.memLp w.1) k v hηc (R := R) fun s hs => by
    simp [deriv_eq_zero_of_vanish hR hs, hR s hs]] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [deriv_lam (hχ.1.differentiable (by simp)), smul_eq_mul]

/-! ### Killing the constant -/

lemma lint_box_le (hW : MemLp W p cylMeasure) (k : ℤ) (v : Vec 1) (c : ℝ) :
    ∫⁻ s in Icc c (c + 1), ‖modeCoef W k v s‖ₑ ≤
      ENNReal.ofReal (‖v‖ + ‖Jv v‖) * eLpNorm W p cylMeasure := by
  set B := ‖v‖ + ‖Jv v‖ with hB
  have hpt : ∀ x : ℝ × ℝ, ‖inner ℝ (modeVec k v x.2) (W x)‖ₑ ≤ ENNReal.ofReal B * ‖W x‖ₑ := by
    intro x
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_modeVec_le k v x.2) (norm_nonneg _))
  have hmeas : AEMeasurable (fun x : ℝ × ℝ => ENNReal.ofReal B * ‖W x‖ₑ)
      ((volume.restrict (Icc c (c + 1))).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [← tg_cyl_restrict]
    exact (hW.1.enorm.restrict).const_mul _
  have hmu : cylMeasure.restrict (Icc c (c + 1) ×ˢ univ) univ = 1 := by
    rw [Measure.restrict_apply_univ, tg_cyl_box _ measurableSet_Icc, Real.volume_Icc,
      add_sub_cancel_left, ENNReal.ofReal_one]
  calc ∫⁻ s in Icc c (c + 1), ‖modeCoef W k v s‖ₑ
      ≤ ∫⁻ s in Icc c (c + 1), ∫⁻ t in Ico (0 : ℝ) 1, ENNReal.ofReal B * ‖W (s, t)‖ₑ :=
        lintegral_mono fun s => (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun t => hpt (s, t))
    _ = ∫⁻ x, ENNReal.ofReal B * ‖W x‖ₑ ∂(cylMeasure.restrict (Icc c (c + 1) ×ˢ univ)) := by
        rw [tg_cyl_restrict, lintegral_prod _ hmeas]
    _ = ENNReal.ofReal B * eLpNorm W 1 (cylMeasure.restrict (Icc c (c + 1) ×ˢ univ)) := by
        rw [lintegral_const_mul'' _ (hW.1.enorm.restrict), eLpNorm_one_eq_lintegral_enorm]
    _ ≤ ENNReal.ofReal B * eLpNorm W p cylMeasure := by
        gcongr
        refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := p)
          (Fact.out : (1 : ℝ≥0∞) ≤ p) hW.1.restrict).trans ?_
        rw [hmu, ENNReal.one_rpow, mul_one]
        exact eLpNorm_mono_measure _ Measure.restrict_le_self

lemma const_eq_zero_of_box (Λ : ℝ → ℝ) (C : ℝ) (f : ℝ → ℝ)
    (hf : ∀ᵐ s, f s = Real.exp (-Λ s) • C) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (hbox : ∀ c, ∫⁻ s in Icc c (c + 1), ‖f s‖ₑ ≤ K)
    (hgrow : ∀ M : ℝ, ∃ c, ∀ s ∈ Icc c (c + 1), M ≤ -Λ s) : C = 0 := by
  by_contra hC
  have hCpos : 0 < |C| := abs_pos.2 hC
  set M := (K.toReal + 1) / |C| with hM
  obtain ⟨c, hc⟩ := hgrow M
  have hle : ENNReal.ofReal (K.toReal + 1) ≤ K := by
    calc ENNReal.ofReal (K.toReal + 1) = ∫⁻ _ in Icc c (c + 1), ENNReal.ofReal (M * |C|) := by
          rw [setLIntegral_const, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one,
            mul_one, hM, div_mul_cancel₀ _ hCpos.ne']
      _ ≤ ∫⁻ s in Icc c (c + 1), ‖f s‖ₑ := by
          refine setLIntegral_mono_ae' measurableSet_Icc ?_
          filter_upwards [hf] with s hs hsI
          rw [hs, ← ofReal_norm_eq_enorm, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
          linarith [hc s hsI, Real.add_one_le_exp (-Λ s)]
      _ ≤ K := hbox c
  have := (ENNReal.lt_ofReal_iff_toReal_lt hK).2 (lt_add_one K.toReal)
  exact absurd hle (not_le.2 this)

lemma lam_grow {χ : ℝ → ℝ} {a b : ℝ} (hχ : IsSlopeWeight χ a b) (ha : a ∈ Ioo 0 (2 * π))
    (hb : b ∈ Ioo 0 (2 * π)) (k : ℤ) (M : ℝ) :
    ∃ c, ∀ s ∈ Icc c (c + 1), M ≤ -(χ s - 2 * π * k * s) := by
  rcases le_or_gt 1 k with hk | hk
  · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hd : 0 < 2 * π - b := by linarith [hb.2]
    refine ⟨max 1 ((M + χ 1 - b) / (2 * π - b)), fun s hs => ?_⟩
    have hs1 : 1 ≤ s := (le_max_left _ _).trans hs.1
    have hcs : (M + χ 1 - b) / (2 * π - b) ≤ s := (le_max_right _ _).trans hs.1
    rw [div_le_iff₀ hd] at hcs
    rw [hχ.eq_right hs1]
    nlinarith [mul_nonneg (sub_nonneg.2 hk') (by linarith : (0 : ℝ) ≤ s), Real.pi_pos]
  · have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast (Int.lt_add_one_iff.1 hk)
    have ha0 : 0 < a := ha.1
    set m := max 1 ((M + χ (-1) + a) / a) with hm
    refine ⟨-m - 1, fun s hs => ?_⟩
    have hsm : s ≤ -m := by linarith [hs.2]
    have hs1 : s ≤ -1 := hsm.trans (by linarith [le_max_left 1 ((M + χ (-1) + a) / a)])
    have hcs : (M + χ (-1) + a) / a ≤ m := le_max_right _ _
    rw [div_le_iff₀ ha0] at hcs
    rw [hχ.eq_left hs1]
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hk' (by linarith : s ≤ 0), Real.pi_pos]

/-- Tg-Inj layer 4: every mode of a kernel element vanishes. -/
theorem modeCoef_ae_eq_zero (hp' : p ≠ ⊤) {a b : ℝ} (ha : a ∈ Ioo 0 (2 * π))
    (hb : b ∈ Ioo 0 (2 * π)) {χ : ℝ → ℝ} (hχ : IsSlopeWeight χ a b) (w : Triple 1 p)
    (hw : w ∈ W1p p 1)
    (h0 : crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0) (k : ℤ) (v : Vec 1) :
    ∀ᵐ s, modeCoef (w.1 : ℝ × ℝ → Vec 1) k v s = 0 := by
  have hW := Lp.memLp w.1
  have hΛ : ContDiff ℝ ∞ (fun s => χ s - 2 * π * k * s) :=
    hχ.1.sub (contDiff_const.mul contDiff_id)
  obtain ⟨C, hC⟩ := ode_weak_ae_eq _ hΛ (modeCoef (w.1 : ℝ × ℝ → Vec 1) k v)
    (locallyIntegrable_modeCoef hW k v) fun ρ hρ hρc => modeCoef_weak hχ w hw h0 k v ρ hρ hρc
  have hC0 : C = 0 := const_eq_zero_of_box _ C _ hC
    (ENNReal.ofReal (‖v‖ + ‖Jv v‖) * eLpNorm (w.1 : ℝ × ℝ → Vec 1) p cylMeasure)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hW.eLpNorm_lt_top.ne))
    (lint_box_le hW k v) (lam_grow hχ ha hb k)
  filter_upwards [hC] with s hs
  rw [hs, hC0, smul_zero]

end

end FiniteEnergyPlane

/-!
# Tg-Inj layer 5 (local, NOT published): the kernel is zero

* `fst_ae_eq_zero_of_kernel`: all modes vanish, so `w.1 = 0` a.e. (Fourier completeness on slices).
* `crApply_slope_injective_proof`: then `w` lies in the kernel of the translation-invariant operator
  `∂ₛ + J₀ ∂ₜ + a`, which is zero (4.11).
-/

namespace FiniteEnergyPlane

open MeasureTheory Filter Topology Set CauchyRiemannIndex
open scoped ContDiff Real ENNReal

noncomputable section

/-- `e₁ = (1, 0)`. -/
abbrev e₁ : Vec 1 := EuclideanSpace.single (Sum.inl 0) 1
/-- `e₂ = (0, 1)`. -/
abbrev e₂ : Vec 1 := EuclideanSpace.single (Sum.inr 0) 1

lemma Jv_e₁ : Jv e₁ = e₂ := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Jv, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, EuclideanSpace.single_apply]

lemma Jv_e₂ : Jv e₂ = -e₁ := by
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Jv, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, EuclideanSpace.single_apply]

lemma inner_modeVec_e₁ (k : ℤ) (t : ℝ) (y : Vec 1) :
    inner ℝ (modeVec k e₁ t) y =
      Real.cos (2 * π * k * t) * y (Sum.inl 0) + Real.sin (2 * π * k * t) * y (Sum.inr 0) := by
  simp [modeVec, Jv_e₁, inner_add_left, real_inner_smul_left, EuclideanSpace.inner_single_left]

lemma inner_modeVec_e₂ (k : ℤ) (t : ℝ) (y : Vec 1) :
    inner ℝ (modeVec k e₂ t) y =
      Real.cos (2 * π * k * t) * y (Sum.inr 0) - Real.sin (2 * π * k * t) * y (Sum.inl 0) := by
  simp [modeVec, Jv_e₂, inner_add_left, inner_neg_left, real_inner_smul_left,
    EuclideanSpace.inner_single_left, sub_eq_add_neg]

/-- `vecToC` as a continuous linear map. -/
def vecToCL : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

lemma vecToCL_apply (a : Vec 1) : vecToCL a = vecToC a := rfl

lemma eq_zero_of_vecToC_eq_zero {a : Vec 1} (h : vecToC a = 0) : a = 0 := by
  have h1 : a (Sum.inl 0) = 0 := by simpa [vecToC] using congrArg Complex.re h
  have h2 : a (Sum.inr 0) = 0 := by simpa [vecToC] using congrArg Complex.im h
  ext i
  rcases i with i | i <;> fin_cases i
  · exact h1
  · exact h2

lemma exp_mul_vecToC (k : ℤ) (t : ℝ) (y : Vec 1) :
    Complex.exp (2 * π * Complex.I * k * t) * vecToC y =
      (inner ℝ (modeVec (-k) e₁ t) y : ℂ) + Complex.I * (inner ℝ (modeVec (-k) e₂ t) y : ℂ) := by
  have e : 2 * π * Complex.I * k * t = ((2 * π * k * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  have e2 : 2 * π * ((-k : ℤ) : ℝ) * t = -(2 * π * k * t) := by push_cast; ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, inner_modeVec_e₁,
    inner_modeVec_e₂, e2, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp [vecToC] <;> ring

/-- `⋃ₙ [-n, n] = ℝ`. -/
lemma iUnion_Icc_nat : (⋃ N : ℕ, Icc (-(N : ℝ)) N) = univ := by
  refine eq_univ_of_forall fun s => mem_iUnion.2 ?_
  obtain ⟨N, hN⟩ := exists_nat_ge |s|
  exact ⟨N, abs_le.1 hN⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma ae_integrable_slice {W : ℝ × ℝ → Vec 1} (hW : MemLp W p cylMeasure) :
    ∀ᵐ s, Integrable (fun t => W (s, t)) (volume.restrict (Ico (0 : ℝ) 1)) := by
  have h : ∀ N : ℕ, ∀ᵐ s ∂(volume.restrict (Icc (-(N : ℝ)) N)),
      Integrable (fun t => W (s, t)) (volume.restrict (Ico (0 : ℝ) 1)) := by
    intro N
    have hI := integrableOn_strip hW (Icc (-(N : ℝ)) N) measurableSet_Icc (by simp)
    rw [IntegrableOn, tg_cyl_restrict] at hI
    exact hI.prod_right_ae
  have := (ae_restrict_iUnion_iff (fun N : ℕ => Icc (-(N : ℝ)) N) _).2 h
  rwa [iUnion_Icc_nat, Measure.restrict_univ] at this

/-- Tg-Inj layer 5a: a kernel element has `w.1 = 0` a.e. -/
theorem fst_ae_eq_zero_of_kernel (hp' : p ≠ ⊤) {a b : ℝ} (ha : a ∈ Ioo 0 (2 * π))
    (hb : b ∈ Ioo 0 (2 * π)) {χ : ℝ → ℝ} (hχ : IsSlopeWeight χ a b) (w : Triple 1 p)
    (hw : w ∈ W1p p 1)
    (h0 : crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0) :
    (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 := by
  set W : ℝ × ℝ → Vec 1 := (w.1 : ℝ × ℝ → Vec 1) with hWdef
  have hW : MemLp W p cylMeasure := Lp.memLp w.1
  have hmodes : ∀ᵐ s, ∀ k : ℤ, modeCoef W k e₁ s = 0 ∧ modeCoef W k e₂ s = 0 := by
    rw [ae_all_iff]
    intro k
    filter_upwards [modeCoef_ae_eq_zero hp' ha hb hχ w hw h0 k e₁,
      modeCoef_ae_eq_zero hp' ha hb hχ w hw h0 k e₂] with s h1 h2
    exact ⟨h1, h2⟩
  -- slice-wise vanishing
  have hslice : ∀ᵐ s, ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), W (s, t) = 0 := by
    filter_upwards [hmodes, ae_integrable_slice hW] with s hs hint
    have hpair : ∀ (k : ℤ) (v : Vec 1),
        Integrable (fun t => inner ℝ (modeVec k v t) (W (s, t))) (volume.restrict (Ico (0 : ℝ) 1)) :=
      fun k v => Integrable.mono' (hint.norm.const_mul (‖v‖ + ‖Jv v‖))
        (((contDiff_modeVec k v).continuous.aestronglyMeasurable).inner hint.1)
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right (norm_modeVec_le k v t) (norm_nonneg _)))
    have hH : IntegrableOn (fun t => vecToC (W (s, t))) (Ico 0 1) :=
      vecToCL.integrable_comp hint
    have hF := ae_eq_zero_of_fourier_eq_zero _ hH fun k => by
      simp_rw [exp_mul_vecToC]
      rw [integral_add (hpair (-k) e₁).ofReal ((hpair (-k) e₂).ofReal.const_mul _),
        integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
      have h1 := (hs (-k)).1
      have h2 := (hs (-k)).2
      simp only [modeCoef] at h1 h2
      rw [h1, h2]
      simp
    filter_upwards [hF] with t ht
    exact eq_zero_of_vecToC_eq_zero ht
  -- back to the cylinder
  have hm : AEStronglyMeasurable W
      ((volume : Measure ℝ).prod (volume.restrict (Ico (0 : ℝ) 1))) := by
    rw [← tg_cyl_eq_prod]; exact hW.1
  have hmeas : MeasurableSet {x : ℝ × ℝ | hm.mk W x = 0} :=
    hm.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_const
  have hmk : ∀ᵐ x ∂((volume : Measure ℝ).prod (volume.restrict (Ico (0 : ℝ) 1))),
      hm.mk W x = 0 := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hmeas).2 ?_
    filter_upwards [hslice, Measure.ae_ae_of_ae_prod hm.ae_eq_mk] with s h1 h2
    filter_upwards [h1, h2] with t ht1 ht2
    show hm.mk W (s, t) = 0
    rw [← ht2]; exact ht1
  rw [tg_cyl_eq_prod]
  filter_upwards [hmk, hm.ae_eq_mk] with x h1 h2
  rw [h2, h1]; rfl

/-- Tg-Inj. -/
theorem crApply_slope_injective_proof (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ a b) :
    ∀ w ∈ W1p p 1, crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 → w = 0 := by
  intro w hw h0
  have h1 := fst_ae_eq_zero_of_kernel hp' ha hb hχ w hw h0
  have hA : crApply (fun x : ℝ × ℝ => (fun _ : ℝ => a • (1 : Mat 1)) x.2) w =ᵐ[cylMeasure] 0 := by
    filter_upwards [h0, h1] with x hx hx1
    simp only [crApply, Pi.zero_apply] at hx hx1 ⊢
    rw [hx1, map_zero, add_zero] at hx ⊢
    exact hx
  obtain ⟨hk, -⟩ := translationInvariant_bijective 1 p hp hp' (fun _ : ℝ => a • (1 : Mat 1))
    (isNondegenerate_const_smul_one 1 a ha).1 (isNondegenerate_const_smul_one 1 a ha).2
  have hmem : w ∈ crKernel p (fun x : ℝ × ℝ => (fun _ : ℝ => a • (1 : Mat 1)) x.2) :=
    Submodule.subset_span ⟨hw, hA⟩
  rw [hk] at hmem
  exact (Submodule.mem_bot ℝ).1 hmem

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (a b : ℝ) (ha : a ∈ Ioo 0 (2 * π)) (hb : b ∈ Ioo 0 (2 * π))
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχa : ∀ s ≤ -1, deriv χ s = a)
    (hχb : ∀ s ≥ 1, deriv χ s = b) :
    ∀ w ∈ W1p p 1, crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w =ᵐ[cylMeasure] 0 → w = 0 :=
  FiniteEnergyPlane.crApply_slope_injective_proof p hp hp' a b ha hb χ ⟨hχ, hχa, hχb⟩
