-- Prove2me | solution 1 for FiniteEnergyPlane.fredholm_index_zero_of_window
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T18:29:14.191602+00:00
-- url     : https://prove2.me/submissions/f62efaa7-996a-4413-bca5-a66a9f1f5753

import Definitions.Def_FiniteEnergyPlane_TubeFamily
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
import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
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
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_contDiffOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_contDiffOn_of_isWeakJHolomorphicOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
import Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_ConleyZehnder_czValue_existsUnique
import Theorems.Thm_CauchyRiemannIndex_index_formula
import Theorems.Thm_FiniteEnergyPlane_czIndex_eq_czIndexOfPath
import Theorems.Thm_FiniteEnergyPlane_exists_loopAlpha_czIndexOfPath_eq_of_symLoop
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_of_fundamentalSolution_apply_one
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_winding_of_antilinear
import Theorems.Thm_CauchyRiemannIndex_model_asymptotic_operator
import Theorems.Thm_CauchyRiemannIndex_isNondegenerate_pi_smul_one



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

/-!
# Q-L, layer L1: `W^{1,p}` triples give weak partials on the plane

For `w ∈ W1p p n` with a continuous periodic representative `g` of `w.1`, the map
`z ↦ g(Re z, Im z)` has weak partials `perF w.2.1`, `perF w.2.2` (the `t`-periodic extensions) on
the strip `stripU = {|Im z| < 1}` of `ℂ`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

/-- `ℂ → ℝ × ℝ`, `z ↦ (Re z, Im z)`. -/
def cplx (z : ℂ) : ℝ × ℝ := Complex.equivRealProdCLM z

/-- `ℝ × ℝ → ℂ`. -/
def toC (x : ℝ × ℝ) : ℂ := Complex.equivRealProdCLM.symm x

@[simp] lemma cplx_toC (x : ℝ × ℝ) : cplx (toC x) = x :=
  Complex.equivRealProdCLM.apply_symm_apply x

@[simp] lemma toC_cplx (z : ℂ) : toC (cplx z) = z :=
  Complex.equivRealProdCLM.symm_apply_apply z

@[simp] lemma cplx_apply (z : ℂ) : cplx z = (z.re, z.im) := by
  simp [cplx]

/-- The strip `|Im z| < 1`. -/
def stripU : Set ℂ := {z | |z.im| < 1}

lemma isOpen_stripU : IsOpen stripU :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The `t`-periodic extension of a function on the strip `ℝ × [0, 1)`. -/
def perF {E : Type*} (f : ℝ × ℝ → E) (x : ℝ × ℝ) : E := f (x.1, Int.fract x.2)

/-- Shift down by one in `t`. -/
def tdn : ℝ × ℝ := (0, -1)

lemma perF_of_mem {E : Type*} (f : ℝ × ℝ → E) {x : ℝ × ℝ} (hx : x ∈ (univ : Set ℝ) ×ˢ Ico 0 1) :
    perF f x = f x := by
  simp only [perF, Int.fract_eq_self.2 hx.2]

lemma perF_add_tdn {E : Type*} (f : ℝ × ℝ → E) (x : ℝ × ℝ) : perF f (x + tdn) = perF f x := by
  simp only [perF, tdn, Prod.fst_add, Prod.snd_add, add_zero, ← sub_eq_add_neg, Int.fract_sub_one]

lemma per_add_tdn {E : Type*} {f : ℝ × ℝ → E} (hf : ∀ s t : ℝ, f (s, t + 1) = f (s, t))
    (x : ℝ × ℝ) : f (x + tdn) = f x := by
  obtain ⟨s, t⟩ := x
  have := hf s (t - 1)
  simp only [sub_add_cancel] at this
  simp only [tdn, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg]
  exact this.symm

lemma fderiv_per {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E}
    (hf : ∀ s t : ℝ, f (s, t + 1) = f (s, t)) (s t : ℝ) :
    fderiv ℝ f (s, t + 1) = fderiv ℝ f (s, t) := by
  have e : f = fun x => f (x + ((0 : ℝ), (1 : ℝ))) := by
    funext x
    obtain ⟨a, b⟩ := x
    rw [Prod.mk_add_mk, add_zero, hf]
  conv_rhs => rw [e]
  rw [fderiv_comp_add_right]
  simp

lemma measurePreserving_tdn : MeasurePreserving (fun x : ℝ × ℝ => x + tdn) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) (-1))
  have e : Prod.map id (fun t : ℝ => t + -1) = fun x : ℝ × ℝ => x + tdn := by
    funext x; obtain ⟨a, b⟩ := x; simp [tdn, Prod.map]
  rw [e] at h
  exact h

lemma measurableEmbedding_tdn : MeasurableEmbedding (fun x : ℝ × ℝ => x + tdn) :=
  (MeasurableEquiv.addRight tdn).measurableEmbedding

lemma preimage_tdn_lower :
    (fun x : ℝ × ℝ => x + tdn) ⁻¹' ((univ : Set ℝ) ×ˢ Ico (-1) 0) = univ ×ˢ Ico 0 1 := by
  ext ⟨s, t⟩
  simp only [tdn, mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, true_and, mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Splitting `ℝ × [-1, 1)` into two period strips. -/
lemma integral_eq_cyl_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ × ℝ → E) (h1 : Integrable F cylMeasure)
    (h2 : Integrable (fun x => F (x + tdn)) cylMeasure)
    (h0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → F x = 0) :
    Integrable F ∧ ∫ x, F x = ∫ x, (F x + F (x + tdn)) ∂cylMeasure := by
  have hlowI : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico (-1) 0) := by
    rw [← (measurePreserving_tdn.integrableOn_comp_preimage measurableEmbedding_tdn),
      preimage_tdn_lower]
    exact h2
  have hupI : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico 0 1) := h1
  have hsplit : (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1 = univ ×ˢ Ico (-1) 0 ∪ univ ×ˢ Ico 0 1 := by
    rw [← prod_union, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
  have hI : Integrable F := by
    have hon : IntegrableOn F ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) := by
      rw [hsplit]; exact hlowI.union hupI
    refine (integrableOn_iff_integrable_of_support_subset
      (s := (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) ?_).1 hon
    intro x hx
    exact Set.mem_prod.2 ⟨mem_univ _, by_contra fun h => hx (h0 x h)⟩
  refine ⟨hI, ?_⟩
  have hA : ∫ x, F x = ∫ x in (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1, F x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)
      fun x hx => h0 x fun h => hx (Set.mem_prod.2 ⟨mem_univ _, h⟩)).symm
  have hdisj : Disjoint ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 0) (univ ×ˢ Ico 0 1) :=
    Set.disjoint_prod.2 (Or.inr (Ico_disjoint_Ico_same))
  have hlow : ∫ x in (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 0, F x =
      ∫ x in (univ : Set ℝ) ×ˢ Ico (0 : ℝ) 1, F (x + tdn) := by
    rw [← preimage_tdn_lower]
    exact (measurePreserving_tdn.setIntegral_preimage_emb measurableEmbedding_tdn F _).symm
  rw [hA, hsplit, setIntegral_union hdisj (MeasurableSet.univ.prod measurableSet_Ico) hlowI hupI,
    hlow]
  rw [show ∫ x, (F x + F (x + tdn)) ∂cylMeasure =
      (∫ x, F x ∂cylMeasure) + ∫ x, F (x + tdn) ∂cylMeasure from integral_add h1 h2, add_comm]
  rfl

/-! ### Test functions on the strip -/

section TestFn

variable (φ : ℂ → ℝ)

lemma exists_vanish_of_hasCompactSupport (hφc : HasCompactSupport φ) :
    ∃ R : ℝ, ∀ z : ℂ, R < |z.re| → φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun z hz => ?_⟩
  have hz' : z ∉ tsupport φ := by
    intro h
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    have := Complex.abs_re_le_norm z
    linarith
  refine ⟨image_eq_zero_of_notMem_tsupport hz', ?_⟩
  by_contra h
  exact hz' (support_fderiv_subset ℝ h)

lemma vanish_of_tsupport (hφU : tsupport φ ⊆ stripU) {z : ℂ} (hz : 1 ≤ |z.im|) :
    φ z = 0 ∧ fderiv ℝ φ z = 0 := by
  have hz' : z ∉ tsupport φ := fun h => absurd (hφU h) (by simp [stripU]; linarith)
  refine ⟨image_eq_zero_of_notMem_tsupport hz', ?_⟩
  by_contra h
  exact hz' (support_fderiv_subset ℝ h)

lemma not_mem_Ico_abs {t : ℝ} (ht : t ∉ Ico (-1 : ℝ) 1) : 1 ≤ |t| := by
  rw [mem_Ico, not_and_or, not_le, not_lt] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

end TestFn

/-- Products of a continuous function vanishing for large `|s|` with an `L^p` function are
integrable on the strip. -/
lemma integrable_smul_cyl {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : ℝ × ℝ → ℝ) (hf : Continuous f)
    (R : ℝ) (hR : ∀ s t, R < |s| → f (s, t) = 0) (h : ℝ × ℝ → Vec n)
    (hh : MemLp h p cylMeasure) : Integrable (fun x => f x • h x) cylMeasure := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  have hf' : MemLp f p.conjExponent cylMeasure := memLp_of_vanish f hf R hR
  have := hh.smul (p := p.conjExponent) (q := p) (r := 1) hf'
  exact memLp_one_iff_integrable.1 this

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L1b: the weak identity for `W^{1,p}` triples on the plane strip
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma integral_cplx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ × ℝ → E) :
    ∫ z : ℂ, F (cplx z) = ∫ x, F x :=
  Complex.volume_preserving_equiv_real_prod.integral_comp' F

lemma toC_re (x : ℝ × ℝ) : (toC x).re = x.1 := by simp [toC]

lemma toC_im (x : ℝ × ℝ) : (toC x).im = x.2 := by simp [toC]

lemma toC_add_tdn_re (x : ℝ × ℝ) : (toC (x + tdn)).re = x.1 := by simp [toC, tdn]

/-- Pairing with `f • e` is the inner product of the integral. -/
lemma integral_inner_smul (f : ℝ × ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hR : ∀ s t, R < |s| → f (s, t) = 0) (h : ℝ × ℝ → Vec n) (hh : MemLp h p cylMeasure)
    (e : Vec n) :
    ∫ x, inner ℝ (h x) (f x • e) ∂cylMeasure = inner ℝ (∫ x, f x • h x ∂cylMeasure) e := by
  rw [real_inner_comm, ← integral_inner (integrable_smul_cyl f hf R hR h hh) e]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm]

/-- Plane integral of `f • G` for a periodic `G` as a cylinder integral. -/
lemma integral_plane_eq_cyl (f : ℝ × ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hR : ∀ x : ℝ × ℝ, R < |x.1| → f x = 0)
    (h0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → f x = 0)
    (G : ℝ × ℝ → Vec n) (hG : ∀ x, G (x + tdn) = G x) (hGm : MemLp G p cylMeasure) :
    ∫ x, f x • G x = ∫ x, (f x + f (x + tdn)) • G x ∂cylMeasure := by
  have hf2 : Continuous fun x : ℝ × ℝ => f (x + tdn) := hf.comp (continuous_id.add continuous_const)
  have i1 := integrable_smul_cyl f hf R (fun s t h => hR (s, t) h) G hGm
  have i2 := integrable_smul_cyl (fun x => f (x + tdn)) hf2 R
    (fun s t h => hR _ (by simpa [tdn] using h)) G hGm
  obtain ⟨-, hI⟩ := integral_eq_cyl_add (fun x => f x • G x) i1
    (by simpa only [hG] using i2) (fun x hx => by simp [h0 x hx])
  rw [hI]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [hG, add_smul]

/-- The weak identity in direction `dir ∈ {1, i}`. -/
theorem weak_identity (dir : ℂ) (hdir : dir = 1 ∨ dir = Complex.I)
    (pd : (ℝ × ℝ → Vec n) → ℝ × ℝ → Vec n)
    (hpd : ∀ u : ℝ × ℝ → Vec n, ∀ x, fderiv ℝ u x (cplx dir) = pd u x)
    (sel : Triple n p →L[ℝ] LpCyl n p)
    (hsel : ∀ u : ℝ × ℝ → Vec n, IsTestSection u → ∀ v : Triple n p,
      (v.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (v.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (v.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u →
      (sel v : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] pd u)
    (w : Triple n p) (hw : w ∈ W1p p n) (g : ℝ × ℝ → Vec n) (hgc : Continuous g)
    (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (hwg : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ stripU) :
    ∫ z, fderiv ℝ φ z dir • g (cplx z) = -∫ z, φ z • perF (sel w) (cplx z) := by
  haveI : Fact (1 ≤ p.conjExponent) := ⟨le_self_add⟩
  -- the coefficient functions
  set D : ℝ × ℝ → ℝ := fun x => fderiv ℝ φ (toC x) dir with hDdef
  set φr : ℝ × ℝ → ℝ := fun x => φ (toC x) with hφrdef
  have hcC : Continuous toC := Complex.equivRealProdCLM.symm.continuous
  have hDc : Continuous D :=
    ((hφ.continuous_fderiv (by simp)).comp hcC).clm_apply continuous_const
  have hφrc : Continuous φr := hφ.continuous.comp hcC
  obtain ⟨R, hR⟩ := exists_vanish_of_hasCompactSupport φ hφc
  have hDR : ∀ x : ℝ × ℝ, R < |x.1| → D x = 0 := fun x hx => by
    simp only [hDdef, (hR (toC x) (by rwa [toC_re])).2, ContinuousLinearMap.zero_apply]
  have hφrR : ∀ x : ℝ × ℝ, R < |x.1| → φr x = 0 := fun x hx =>
    (hR (toC x) (by rwa [toC_re])).1
  have hD0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → D x = 0 := fun x hx => by
    simp only [hDdef, (vanish_of_tsupport φ hφU (by rw [toC_im]; exact not_mem_Ico_abs hx)).2,
      ContinuousLinearMap.zero_apply]
  have hφr0 : ∀ x : ℝ × ℝ, x.2 ∉ Ico (-1 : ℝ) 1 → φr x = 0 := fun x hx =>
    (vanish_of_tsupport φ hφU (by rw [toC_im]; exact not_mem_Ico_abs hx)).1
  set DΦ : ℝ × ℝ → ℝ := fun x => D x + D (x + tdn) with hDΦdef
  set Φ : ℝ × ℝ → ℝ := fun x => φr x + φr (x + tdn) with hΦdef
  have hsh : Continuous fun x : ℝ × ℝ => x + tdn := continuous_id.add continuous_const
  have hDΦc : Continuous DΦ := hDc.add (hDc.comp hsh)
  have hΦc : Continuous Φ := hφrc.add (hφrc.comp hsh)
  have hDΦR : ∀ s t, R < |s| → DΦ (s, t) = 0 := fun s t h => by
    simp only [hDΦdef, hDR (s, t) h, hDR ((s, t) + tdn) (by simpa [tdn] using h), add_zero]
  have hΦR : ∀ s t, R < |s| → Φ (s, t) = 0 := fun s t h => by
    simp only [hΦdef, hφrR (s, t) h, hφrR ((s, t) + tdn) (by simpa [tdn] using h), add_zero]
  -- plane integrals as cylinder integrals
  have hplaneD : ∀ G : ℝ × ℝ → Vec n, (∀ x, G (x + tdn) = G x) → MemLp G p cylMeasure →
      ∫ z, fderiv ℝ φ z dir • G (cplx z) = ∫ x, DΦ x • G x ∂cylMeasure := by
    intro G hG hGm
    rw [← integral_plane_eq_cyl D hDc R hDR hD0 G hG hGm, ← integral_cplx]
    simp only [hDdef, toC_cplx]
  have hplaneφ : ∀ G : ℝ × ℝ → Vec n, (∀ x, G (x + tdn) = G x) → MemLp G p cylMeasure →
      ∫ z, φ z • G (cplx z) = ∫ x, Φ x • G x ∂cylMeasure := by
    intro G hG hGm
    rw [← integral_plane_eq_cyl φr hφrc R hφrR hφr0 G hG hGm, ← integral_cplx]
    simp only [hφrdef, toC_cplx]
  -- the functional
  set P := ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := p.conjExponent)
  have hm1 : ∀ e : Vec n, MemLp (fun x => DΦ x • e) p.conjExponent cylMeasure := fun e =>
    memLp_of_vanish _ (hDΦc.smul continuous_const) R fun s t h => by simp [hDΦR s t h]
  have hm2 : ∀ e : Vec n, MemLp (fun x => Φ x • e) p.conjExponent cylMeasure := fun e =>
    memLp_of_vanish _ (hΦc.smul continuous_const) R fun s t h => by simp [hΦR s t h]
  let Λ : Vec n → Triple n p →L[ℝ] ℝ := fun e =>
    (P.flip ((hm1 e).toLp _)).comp (ContinuousLinearMap.fst ℝ _ _) + (P.flip ((hm2 e).toLp _)).comp sel
  have hΛ : ∀ e (v : Triple n p), Λ e v =
      inner ℝ (∫ x, DΦ x • v.1 x ∂cylMeasure + ∫ x, Φ x • sel v x ∂cylMeasure) e := by
    intro e v
    simp only [Λ, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_fst', P, ckaPairL_apply]
    rw [inner_add_left, ← integral_inner_smul DΦ hDΦc R hDΦR _ (Lp.memLp v.1) e,
      ← integral_inner_smul Φ hΦc R hΦR _ (Lp.memLp (sel v)) e]
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [(hm1 e).coeFn_toLp] with x hx
      rw [hx]
    · refine integral_congr_ae ?_
      filter_upwards [(hm2 e).coeFn_toLp] with x hx
      rw [hx]
  -- vanishing on test triples
  have htest : ∀ u : ℝ × ℝ → Vec n, ∀ hu : IsTestSection u, ∀ v ∈ testTriples n p,
      (v.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u →
      (v.2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialS u →
      (v.2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] partialT u → ∀ e, Λ e v = 0 := by
    intro u hu v _ h1 h2 h3 e
    have hs := hsel u hu v h1 h2 h3
    have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
    have hupd : ∀ x, pd u (x + tdn) = pd u x := by
      intro x
      rw [← hpd, ← hpd]
      obtain ⟨s, t⟩ := x
      have := fderiv_per hu.2.1 s (t - 1)
      simp only [sub_add_cancel] at this
      simp only [tdn, Prod.mk_add_mk, add_zero, ← sub_eq_add_neg, this]
    have hupm : MemLp (pd u) p cylMeasure := (Lp.memLp (sel v)).ae_eq hs
    have hum : MemLp u p cylMeasure := hu.memLp
    have hu_per : ∀ x, u (x + tdn) = u x := per_add_tdn hu.2.1
    rw [hΛ]
    have e1 : ∫ x, DΦ x • v.1 x ∂cylMeasure = ∫ z, fderiv ℝ φ z dir • u (cplx z) := by
      rw [hplaneD u hu_per hum]
      refine integral_congr_ae ?_
      filter_upwards [h1] with x hx
      rw [hx]
    have e2 : ∫ x, Φ x • sel v x ∂cylMeasure = ∫ z, φ z • pd u (cplx z) := by
      rw [hplaneφ (pd u) hupd hupm]
      refine integral_congr_ae ?_
      filter_upwards [hs] with x hx
      rw [hx]
    -- the plane identity for the smooth map `u ∘ cplx`
    have hcomp : ContDiffOn ℝ 1 (fun z => u (cplx z)) univ :=
      ((hu.1.of_le (by simp)).comp Complex.equivRealProdCLM.contDiff).contDiffOn
    have hW := JHolomorphic.HasWeakPartialsOn.of_contDiffOn isOpen_univ hcomp φ hφ hφc
      (subset_univ _)
    have hfd : ∀ z (a : ℂ), fderiv ℝ (fun z => u (cplx z)) z a = fderiv ℝ u (cplx z) (cplx a) := by
      intro z a
      have : (fun z => u (cplx z)) = u ∘ Complex.equivRealProdCLM := rfl
      rw [this, ContinuousLinearEquiv.comp_right_fderiv]
      rfl
    have e3 : ∫ z, fderiv ℝ φ z dir • u (cplx z) = -∫ z, φ z • pd u (cplx z) := by
      rcases hdir with rfl | rfl
      · rw [hW.1]
        simp only [hfd, hpd]
      · rw [hW.2]
        simp only [hfd, hpd]
    rw [e1, e2, e3, neg_add_cancel, inner_zero_left]
  -- vanishing on `W^{1,p}`
  have hall : ∀ e, Λ e w = 0 := fun e =>
    ckp_W1p_le_ker (Λ e) (fun u hu v hv h1 h2 h3 => htest u hu v hv h1 h2 h3 e) w hw
  have hI : ∫ x, DΦ x • w.1 x ∂cylMeasure + ∫ x, Φ x • sel w x ∂cylMeasure = 0 := by
    have := hall (∫ x, DΦ x • w.1 x ∂cylMeasure + ∫ x, Φ x • sel w x ∂cylMeasure)
    rw [hΛ] at this
    exact inner_self_eq_zero.1 this
  -- back to the plane
  have hgm : MemLp g p cylMeasure := (Lp.memLp w.1).ae_eq hwg
  have hpm : MemLp (perF (sel w : ℝ × ℝ → Vec n)) p cylMeasure := by
    refine (Lp.memLp (sel w)).ae_eq ?_
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    rw [perF_of_mem _ hx]
  have e1 : ∫ z, fderiv ℝ φ z dir • g (cplx z) = ∫ x, DΦ x • w.1 x ∂cylMeasure := by
    rw [hplaneD g (per_add_tdn hgper) hgm]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
  have e2 : ∫ z, φ z • perF (sel w : ℝ × ℝ → Vec n) (cplx z) = ∫ x, Φ x • sel w x ∂cylMeasure := by
    rw [hplaneφ _ (perF_add_tdn _) hpm]
    refine integral_congr_ae ?_
    unfold cylMeasure
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx
    rw [perF_of_mem _ hx]
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left hI

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L1c: `W^{1,p}` triples as `W^{1,p}_loc` maps on the plane strip
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Shift up by one in `t`. -/
def tup : ℝ × ℝ := (0, 1)

lemma measurePreserving_tup : MeasurePreserving (fun x : ℝ × ℝ => x + tup) volume volume := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (measurePreserving_add_right (volume : Measure ℝ) 1)
  have e : Prod.map id (fun t : ℝ => t + 1) = fun x : ℝ × ℝ => x + tup := by
    funext x; obtain ⟨a, b⟩ := x; simp [tup, Prod.map]
  rw [e] at h
  exact h

/-- The lower strip `ℝ × [-1, 0)`. -/
abbrev lowS : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Ico (-1) 0

/-- The period strip `ℝ × [0, 1)`. -/
abbrev upS : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ Ico 0 1

lemma preimage_tup_upS : (fun x : ℝ × ℝ => x + tup) ⁻¹' upS = lowS := by
  ext ⟨s, t⟩
  simp only [tup, mem_preimage, Prod.mk_add_mk, add_zero, mem_prod, mem_univ, true_and, mem_Ico]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

lemma measurePreserving_tup_restrict :
    MeasurePreserving (fun x : ℝ × ℝ => x + tup) (volume.restrict lowS) cylMeasure := by
  have := measurePreserving_tup.restrict_preimage (MeasurableSet.univ.prod measurableSet_Ico)
    (s := upS)
  rwa [preimage_tup_upS] at this

lemma perF_of_mem_lowS {E : Type*} (f : ℝ × ℝ → E) {x : ℝ × ℝ} (hx : x ∈ lowS) :
    perF f x = f (x + tup) := by
  obtain ⟨s, t⟩ := x
  have ht := hx.2
  simp only [perF, tup, Prod.mk_add_mk, add_zero]
  congr 2
  rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩]

lemma lowS_union_upS : lowS ∪ upS = (univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1 := by
  rw [← prod_union, Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]

/-- Transport of an a.e. statement on the period strip to `ℝ × [-1, 1)`. -/
lemma ae_of_cyl (P Q : ℝ × ℝ → Prop) (hP : ∀ᵐ x ∂cylMeasure, P x)
    (hup : ∀ x ∈ upS, P x → Q x) (hlow : ∀ x ∈ lowS, P (x + tup) → Q x) :
    ∀ᵐ x ∂(volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)), Q x := by
  rw [← lowS_union_upS, ae_restrict_union_iff]
  constructor
  · have h := measurePreserving_tup_restrict.quasiMeasurePreserving.ae hP
    filter_upwards [h, ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx hm
    exact hlow x hm hx
  · have hP' : ∀ᵐ x ∂(volume.restrict upS), P x := hP
    filter_upwards [hP', ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)] with x hx hm
    exact hup x hm hx

/-- `perF f` is `L^p` on `ℝ × [-1, 1)`. -/
lemma memLp_perF (f : LpCyl n p) :
    MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)) := by
  have hmL : MeasurableSet lowS := MeasurableSet.univ.prod measurableSet_Ico
  have hmU : MeasurableSet upS := MeasurableSet.univ.prod measurableSet_Ico
  have hU : MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict upS) := by
    refine (Lp.memLp f).ae_eq ?_
    filter_upwards [ae_restrict_mem hmU] with x hx
    rw [perF_of_mem _ hx]
  have hL : MemLp (perF (f : ℝ × ℝ → Vec n)) p (volume.restrict lowS) := by
    refine ((Lp.memLp f).comp_measurePreserving measurePreserving_tup_restrict).ae_eq ?_
    filter_upwards [ae_restrict_mem hmL] with x hx
    rw [perF_of_mem_lowS _ hx]
    rfl
  rw [← lowS_union_upS, ← memLp_indicator_iff_restrict (hmL.union hmU),
    indicator_union_of_disjoint (Set.disjoint_prod.2 (Or.inr Ico_disjoint_Ico_same))]
  exact ((memLp_indicator_iff_restrict hmL).2 hL).add ((memLp_indicator_iff_restrict hmU).2 hU)

lemma measurePreserving_cplx : MeasurePreserving cplx volume volume :=
  Complex.volume_preserving_equiv_real_prod

/-- `L^p` on `ℝ × [-1, 1)` gives `L^p` on compact subsets of the plane strip. -/
lemma memLp_comp_cplx_of_compact {E : Type*} [NormedAddCommGroup E] {F : ℝ × ℝ → E}
    (hF : MemLp F p (volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)))
    (K : Set ℂ) (hK : K ⊆ stripU) :
    MemLp (fun z => F (cplx z)) p (volume.restrict K) := by
  have hm : MeasurableSet ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have h := hF.comp_measurePreserving (measurePreserving_cplx.restrict_preimage hm)
  refine h.mono_measure (Measure.restrict_mono ?_ le_rfl)
  intro z hz
  have := hK hz
  simp only [stripU, mem_setOf_eq, abs_lt] at this
  simp [cplx_apply, this.1.le, this.2]

/-- The a.e. version of an a.e. statement on the plane strip. -/
lemma ae_stripU_of (Q : ℂ → Prop)
    (hQ : ∀ᵐ x ∂(volume.restrict ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1)), Q (toC x)) :
    ∀ᵐ z ∂(volume.restrict stripU), Q z := by
  have hm : MeasurableSet ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) :=
    MeasurableSet.univ.prod measurableSet_Ico
  have h := (measurePreserving_cplx.restrict_preimage hm).quasiMeasurePreserving.ae hQ
  have hsub : stripU ⊆ cplx ⁻¹' ((univ : Set ℝ) ×ˢ Ico (-1 : ℝ) 1) := by
    intro z hz
    simp only [stripU, mem_setOf_eq, abs_lt] at hz
    simp [cplx_apply, hz.1.le, hz.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub h] with z hz
  simpa only [toC_cplx] using hz

/-- L1. A `W^{1,p}` triple with a continuous periodic representative is a `W^{1,p}_loc` map on
the plane strip, and the equation `D_M w = 0` holds a.e. there. -/
theorem isWeak_of_mem_W1p (w : Triple n p) (hw : w ∈ W1p p n) (g : ℝ × ℝ → Vec n)
    (hgc : Continuous g) (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (hwg : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) :
    JHolomorphic.HasWeakPartialsOn stripU (fun z => g (cplx z))
        (fun z => perF (w.2.1 : ℝ × ℝ → Vec n) (cplx z))
        (fun z => perF (w.2.2 : ℝ × ℝ → Vec n) (cplx z)) ∧
      ∀ K ⊆ stripU, MemLp (fun z => perF (w.2.1 : ℝ × ℝ → Vec n) (cplx z)) p (volume.restrict K) ∧
        MemLp (fun z => perF (w.2.2 : ℝ × ℝ → Vec n) (cplx z)) p (volume.restrict K) := by
  refine ⟨fun φ hφ hφc hφU => ⟨?_, ?_⟩, fun K hK =>
    ⟨memLp_comp_cplx_of_compact (memLp_perF _) K hK,
      memLp_comp_cplx_of_compact (memLp_perF _) K hK⟩⟩
  · exact weak_identity 1 (Or.inl rfl) partialS
      (fun u x => by simp [cplx_apply, partialS])
      ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
      (fun u _ v _ h2 _ => h2) w hw g hgc hgper hwg φ hφ hφc hφU
  · exact weak_identity Complex.I (Or.inr rfl) partialT
      (fun u x => by simp [cplx_apply, partialT])
      ((ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _))
      (fun u _ v _ _ h3 => h3) w hw g hgc hgper hwg φ hφ hφc hφU

/-- The equation `D_M w = 0` a.e. on the plane strip. -/
theorem ae_eq_zero_stripU (M : ℝ × ℝ → Mat n) (hMper : ∀ s t : ℝ, M (s, t + 1) = M (s, t))
    (w : Triple n p) (g : ℝ × ℝ → Vec n) (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (hwg : (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) (h0 : crApply M w =ᵐ[cylMeasure] 0) :
    ∀ᵐ z ∂(volume.restrict stripU),
      perF (w.2.1 : ℝ × ℝ → Vec n) (cplx z) +
        Matrix.toEuclideanLin (J₀ n) (perF (w.2.2 : ℝ × ℝ → Vec n) (cplx z)) +
        Matrix.toEuclideanLin (M (cplx z)) (g (cplx z)) = 0 := by
  refine ae_stripU_of _ ?_
  simp only [cplx_toC]
  have hP : ∀ᵐ x ∂cylMeasure, (w.2.1 : ℝ × ℝ → Vec n) x +
      Matrix.toEuclideanLin (J₀ n) ((w.2.2 : ℝ × ℝ → Vec n) x) +
      Matrix.toEuclideanLin (M x) (g x) = 0 := by
    filter_upwards [h0, hwg] with x hx hx'
    simpa [crApply, hx'] using hx
  refine ae_of_cyl _ _ hP (fun x hx h => ?_) (fun x hx h => ?_)
  · rw [perF_of_mem _ hx, perF_of_mem _ hx]; exact h
  · rw [perF_of_mem_lowS _ hx, perF_of_mem_lowS _ hx]
    have hM : M (x + tup) = M x := by
      obtain ⟨s, t⟩ := x; simp [tup, hMper]
    have hg : g (x + tup) = g x := by
      obtain ⟨s, t⟩ := x; simp [tup, hgper]
    rw [hM, hg] at h
    exact h

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L2: regularity of weak solutions of `∂ₛu + J₀ ∂ₜu + m(z, u) = 0`

Graph trick: `z ↦ (z, u z)` is weakly `J`-holomorphic for the smooth almost complex structure
`J(z, y)(a, b) = (i a, J₀ b + Re a · J₀ m(z, y) + Im a · m(z, y))` on `ℂ × F`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Set JHolomorphic
open scoped ContDiff ENNReal

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The graph almost complex structure. -/
def graphJ (J₀F : F →L[ℝ] F) (m : ℂ → F → F) (x : ℂ × F) : (ℂ × F) →L[ℝ] (ℂ × F) :=
  ((Complex.I • ContinuousLinearMap.id ℝ ℂ).comp (ContinuousLinearMap.fst ℝ ℂ F)).prod
    (J₀F.comp (ContinuousLinearMap.snd ℝ ℂ F) +
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ F)).smulRight (J₀F (m x.1 x.2)) +
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ F)).smulRight (m x.1 x.2))

lemma graphJ_apply (J₀F : F →L[ℝ] F) (m : ℂ → F → F) (x : ℂ × F) (v : ℂ × F) :
    graphJ J₀F m x v = (Complex.I * v.1,
      J₀F v.2 + v.1.re • J₀F (m x.1 x.2) + v.1.im • m x.1 x.2) := by
  simp [graphJ]

lemma isAlmostComplexOn_graphJ (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2)) :
    IsAlmostComplexOn (graphJ J₀F m) univ := by
  refine ⟨isOpen_univ, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    rw [contDiff_clm_apply_iff]
    intro v
    simp only [graphJ_apply]
    exact contDiff_const.prodMk
      ((contDiff_const.add ((J₀F.contDiff.comp hm).const_smul _)).add (hm.const_smul _))
  · intro x _
    refine ContinuousLinearMap.ext fun v => ?_
    rw [ContinuousLinearMap.comp_apply, graphJ_apply, graphJ_apply]
    refine Prod.ext ?_ ?_
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.fst_neg]
      rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
    · simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg,
        map_add, map_smul, hJ, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        zero_mul, one_mul, zero_sub, add_zero, smul_neg, neg_smul]
      abel

lemma memLp_pair {r : ℝ≥0∞} {μ : Measure ℂ} {f : ℂ → ℂ} {g : ℂ → F} (hf : MemLp f r μ)
    (hg : MemLp g r μ) : MemLp (fun z => (f z, g z)) r μ := by
  have h := ((ContinuousLinearMap.inl ℝ ℂ F).comp_memLp' hf).add
    ((ContinuousLinearMap.inr ℝ ℂ F).comp_memLp' hg)
  have e : (fun z => (f z, g z)) =
      (⇑(ContinuousLinearMap.inl ℝ ℂ F) ∘ f) + (⇑(ContinuousLinearMap.inr ℝ ℂ F) ∘ g) := by
    funext z; simp
  rw [e]; exact h

/-- L2. Weak solutions of a smooth first-order equation `∂ₛu + J₀ ∂ₜu + m(z, u) = 0` with a
complex structure `J₀` on the values are smooth. -/
theorem contDiffOn_of_weak_eq (J₀F : F →L[ℝ] F) (hJ : ∀ y, J₀F (J₀F y) = -y)
    (m : ℂ → F → F) (hm : ContDiff ℝ ∞ (fun x : ℂ × F => m x.1 x.2))
    (q : ℝ) (hq : 2 < q) (U : Set ℂ) (hU : IsOpen U) (u us ut : ℂ → F)
    (hu : ContinuousOn u U) (hw : HasWeakPartialsOn U u us ut)
    (hLp : ∀ K ⊆ U, IsCompact K →
      MemLp us (ENNReal.ofReal q) (volume.restrict K) ∧ MemLp ut (ENNReal.ofReal q) (volume.restrict K))
    (heq : ∀ᵐ z ∂(volume.restrict U), us z + J₀F (ut z) + m z (u z) = 0) :
    ContDiffOn ℝ ∞ u U := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hid0 := HasWeakPartialsOn.of_contDiffOn hU (contDiff_id (𝕜 := ℝ) (E := ℂ)).contDiffOn
  have hid : HasWeakPartialsOn U (fun z : ℂ => z) (fun _ => (1 : ℂ)) (fun _ => Complex.I) := by
    have h := hid0
    simp at h
    exact h
  have hint : ∀ K ⊆ U, IsCompact K →
      IntegrableOn (fun z : ℂ => z) K ∧ IntegrableOn (fun _ : ℂ => (1 : ℂ)) K ∧
        IntegrableOn (fun _ : ℂ => Complex.I) K ∧
        IntegrableOn u K ∧ IntegrableOn us K ∧ IntegrableOn ut K := by
    intro K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact ⟨continuousOn_id.integrableOn_compact hK, continuousOn_const.integrableOn_compact hK,
      continuousOn_const.integrableOn_compact hK, (hu.mono hKU).integrableOn_compact hK,
      ((hLp K hKU hK).1).integrable hq1, ((hLp K hKU hK).2).integrable hq1⟩
  have hG := hid.prodMk hw hint
  have hweak : IsWeakJHolomorphicOn q (graphJ J₀F m) univ U (fun z => (z, u z)) := by
    refine ⟨continuousOn_id.prodMk hu, fun _ _ => mem_univ _, _, _, hG,
      fun K hKU hK => ⟨?_, ?_, ?_⟩, ?_⟩
    · exact memLp_of_continuousOn_compact hK ((continuousOn_id.prodMk hu).mono hKU)
    · exact memLp_pair (memLp_of_continuousOn_compact hK continuousOn_const) (hLp K hKU hK).1
    · exact memLp_pair (memLp_of_continuousOn_compact hK continuousOn_const) (hLp K hKU hK).2
    · filter_upwards [heq] with z hz
      rw [graphJ_apply]
      refine Prod.ext ?_ ?_
      · simp [Complex.I_mul_I]
      · simp only [Prod.snd_add, Prod.snd_zero, Complex.I_re, Complex.I_im, zero_smul, add_zero,
          one_smul]
        rw [← add_assoc]
        exact hz
  have hsm := contDiffOn_of_isWeakJHolomorphicOn q hq (graphJ J₀F m) univ
    (isAlmostComplexOn_graphJ J₀F hJ m hm) U hU _ hweak
  exact contDiff_snd.comp_contDiffOn hsm

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L3: kernel elements of `D_M` on `W^{1,p}` are smooth (L-K)
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal

noncomputable section

lemma fderiv_comp_cplx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u : ℝ × ℝ → E)
    (z a : ℂ) : fderiv ℝ (fun z => u (cplx z)) z a = fderiv ℝ u (cplx z) (cplx a) := by
  have : (fun z => u (cplx z)) = u ∘ Complex.equivRealProdCLM := rfl
  rw [this, ContinuousLinearEquiv.comp_right_fderiv]
  rfl

lemma measurePreserving_toC : MeasurePreserving toC volume volume :=
  Complex.volume_preserving_equiv_real_prod.symm

open scoped Matrix.Norms.Elementwise in
lemma contDiff_matCLM_comp {n : ℕ} (M : ℝ × ℝ → Mat n)
    (hM : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => M x i j)) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => matCLM n (M x)) := by
  have hMs : ContDiff ℝ ∞ M := contDiff_pi.2 fun i => contDiff_pi.2 fun j => hM i j
  exact (LinearMap.toContinuousLinearMap (matCLM n)).contDiff.comp hMs

lemma per_int {E : Type*} {g : ℝ × ℝ → E} (hg : ∀ s t : ℝ, g (s, t + 1) = g (s, t))
    (x : ℝ × ℝ) (k : ℤ) : g (x - ((0 : ℝ), (k : ℝ))) = g x := by
  obtain ⟨s, t⟩ := x
  have hp : Function.Periodic (fun t => g (s, t)) 1 := fun t => hg s t
  have := (hp.int_mul k) (t - k)
  simp only [mul_one, sub_add_cancel] at this
  simp only [Prod.mk_sub_mk, sub_zero]
  exact this.symm

/-- L-K. -/
theorem exists_smooth_of_crApply_eq_zero_proof (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p)
    (hp' : p ≠ ⊤) (M : ℝ × ℝ → Mat 1) (hM : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => M x i j))
    (hMper : ∀ s t : ℝ, M (s, t + 1) = M (s, t))
    (w : Triple 1 p) (hw : w ∈ W1p p 1) (h0 : crApply M w =ᵐ[cylMeasure] 0) :
    ∃ g : ℝ × ℝ → Vec 1, ContDiff ℝ ∞ g ∧ (∀ s t : ℝ, g (s, t + 1) = g (s, t)) ∧
      (w.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g ∧ (∀ x, crOp M g x = 0) ∧
      MemLp (partialS g) p cylMeasure ∧ MemLp (partialT g) p cylMeasure := by
  obtain ⟨C, hC⟩ := exists_continuous_representative_of_mem_W1p p hp hp' 1
  obtain ⟨g, hgc, hgper, hwg⟩ := (hC w hw).1
  obtain ⟨hW, hLpK⟩ := isWeak_of_mem_W1p w hw g hgc hgper hwg
  have hae := ae_eq_zero_stripU M hMper w g hgper hwg h0
  have hq : 2 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp').2 hp
    simpa using this
  have hpq : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp'
  have hcplx : Continuous cplx := Complex.equivRealProdCLM.continuous
  have hJ : ∀ y : Vec 1, matCLM 1 (J₀ 1) (matCLM 1 (J₀ 1) y) = -y := by
    intro y
    have hsq : J₀ 1 * J₀ 1 = -1 := Matrix.J_squared _ _
    rw [matCLM_apply, matCLM_apply, show Matrix.toEuclideanLin (J₀ 1)
      (Matrix.toEuclideanLin (J₀ 1) y) = Matrix.toEuclideanLin (J₀ 1 * J₀ 1) y by
        rw [Matrix.toLpLin_mul]; rfl, hsq]
    simp
  have hm : ContDiff ℝ ∞ (fun x : ℂ × Vec 1 => matCLM 1 (M (cplx x.1)) x.2) :=
    (((contDiff_matCLM_comp M hM).comp Complex.equivRealProdCLM.contDiff).comp
      contDiff_fst).clm_apply contDiff_snd
  -- smooth on the plane strip
  have hsmU : ContDiffOn ℝ ∞ (fun z => g (cplx z)) stripU := by
    refine contDiffOn_of_weak_eq (matCLM 1 (J₀ 1)) hJ (fun z y => matCLM 1 (M (cplx z)) y) hm
      p.toReal hq stripU isOpen_stripU _ _ _ (hgc.comp hcplx).continuousOn hW
      (fun K hK _ => by rw [hpq]; exact hLpK K hK) ?_
    filter_upwards [hae] with z hz
    simpa only [matCLM_apply] using hz
  -- smooth on `ℝ × ℝ`
  have hsm : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    set k : ℤ := round x.2
    have e : g = (fun z => g (cplx z)) ∘ toC ∘ fun y => y - ((0 : ℝ), (k : ℝ)) := by
      funext y; simp only [Function.comp_apply, cplx_toC, per_int hgper]
    have hin : toC (x - ((0 : ℝ), (k : ℝ))) ∈ stripU := by
      simp only [stripU, mem_setOf_eq, toC_im, Prod.snd_sub]
      have := abs_sub_round x.2
      linarith
    rw [e]
    refine ContDiffAt.comp _ ((hsmU _ hin).contDiffAt (isOpen_stripU.mem_nhds hin)) ?_
    exact (Complex.equivRealProdCLM.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt
  -- the weak partials are the classical ones
  have hsmU1 : ContDiffOn ℝ 1 (fun z => g (cplx z)) stripU :=
    ((hsm.comp Complex.equivRealProdCLM.contDiff).of_le (by simp)).contDiffOn
  have hW' := JHolomorphic.HasWeakPartialsOn.of_contDiffOn isOpen_stripU hsmU1
  have hcd : Continuous (fderiv ℝ g) := hsm.continuous_fderiv (by simp)
  have hpq1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hint : ∀ K ⊆ stripU, IsCompact K →
      IntegrableOn (fun z => perF (w.2.1 : ℝ × ℝ → Vec 1) (cplx z)) K ∧
      IntegrableOn (fun z => perF (w.2.2 : ℝ × ℝ → Vec 1) (cplx z)) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun z => g (cplx z)) z 1) K ∧
      IntegrableOn (fun z => fderiv ℝ (fun z => g (cplx z)) z Complex.I) K := by
    intro K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    refine ⟨(hLpK K hKU).1.integrable hpq1, (hLpK K hKU).2.integrable hpq1, ?_, ?_⟩
    · simp only [fderiv_comp_cplx]
      exact ((hcd.comp hcplx).clm_apply continuous_const).continuousOn.integrableOn_compact hK
    · simp only [fderiv_comp_cplx]
      exact ((hcd.comp hcplx).clm_apply continuous_const).continuousOn.integrableOn_compact hK
  have heqU := JHolomorphic.HasWeakPartialsOn.ae_eq isOpen_stripU hW hW' hint
  -- pull back to the period strip
  have hsub : upS ⊆ toC ⁻¹' stripU := by
    intro x hx
    simp only [mem_preimage, stripU, mem_setOf_eq, toC_im]
    rw [abs_lt]; exact ⟨by linarith [hx.2.1], hx.2.2⟩
  have hpull : ∀ᵐ x ∂cylMeasure, (w.2.1 : ℝ × ℝ → Vec 1) x = partialS g x ∧
      (w.2.2 : ℝ × ℝ → Vec 1) x = partialT g x := by
    have h1 := (measurePreserving_toC.restrict_preimage isOpen_stripU.measurableSet).quasiMeasurePreserving.ae heqU
    have h2 : ∀ᵐ x ∂(volume.restrict upS), _ := ae_restrict_of_ae_restrict_of_subset hsub h1
    have h3 : ∀ᵐ x ∂cylMeasure, x ∈ upS := ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ico)
    filter_upwards [h2, h3] with x hx hxm
    simp only [cplx_toC, fderiv_comp_cplx, perF_of_mem _ hxm] at hx
    refine ⟨hx.1.trans ?_, hx.2.trans ?_⟩
    · simp [partialS, cplx_apply]
    · simp [partialT, cplx_apply]
  -- the classical equation
  have hcrc : Continuous (crOp M g) := by
    have hMc : Continuous fun x => matCLM 1 (M x) := (contDiff_matCLM_comp M hM).continuous
    exact ((hcd.clm_apply continuous_const).add
      ((matCLM 1 (J₀ 1)).continuous.comp (hcd.clm_apply continuous_const))).add
      (hMc.clm_apply hgc)
  have hcrp : ∀ s t : ℝ, crOp M g (s, t + 1) = crOp M g (s, t) := by
    intro s t
    simp only [crOp, partialS, partialT, fderiv_per hgper, hgper, hMper]
  have hcr0 : crOp M g = 0 := by
    refine eq_of_continuous_periodic_ae_eq hcrc continuous_const hcrp (fun _ _ => rfl) ?_
    filter_upwards [h0, hpull, hwg] with x hx hxp hxg
    simp only [crApply, Pi.zero_apply, hxp.1, hxp.2, hxg] at hx
    exact hx
  refine ⟨g, hsm, hgper, hwg, fun x => congrFun hcr0 x, ?_, ?_⟩
  · exact (Lp.memLp w.2.1).ae_eq (hpull.mono fun x hx => hx.1)
  · exact (Lp.memLp w.2.2).ae_eq (hpull.mono fun x hx => hx.2)

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L4: the plane function of a cylinder solution

For a smooth `t`-periodic `v`, `pf v z = vecToC (v (s, t))` at `z = cylInf s t` (and `0` at `z = 0`).
It is smooth on `ℂ \ {0}`, and if `∂ₛv + J₀ ∂ₜv + S v = 0` with `IsPlaneCoeff S` (coefficient `A`),
then `∂ₓζ + i ∂ᵧζ = -2 A(z) ζ` on `ℂ \ {0}`.
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### `vecToC` -/

/-- `vecToC` as a continuous linear map. -/
def vC : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

lemma vC_apply (a : Vec 1) : vC a = vecToC a := rfl

lemma vecToC_J₀ (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type]

lemma norm_vecToC_le (a : Vec 1) : ‖vecToC a‖ ≤ ‖a‖ := by
  have h1 : ‖vecToC a‖ ^ 2 = a (Sum.inl 0) ^ 2 + a (Sum.inr 0) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [vecToC]; ring
  have h2 : ‖a‖ ^ 2 = a (Sum.inl 0) ^ 2 + a (Sum.inr 0) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Fintype.sum_sum_type]
  exact le_of_eq (by nlinarith [norm_nonneg (vecToC a), norm_nonneg a])

lemma norm_vC_le : ‖vC‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [one_mul, vC_apply]; exact norm_vecToC_le a

/-! ### `cylInf` -/

lemma cylInf_eq_exp (s t : ℝ) :
    cylInf s t = Complex.exp (((2 * π : ℝ) : ℂ) * ((s : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold cylInf ccwLoop
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast; ring

lemma cylInf_ne_zero (s t : ℝ) : cylInf s t ≠ 0 := by
  rw [cylInf_eq_exp]; exact Complex.exp_ne_zero _

lemma norm_cylInf (s t : ℝ) : ‖cylInf s t‖ = Real.exp (2 * π * s) := by
  unfold cylInf ccwLoop
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

lemma cylInf_log_arg {z : ℂ} (hz : z ≠ 0) :
    cylInf (Real.log ‖z‖ / (2 * π)) (Complex.arg z / (2 * π)) = z := by
  unfold cylInf ccwLoop
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hπ, Real.exp_log (norm_pos_iff.2 hz), mul_div_cancel₀ _ hπ]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma arg_cylInf (s t : ℝ) : ∃ k : ℤ, Complex.arg (cylInf s t) / (2 * π) = t - k := by
  unfold cylInf ccwLoop
  rw [Complex.arg_real_mul _ (Real.exp_pos _), Complex.arg_exp_mul_I]
  refine ⟨toIocDiv Real.two_pi_pos (-π) (2 * π * t), ?_⟩
  rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]
  field_simp

/-! ### The log chart (copy of `JWQ_N5`, renamed) -/

/-- `log(1 + ζ) / (2π)`. -/
def lchart (ζ : ℂ) : ℂ := Complex.log (1 + ζ) * (((2 * π : ℝ) : ℂ))⁻¹

lemma one_add_mem_slitPlane' {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 1 + ζ ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have := Complex.abs_re_le_norm ζ
  rw [Complex.add_re, Complex.one_re]
  linarith [neg_abs_le ζ.re]

lemma lchart_contDiffAt {ζ : ℂ} (hζ : ‖ζ‖ < 1) : ContDiffAt ℝ ∞ lchart ζ := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (1 + ζ) :=
    (Complex.contDiffAt_log (one_add_mem_slitPlane' hζ)).restrict_scalars ℝ
  exact (hlog.comp ζ (contDiffAt_const.add contDiffAt_id)).mul contDiffAt_const

lemma lchart_contDiffOn : ContDiffOn ℝ ∞ lchart (ball (0 : ℂ) 1) := fun ζ hζ =>
  (lchart_contDiffAt (mem_ball_zero_iff.1 hζ)).contDiffWithinAt

/-- `cylInf s t (1 + ζ)` in log coordinates. -/
lemma cylInf_mul_one_add (s t : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ < 1) :
    cylInf s t * (1 + ζ) = cylInf (s + (lchart ζ).re) (t + (lchart ζ).im) := by
  have hne : 1 + ζ ≠ 0 := Complex.slitPlane_ne_zero (one_add_mem_slitPlane' hζ)
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have hre : 2 * π * (lchart ζ).re = (Complex.log (1 + ζ)).re := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    field_simp
  have him : 2 * π * (lchart ζ).im = (Complex.log (1 + ζ)).im := by
    simp only [lchart, ← Complex.ofReal_inv, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add]
    field_simp
  unfold cylInf ccwLoop
  rw [← Complex.exp_log hne]
  simp only [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, zero_mul]
    push_cast
    linarith [hre]
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_mul, zero_add]
    push_cast
    linarith [him]

/-! ### The plane function -/

/-- The plane function of `v`. -/
def pf (v : ℝ × ℝ → Vec 1) (z : ℂ) : ℂ :=
  if z = 0 then 0 else vecToC (v (Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π)))

variable {v : ℝ × ℝ → Vec 1}

lemma pf_zero : pf v 0 = 0 := by simp [pf]

lemma pf_cylInf (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t)) (s t : ℝ) :
    pf v (cylInf s t) = vecToC (v (s, t)) := by
  rw [pf, if_neg (cylInf_ne_zero s t), norm_cylInf, Real.log_exp,
    mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0)]
  obtain ⟨k, hk⟩ := arg_cylInf s t
  rw [hk]
  have := per_int hvper (s, t) k
  simpa using congrArg vecToC this

/-- `pf v` near `z₀ = cylInf s₀ t₀` in log coordinates. -/
lemma pf_local (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t)) (s₀ t₀ : ℝ) {z : ℂ}
    (hz : z ∈ ball (cylInf s₀ t₀) ‖cylInf s₀ t₀‖) :
    pf v z = vecToC (v (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im)) := by
  have h0 := cylInf_ne_zero s₀ t₀
  have hlt : ‖z / cylInf s₀ t₀ - 1‖ < 1 := by
    rw [div_sub_one h0, norm_div, div_lt_one (norm_pos_iff.2 h0)]
    rwa [mem_ball, dist_eq_norm] at hz
  rw [← pf_cylInf hvper, ← cylInf_mul_one_add s₀ t₀ hlt, add_sub_cancel, mul_div_cancel₀ _ h0]

lemma pf_contDiffAt (hv : ContDiff ℝ ∞ v) (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t))
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) : ContDiffAt ℝ ∞ (pf v) z₀ := by
  set s₀ := Real.log ‖z₀‖ / (2 * π)
  set t₀ := Complex.arg z₀ / (2 * π)
  have he : cylInf s₀ t₀ = z₀ := cylInf_log_arg hz₀
  have hr : 0 < ‖cylInf s₀ t₀‖ := norm_pos_iff.2 (cylInf_ne_zero _ _)
  have hloc : pf v =ᶠ[𝓝 z₀] fun z => vecToC (v (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im)) := by
    have : ball (cylInf s₀ t₀) ‖cylInf s₀ t₀‖ ∈ 𝓝 z₀ := by
      rw [he] at hr ⊢; exact ball_mem_nhds _ hr
    filter_upwards [this] with z hz
    exact pf_local hvper s₀ t₀ hz
  refine ContDiffAt.congr_of_eventuallyEq ?_ hloc
  have hq : ContDiffAt ℝ ∞ (fun z => z / cylInf s₀ t₀ - 1) z₀ :=
    (contDiffAt_id.div_const _).sub contDiffAt_const
  have hq0 : ‖z₀ / cylInf s₀ t₀ - 1‖ < 1 := by rw [he, div_self hz₀, sub_self, norm_zero]; norm_num
  have hl : ContDiffAt ℝ ∞ (fun z => lchart (z / cylInf s₀ t₀ - 1)) z₀ :=
    ContDiffAt.comp (g := lchart) (f := fun z => z / cylInf s₀ t₀ - 1) z₀
      (lchart_contDiffAt hq0) hq
  have hpair : ContDiffAt ℝ ∞ (fun z => (s₀ + (lchart (z / cylInf s₀ t₀ - 1)).re,
      t₀ + (lchart (z / cylInf s₀ t₀ - 1)).im)) z₀ :=
    (contDiffAt_const.add (Complex.reCLM.contDiff.contDiffAt.comp z₀ hl)).prodMk
      (contDiffAt_const.add (Complex.imCLM.contDiff.contDiffAt.comp z₀ hl))
  exact vC.contDiff.contDiffAt.comp z₀ (hv.contDiffAt.comp z₀ hpair)

lemma pf_contDiffOn (hv : ContDiff ℝ ∞ v) (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t))
    (U : Set ℂ) : ContDiffOn ℝ ∞ (pf v) (U \ {0}) := fun z hz =>
  (pf_contDiffAt hv hvper hz.2).contDiffWithinAt

/-! ### Derivatives through the exponential chart -/

/-- `cylInf` on `ℝ × ℝ`. -/
def Ecyl (x : ℝ × ℝ) : ℂ := cylInf x.1 x.2

lemma toC_eq (x : ℝ × ℝ) : toC x = (x.1 : ℂ) + (x.2 : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [toC]

lemma Ecyl_eq (x : ℝ × ℝ) : Ecyl x = Complex.exp (((2 * π : ℝ) : ℂ) * toC x) := by
  rw [Ecyl, cylInf_eq_exp, toC_eq]

lemma hasFDerivAt_Ecyl (x : ℝ × ℝ) :
    HasFDerivAt Ecyl ((((2 * π : ℝ) : ℂ) * Ecyl x) • (Complex.equivRealProdCLM.symm :
      ℝ × ℝ →L[ℝ] ℂ)) x := by
  have e : Ecyl = fun x => Complex.exp (((2 * π : ℝ) : ℂ) * toC x) := funext Ecyl_eq
  have hL : HasFDerivAt (fun x : ℝ × ℝ => ((2 * π : ℝ) : ℂ) * toC x)
      (((2 * π : ℝ) : ℂ) • (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ)) x := by
    have := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).hasFDerivAt (x := x)
    exact this.const_smul (((2 * π : ℝ) : ℂ))
  have h := ((Complex.hasDerivAt_exp (((2 * π : ℝ) : ℂ) * toC x)).hasFDerivAt.restrictScalars ℝ).comp
    x hL
  rw [e]
  refine h.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul,
    ContinuousLinearMap.toSpanSingleton_apply, Ecyl_eq]
  rw [show (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) y = toC y from rfl]
  ring

/-- The chain rule through `Ecyl`. -/
lemma fderiv_pf_cylInf (hv : ContDiff ℝ ∞ v) (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t))
    (x : ℝ × ℝ) (h : ℂ) :
    fderiv ℝ (pf v) (Ecyl x) (((2 * π : ℝ) : ℂ) * Ecyl x * h) = vecToC (fderiv ℝ v x (cplx h)) := by
  have hcomp : (pf v) ∘ Ecyl = fun x => vC (v x) := by
    funext x; simp [Ecyl, pf_cylInf hvper, vC_apply]
  have hdz : DifferentiableAt ℝ (pf v) (Ecyl x) :=
    (pf_contDiffAt hv hvper (cylInf_ne_zero _ _)).differentiableAt (by simp)
  have h1 := (hdz.hasFDerivAt.comp x (hasFDerivAt_Ecyl x))
  rw [hcomp] at h1
  have h2 : HasFDerivAt (fun x => vC (v x)) (vC.comp (fderiv ℝ v x)) x :=
    vC.hasFDerivAt.comp x ((hv.differentiable (by simp)) x).hasFDerivAt
  have := congrArg (fun L : ℝ × ℝ →L[ℝ] ℂ => L (cplx h)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_coe] at this
  rw [← vC_apply, ← this]
  congr 1

/-- For a real-linear `L : ℂ → ℂ`, `L c + i L(c i) = c̄ (L 1 + i L i)`. -/
lemma clm_conj_identity (L : ℂ →L[ℝ] ℂ) (c : ℂ) :
    L c + Complex.I * L (c * Complex.I) =
      (starRingEnd ℂ) c * (L 1 + Complex.I * L Complex.I) := by
  have key : ∀ w : ℂ, L w = (w.re : ℂ) * L 1 + (w.im : ℂ) * L Complex.I := by
    intro w
    have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by
      apply Complex.ext <;> simp
    conv_lhs => rw [hw]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hconj : (starRingEnd ℂ) c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [key c, key (c * Complex.I), Complex.mul_I_re, Complex.mul_I_im, hconj, Complex.ofReal_neg]
  linear_combination ((c.im : ℂ) * L Complex.I) * Complex.I_sq

/-- The plane equation on `ℂ \ {0}`. -/
lemma pf_eq (S : ℝ × ℝ → Mat 1) (A : ℂ → ℂ →L[ℝ] ℂ)
    (hA : ∀ (s t : ℝ) (a : Vec 1), vecToC (Matrix.toEuclideanLin (S (s, t)) a) =
      (4 * π : ℝ) * (starRingEnd ℂ) (cylInf s t) * A (cylInf s t) (vecToC a))
    (hv : ContDiff ℝ ∞ v) (hvper : ∀ s t : ℝ, v (s, t + 1) = v (s, t))
    (heq : ∀ x, crOp S v x = 0) {z : ℂ} (hz : z ≠ 0) :
    fderiv ℝ (pf v) z 1 + Complex.I * fderiv ℝ (pf v) z Complex.I =
      -((2 : ℂ) * A z (pf v z)) := by
  set x : ℝ × ℝ := (Real.log ‖z‖ / (2 * π), Complex.arg z / (2 * π))
  have hx : Ecyl x = z := cylInf_log_arg hz
  set L := fderiv ℝ (pf v) z
  set c : ℂ := ((2 * π : ℝ) : ℂ) * z
  have h1 : L c = vecToC (partialS v x) := by
    have := fderiv_pf_cylInf hv hvper x 1
    rw [hx, mul_one] at this
    rw [show partialS v x = fderiv ℝ v x (cplx 1) by simp [partialS, cplx_apply]]
    exact this
  have h2 : L (c * Complex.I) = vecToC (partialT v x) := by
    have := fderiv_pf_cylInf hv hvper x Complex.I
    rw [hx] at this
    rw [show partialT v x = fderiv ℝ v x (cplx Complex.I) by simp [partialT, cplx_apply]]
    exact this
  have hcr := heq x
  have hsum : L c + Complex.I * L (c * Complex.I) =
      -(((4 * π : ℝ) : ℂ) * (starRingEnd ℂ) z * A z (pf v z)) := by
    rw [h1, h2, ← vecToC_J₀]
    have : vecToC (partialS v x) + vecToC (Matrix.toEuclideanLin (J₀ 1) (partialT v x)) =
        -vecToC (Matrix.toEuclideanLin (S x) (v x)) := by
      rw [← vC_apply, ← vC_apply, ← vC_apply, ← map_add, ← map_neg]
      congr 1
      rw [crOp] at hcr
      exact eq_neg_of_add_eq_zero_left hcr
    rw [this, show x = (x.1, x.2) from rfl, hA, ← pf_cylInf hvper,
      show cylInf x.1 x.2 = z from hx]
  rw [clm_conj_identity] at hsum
  have hcz : (starRingEnd ℂ) c = ((2 * π : ℝ) : ℂ) * (starRingEnd ℂ) z := by
    rw [map_mul, Complex.conj_ofReal]
  have hc0 : (starRingEnd ℂ) c ≠ 0 := by
    rw [hcz]
    exact mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity))
      ((map_ne_zero (starRingEnd ℂ)).2 hz)
  apply mul_left_cancel₀ hc0
  rw [hsum, hcz]
  push_cast
  ring

/-! ### Decay at `0` -/

lemma norm_pf_le (B : ℝ) (g : ℝ × ℝ → Vec 1) (hB : ∀ x, ‖g x‖ ≤ B) (χ : ℝ → ℝ)
    (hvg : ∀ x, v x = Real.exp (χ x.1) • g x) (z : ℂ) (hz : z ≠ 0) :
    ‖pf v z‖ ≤ B * Real.exp (χ (Real.log ‖z‖ / (2 * π))) := by
  rw [pf, if_neg hz, hvg]
  refine (norm_vecToC_le _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le

lemma tendsto_pf_zero (B : ℝ) (g : ℝ × ℝ → Vec 1) (hB : ∀ x, ‖g x‖ ≤ B) (χ : ℝ → ℝ)
    (hχ : ∀ s ≤ -1, χ s = χ (-1) + π * (s + 1))
    (hvg : ∀ x, v x = Real.exp (χ x.1) • g x) : ContinuousAt (pf v) 0 := by
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z‖ / (2 * π)) (𝓝[≠] 0) atBot := by
    have h1 : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    exact (Real.tendsto_log_nhdsGT_zero.comp h1).atBot_div_const (by positivity)
  have hχb : Tendsto χ atBot atBot := by
    have h : Tendsto (fun s => χ (-1) + π * (s + 1)) atBot atBot :=
      tendsto_atBot_add_const_left _ _ ((tendsto_atBot_add_const_right _ 1 tendsto_id).const_mul_atBot
        Real.pi_pos)
    refine h.congr' ?_
    filter_upwards [eventually_le_atBot (-1)] with s hs
    exact (hχ s hs).symm
  have hexp : Tendsto (fun z : ℂ => B * Real.exp (χ (Real.log ‖z‖ / (2 * π)))) (𝓝[≠] 0) (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (hχb.comp hlog)).const_mul B
    simpa using this
  have hne : Tendsto (pf v) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hexp
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact norm_pf_le B g hB χ hvg z hz
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, pf_zero]
  exact hne

end

end QL

end FiniteEnergyPlane

/-!
# Q-L, layer L5a: the unweighted solution `v = e^χ g` and its energy near `s = -∞`
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Weights -/

/-- An exponential weight bound on a half-line from affinity beyond `1` (resp. `-1`). -/
lemma exists_exp_bound_right (χ : ℝ → ℝ) (hc : Continuous χ) (b : ℝ)
    (hχ : ∀ s ≥ 1, χ s = χ 1 + b * (s - 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≥ 0, Real.exp (χ s) ≤ K * Real.exp (b * s) := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((Real.continuous_exp.comp (hc.sub (continuous_const.mul continuous_id)))).continuousOn
  refine ⟨max (max K₀ 1) (Real.exp (χ 1 - b)), lt_max_of_lt_left (lt_max_of_lt_right one_pos),
    fun s hs => ?_⟩
  have hsplit : Real.exp (χ s) = Real.exp (χ s - b * s) * Real.exp (b * s) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  rcases le_or_gt s 1 with h1 | h1
  · have := hK₀ s ⟨hs, h1⟩
    simp only [Function.comp, Real.norm_eq_abs, Real.abs_exp, id] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · rw [hχ s h1.le]
    exact le_of_eq_of_le (by ring_nf) (le_max_right _ _)

lemma exists_exp_bound_left (χ : ℝ → ℝ) (hc : Continuous χ) (a : ℝ)
    (hχ : ∀ s ≤ -1, χ s = χ (-1) + a * (s + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ s ≤ 0, Real.exp (χ s) ≤ K * Real.exp (a * s) := by
  obtain ⟨K, hK, h⟩ := exists_exp_bound_right (fun s => χ (-s)) (hc.comp continuous_neg) (-a)
    (fun s hs => by rw [hχ (-s) (by linarith)]; ring_nf)
  refine ⟨K, hK, fun s hs => ?_⟩
  have := h (-s) (by linarith)
  simpa using this

/-! ### `v = e^χ g` -/

variable {g : ℝ × ℝ → Vec 1} {χ : ℝ → ℝ}

/-- The unweighted section. -/
def vOf (χ : ℝ → ℝ) (g : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : Vec 1 := Real.exp (χ x.1) • g x

lemma hasFDerivAt_expχ (hχ : ContDiff ℝ ∞ χ) (x : ℝ × ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => Real.exp (χ x.1))
      ((Real.exp (χ x.1) * deriv χ x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  have hd : HasDerivAt χ (deriv χ x.1) x.1 :=
    ((hχ.differentiable (by simp)) x.1).hasDerivAt
  have h := ((Real.hasDerivAt_exp (χ x.1)).comp x.1 hd).hasFDerivAt.comp x
    (hasFDerivAt_fst (p := x))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun y => ?_)
  simp [mul_comm]

lemma hasFDerivAt_vOf (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    HasFDerivAt (vOf χ g) (Real.exp (χ x.1) • fderiv ℝ g x +
      ((Real.exp (χ x.1) * deriv χ x.1) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (g x)) x :=
  (hasFDerivAt_expχ hχ x).smul ((hg.differentiable (by simp)) x).hasFDerivAt

lemma vOf_contDiff (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (vOf χ g) :=
  (Real.contDiff_exp.comp (hχ.comp contDiff_fst)).smul hg

lemma vOf_per (hgper : ∀ s t : ℝ, g (s, t + 1) = g (s, t)) (s t : ℝ) :
    vOf χ g (s, t + 1) = vOf χ g (s, t) := by simp [vOf, hgper]

lemma toE_add_smul_one (A : Mat 1) (c : ℝ) (y : Vec 1) :
    Matrix.toEuclideanLin (A + c • (1 : Mat 1)) y = Matrix.toEuclideanLin A y + c • y := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  congr 2
  simp [Matrix.toEuclideanLin_apply]

lemma vOf_crOp (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (S : ℝ × ℝ → Mat 1) (x : ℝ × ℝ) :
    crOp S (vOf χ g) x =
      Real.exp (χ x.1) • crOp (fun x => S x + deriv χ x.1 • (1 : Mat 1)) g x := by
  have hd := (hasFDerivAt_vOf hχ hg x).fderiv
  have hS1 : partialS (vOf χ g) x =
      Real.exp (χ x.1) • partialS g x + (Real.exp (χ x.1) * deriv χ x.1) • g x := by
    simp [partialS, hd]
  have hT1 : partialT (vOf χ g) x = Real.exp (χ x.1) • partialT g x := by
    simp [partialT, hd]
  simp only [crOp, hS1, hT1, vOf, map_smul, toE_add_smul_one, smul_add, smul_smul]
  module

/-- A continuous linear map on `ℝ × ℝ` is bounded by its two partials. -/
lemma norm_clm_prod_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ × ℝ →L[ℝ] E) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
  have hy : y = y.1 • ((1 : ℝ), (0 : ℝ)) + y.2 • ((0 : ℝ), (1 : ℝ)) := by
    obtain ⟨a, b⟩ := y; simp
  have h1 : |y.1| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_fst_le y
  have h2 : |y.2| ≤ ‖y‖ := by
    rw [← Real.norm_eq_abs]; exact norm_snd_le y
  calc ‖L y‖ = ‖y.1 • L (1, 0) + y.2 • L (0, 1)‖ := by
        conv_lhs => rw [hy]
        rw [map_add, map_smul, map_smul]
    _ ≤ |y.1| * ‖L (1, 0)‖ + |y.2| * ‖L (0, 1)‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ‖y‖ * ‖L (1, 0)‖ + ‖y‖ * ‖L (0, 1)‖ := by gcongr
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖y‖ := by ring

lemma norm_fderiv_vOf_le (hχ : ContDiff ℝ ∞ χ) (hg : ContDiff ℝ ∞ g) (x : ℝ × ℝ) :
    ‖fderiv ℝ (vOf χ g) x‖ ≤
      Real.exp (χ x.1) * (|deriv χ x.1| * ‖g x‖ + ‖partialS g x‖ + ‖partialT g x‖) := by
  rw [(hasFDerivAt_vOf hχ hg x).fderiv]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hf : ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ
  have hD := norm_clm_prod_le (fderiv ℝ g x)
  have e1 : ‖fderiv ℝ g x‖ ≤ ‖partialS g x‖ + ‖partialT g x‖ := hD
  have : |deriv χ x.1| * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ * ‖g x‖ ≤ |deriv χ x.1| * ‖g x‖ := by
    have := mul_le_mul_of_nonneg_left hf (abs_nonneg (deriv χ x.1))
    nlinarith [norm_nonneg (g x)]
  have he := (Real.exp_pos (χ x.1)).le
  nlinarith [mul_le_mul_of_nonneg_left e1 he, mul_le_mul_of_nonneg_left this he]

end

end QL

end FiniteEnergyPlane

namespace CauchyRiemannIndex

/-- The restricted fundamental solution of a nondegenerate symmetric loop lies in `SP n`. -/
lemma crj_mem_SP (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    ψ ∈ ConleyZehnder.SP n := by
  refine ⟨fun t => ?_, ?_, ?_⟩
  · rw [hψ]; exact fundamentalSolution_symplectic n S hS.2.2 Ψ hΨ t
  · rw [hψ]; simpa using hΨ.1
  · rw [hψ]; simpa using hnd Ψ hΨ

lemma crj_czIndex_eq_of_isCZValue {n : ℕ} (ψ : C(unitInterval, Mat n))
    (hSP : ψ ∈ ConleyZehnder.SP n) {k : ℤ} (hk : IsCZValue ψ k) : czIndex ψ = k := by
  obtain ⟨k', -, huniq⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (huniq _ hex.choose_spec).trans (huniq _ hk).symm

lemma crj_bridge (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hnd : IsNondegenerate S) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (ψ : C(unitInterval, Mat n)) (hψ : ∀ t : unitInterval, ψ t = Ψ t) :
    asymptoticCZIndex S = czIndex ψ := by
  have hSP := crj_mem_SP n S hS hnd Ψ hΨ ψ hψ
  obtain ⟨k, hk, -⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hk' : IsCZValue ψ k := hk
  rw [crj_czIndex_eq_of_isCZValue ψ hSP hk']
  have hex : ∃ k, IsAsymptoticCZValue S k := ⟨k, Ψ, hΨ, ψ, hψ, hk'⟩
  unfold asymptoticCZIndex
  rw [dif_pos hex]
  obtain ⟨Ψ', hΨ', ψ', hψ', hk''⟩ := hex.choose_spec
  have hΨΨ : Ψ' = Ψ := (fundamentalSolution_existsUnique n S hS.1).unique hΨ' hΨ
  have hψψ : ψ' = ψ := ContinuousMap.ext fun t => by rw [hψ', hψ, hΨΨ]
  rw [hψψ] at hk''
  exact (crj_czIndex_eq_of_isCZValue ψ hSP hk'').symm.trans
    (crj_czIndex_eq_of_isCZValue ψ hSP hk')

end CauchyRiemannIndex

/-!
# Q-L, layer L6: L-I, the weighted operator is Fredholm of index `0`
-/

namespace FiniteEnergyPlane

namespace QL

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

/-! ### Shifting the asymptotic operator -/

lemma isLoopEigen_shift (Sinf : ℝ → Mat 1) (δ μ : ℝ) (e : ℝ → Vec 1) :
    IsLoopEigen (fun t => Sinf t + δ • (1 : Mat 1)) μ e ↔ IsLoopEigen Sinf (μ + δ) e := by
  simp only [IsLoopEigen, toE_add_smul_one]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' fun t => ⟨fun h => ?_, fun h => ?_⟩
  · rw [add_smul, ← h]; abel
  · rw [sub_add_eq_sub_sub, h, add_smul, add_sub_cancel_right]

lemma hasLoopEigenWind_shift (Sinf : ℝ → Mat 1) (δ μ : ℝ) (k : ℤ) :
    HasLoopEigenWind (fun t => Sinf t + δ • (1 : Mat 1)) μ k ↔ HasLoopEigenWind Sinf (μ + δ) k := by
  simp only [HasLoopEigenWind, isLoopEigen_shift]

lemma isSymLoop_shift {Sinf : ℝ → Mat 1} (h : IsSymLoop Sinf) (δ : ℝ) :
    IsSymLoop (fun t => Sinf t + δ • (1 : Mat 1)) :=
  ⟨h.1.add continuous_const, fun t => by simp only [h.2.1 t],
    fun t => (h.2.2 t).add (Matrix.isSymm_one.smul δ)⟩

lemma contDiff_shift {Sinf : ℝ → Mat 1} (h : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (δ : ℝ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => (Sinf t + δ • (1 : Mat 1)) i j) := fun i j => by
  simp only [Matrix.add_apply, Matrix.smul_apply]
  exact (h i j).add contDiff_const

/-- No eigenvalue `δ` gives nondegeneracy of the shifted loop. -/
lemma isNondegenerate_shift {Sinf : ℝ → Mat 1} (hSinf : IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (δ : ℝ)
    (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e) : IsNondegenerate (fun t => Sinf t + δ • (1 : Mat 1)) := by
  intro Ψ hΨ hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hv1 : Matrix.mulVec (Ψ 1) v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    exact hv.symm
  set w : Vec 1 := WithLp.toLp 2 v
  have hw0 : w ≠ 0 := by
    intro h; apply hv0
    have := congrArg (WithLp.ofLp) h
    simpa [w] using this
  have hw1 : Matrix.toEuclideanLin (Ψ 1) w = w := by
    simp only [w, Matrix.toEuclideanLin_apply, hv1]
  exact hδe _ (isLoopEigen_of_fundamentalSolution_apply_one Sinf hSinf hSinf' δ Ψ hΨ w hw0 hw1)

/-! ### Conley–Zehnder indices of the ends -/

lemma czIndexOfPath_congr (φ φ' : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, φ t = φ' t) :
    HryniewiczCriterion.czIndexOfPath φ = HryniewiczCriterion.czIndexOfPath φ' := by
  have : HryniewiczCriterion.windingInterval φ = HryniewiczCriterion.windingInterval φ' := by
    ext d
    simp only [HryniewiczCriterion.windingInterval, HryniewiczCriterion.IsAngleLift,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨s, hs, θ, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨s, hs, θ, ⟨h1, h2, fun t ht => by rw [← h t ht]; exact h3 t ht⟩, rfl⟩
    · rintro ⟨s, hs, θ, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨s, hs, θ, ⟨h1, h2, fun t ht => by rw [h t ht]; exact h3 t ht⟩, rfl⟩
  unfold HryniewiczCriterion.czIndexOfPath
  rw [this]

/-- A loop with a spectral window around `δ` (winding `≤ 0` below, `≥ 1` above) has, after the
shift by `δ`, Conley–Zehnder index `1`. -/
theorem asymptoticCZIndex_shift_eq_one {Sinf : ℝ → Mat 1} (hSinf : IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (δ : ℝ)
    (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k)) :
    asymptoticCZIndex (fun t => Sinf t + δ • (1 : Mat 1)) = 1 := by
  have hT := isSymLoop_shift hSinf δ
  have hnd := isNondegenerate_shift hSinf hSinf' δ hδe
  obtain ⟨Ψ, hΨ, -⟩ := fundamentalSolution_existsUnique 1 _ hT.1
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun t => by
    letI : NormedAddCommGroup (Mat 1) := Matrix.normedAddCommGroup
    letI : NormedSpace ℝ (Mat 1) := Matrix.normedSpace
    exact (hΨ.2 t).continuousAt
  let ψ : C(unitInterval, Mat 1) := ⟨fun t => Ψ t, hΨc.comp continuous_subtype_val⟩
  have hSP := crj_mem_SP 1 _ hT hnd Ψ hΨ ψ (fun _ => rfl)
  rw [crj_bridge 1 _ hT hnd Ψ hΨ ψ (fun _ => rfl),
    show CauchyRiemannIndex.czIndex ψ = ConleyZehnder.czIndex ψ from rfl,
    czIndex_eq_czIndexOfPath ψ hSP]
  obtain ⟨a, b, ⟨⟨μ, hμ, ha⟩, -⟩, ⟨⟨μ', hμ', hb⟩, -⟩, hab, hcz⟩ :=
    exists_loopAlpha_czIndexOfPath_eq_of_symLoop _ hT (contDiff_shift hSinf' δ)
  rw [czIndexOfPath_congr _ (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ))
    (fun τ hτ => by
      show Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ (Set.projIcc 0 1 zero_le_one τ)) = _
      rw [Set.projIcc_of_mem _ hτ]), hcz Ψ hΨ]
  have ha0 : a ≤ 0 := by
    rcases hwin _ _ ((hasLoopEigenWind_shift Sinf δ μ a).1 ha) with h | h
    · exact h.2
    · linarith [h.1]
  have hb1 : 1 ≤ b := by
    rcases hwin _ _ ((hasLoopEigenWind_shift Sinf δ μ' b).1 hb) with h | h
    · linarith [h.1]
    · exact h.2
  omega

/-- The constant loop `π · 1` has Conley–Zehnder index `1`. -/
theorem asymptoticCZIndex_pi_smul_one :
    asymptoticCZIndex (fun _ : ℝ => π • (1 : Mat 1)) = 1 := by
  set β : ℝ → ℂ := fun t => Complex.exp (2 * π * t * Complex.I)
  have hβc : Continuous β := by fun_prop
  have hper : Function.Periodic β 1 := fun t => by
    simp only [β]
    rw [show (2 * π * ((t + 1 : ℝ) : ℂ) * Complex.I : ℂ) =
      2 * π * t * Complex.I + 2 * π * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hnd : ∀ σ : ℝ, 0 ≤ σ →
      IsNondegenerate (fun t => π • (1 : Mat 1) + σ • antilinearMat (β t)) := by
    intro σ hσ
    rcases hσ.eq_or_lt with rfl | hpos
    · simp only [zero_smul, add_zero]
      exact (isNondegenerate_pi_smul_one 1).2
    · have := (model_asymptotic_operator 1 σ hpos).1
      simp only [Int.cast_one, mul_one] at this
      exact this
  have he : ∀ t : ℝ, (2 * π * t * Complex.I : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I := by
    intro t; push_cast; ring
  refine asymptoticCZIndex_eq_winding_of_antilinear _ (isNondegenerate_pi_smul_one 1).1 β hβc
    hper (fun t => Complex.exp_ne_zero _) hnd 1 (fun t => 2 * π * t) (by fun_prop)
    (fun t => ?_) (by simp)
  simp only [β, he, Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul]

/-! ### The ends of the weighted coefficient -/

lemma abs_apply_le_norm_vecToC (v : Vec 1) (i : Fin 1 ⊕ Fin 1) : |v i| ≤ ‖vecToC v‖ := by
  rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · exact Complex.abs_re_le_norm (vecToC v)
  · exact Complex.abs_im_le_norm (vecToC v)

lemma isAsymptoticTo_window (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t)) (Sinf : ℝ → Mat 1)
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (δ : ℝ) (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    IsAsymptoticTo (fun x => S x + deriv χ x.1 • (1 : Mat 1))
      (fun t => Sinf t + δ • (1 : Mat 1)) (fun _ => π • (1 : Mat 1)) := by
  have hSc : Continuous S :=
    continuous_pi fun i => continuous_pi fun j => (hS i j).continuous
  have hcd : Continuous (deriv χ) := hχ.1.continuous_deriv (by simp)
  refine ⟨hSc.add ((hcd.comp continuous_fst).smul continuous_const),
    fun s t => by simp only [hSper], fun ε hε => ?_⟩
  -- `+∞`
  have hplus : ∀ i j, ∀ᶠ s in atTop, ∀ t, |S (s, t) i j - Sinf t i j| ≤ ε := by
    intro i j
    obtain ⟨C, s₁, hC⟩ := (hSas i j).2 0
    have hlim : Tendsto (fun s : ℝ => C * Real.exp (-(d * s))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hd))).const_mul C
      simpa using this
    filter_upwards [hlim.eventually (ge_mem_nhds hε), eventually_ge_atTop s₁] with s h1 h2 t
    have := hC s h2 t
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans h1
  -- `-∞`
  obtain ⟨A, hAc, hAeq⟩ := hA
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hAc.continuous.continuousOn
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 (mem_closedBall_self zero_le_one))
  have hent : ∀ s ≤ 0, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ 4 * π * K * Real.exp (2 * π * s) := by
    intro s hs t i j
    set a : Vec 1 := EuclideanSpace.single j 1
    have e : (Matrix.toEuclideanLin (S (s, t)) a) i = S (s, t) i j := by
      simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec_single_one]
    have hz : cylInf s t ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_cylInf]
      exact Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have ha : ‖vecToC a‖ ≤ 1 := (norm_vecToC_le a).trans (by simp [a])
    rw [← e]
    refine (abs_apply_le_norm_vecToC _ i).trans ?_
    rw [hAeq, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * π), Complex.norm_conj, norm_cylInf]
    calc 4 * π * Real.exp (2 * π * s) * ‖A (cylInf s t) (vecToC a)‖
        ≤ 4 * π * Real.exp (2 * π * s) * (K * 1) :=
          mul_le_mul_of_nonneg_left (((A _).le_opNorm _).trans
            (mul_le_mul (hK _ hz) ha (norm_nonneg _) hK0)) (by positivity)
      _ = 4 * π * K * Real.exp (2 * π * s) := by ring
  have hminus : ∀ᶠ s in atBot, ∀ t : ℝ, ∀ i j, |S (s, t) i j| ≤ ε := by
    have hlim : Tendsto (fun s : ℝ => 4 * π * K * Real.exp (2 * π * s)) atBot (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atBot (by positivity : (0 : ℝ) < 2 * π))).const_mul (4 * π * K)
      simpa using this
    filter_upwards [hlim.eventually (ge_mem_nhds hε), eventually_le_atBot 0] with s h1 h2 t i j
    exact (hent s h2 t i j).trans h1
  have hplus' : ∀ᶠ s in atTop, ∀ i j, ∀ t, |S (s, t) i j - Sinf t i j| ≤ ε := by
    rw [eventually_all]; intro i; rw [eventually_all]; exact hplus i
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hplus'
  obtain ⟨R₂, hR₂⟩ := eventually_atBot.1 hminus
  have m1 := le_max_left (max R₁ 1) (max (-R₂) 1)
  have m2 := le_max_right (max R₁ 1) (max (-R₂) 1)
  have m3 := le_max_left R₁ 1
  have m4 := le_max_right R₁ 1
  have m5 := le_max_left (-R₂) 1
  have m6 := le_max_right (-R₂) 1
  refine ⟨max (max R₁ 1) (max (-R₂) 1), fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · show |(S (s, t) + deriv χ s • (1 : Mat 1)) i j - (Sinf t + δ • (1 : Mat 1)) i j| ≤ ε
    have h1 : 1 ≤ s := by linarith
    have h2 : R₁ ≤ s := by linarith
    have : (S (s, t) + deriv χ s • (1 : Mat 1)) i j - (Sinf t + δ • (1 : Mat 1)) i j =
        S (s, t) i j - Sinf t i j := by
      simp only [hχ.2.2 s h1, Matrix.add_apply]; ring
    rw [this]; exact hR₁ s h2 i j t
  · show |(S (s, t) + deriv χ s • (1 : Mat 1)) i j - (π • (1 : Mat 1)) i j| ≤ ε
    have h1 : s ≤ -1 := by linarith
    have h2 : s ≤ R₂ := by linarith
    have : (S (s, t) + deriv χ s • (1 : Mat 1)) i j - (π • (1 : Mat 1)) i j = S (s, t) i j := by
      simp only [hχ.2.1 s h1, Matrix.add_apply]; ring
    rw [this]; exact hR₂ s h2 t i j

/-- L-I. -/
theorem fredholm_index_zero_of_window_proof (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    IsFredholmCR p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) ∧
      crIndex p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) = 0 := by
  have hpi := isNondegenerate_pi_smul_one 1
  have hF := index_formula 1 p hp hp' _ _ (isSymLoop_shift hSinf δ) hpi.1 _
    (isAsymptoticTo_window S hS hSper Sinf d hd hSas hA δ χ hχ)
    (isNondegenerate_shift hSinf hSinf' δ hδe) hpi.2
  refine ⟨hF.1, ?_⟩
  rw [hF.2, asymptoticCZIndex_shift_eq_one hSinf hSinf' δ hδe hwin, asymptoticCZIndex_pi_smul_one]
  simp

end

end QL

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ⊤)
    (Sinf : ℝ → Mat 1) (hSinf : IsSymLoop Sinf) (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (δ : ℝ) (hδe : ∀ e, ¬ IsLoopEigen Sinf δ e)
    (hwin : ∀ (μ : ℝ) (k : ℤ), HasLoopEigenWind Sinf μ k → (μ < δ ∧ k ≤ 0) ∨ (δ < μ ∧ 1 ≤ k))
    (S : ℝ × ℝ → Mat 1) (hS : ∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => S x i j))
    (hSper : ∀ s t : ℝ, S (s, t + 1) = S (s, t))
    (d : ℝ) (hd : 0 < d) (hSas : IsExpAsymptoticTo S Sinf d) (hA : IsPlaneCoeff S)
    (χ : ℝ → ℝ) (hχ : IsSlopeWeight χ π δ) :
    IsFredholmCR p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) ∧
      crIndex p (fun x => S x + deriv χ x.1 • (1 : Mat 1)) = 0 :=
  QL.fredholm_index_zero_of_window_proof p hp hp' Sinf hSinf hSinf' δ hδe hwin S hS hSper d hd hSas hA χ hχ
