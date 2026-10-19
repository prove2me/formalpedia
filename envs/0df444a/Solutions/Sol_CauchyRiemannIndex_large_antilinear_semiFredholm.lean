-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_semiFredholm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T13:47:10.980162+00:00
-- url     : https://prove2.me/submissions/c02c2547-6d0e-4ae9-9a40-d9a84e5e50bc

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
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
import Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity
import Mathlib.MeasureTheory.Function.L2Space



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

/-- The `L^q` annihilator of `D_S(W^{1,p})`, tested on test sections. -/
lemma ckm_ann_iff {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (g : LpCyl n q) :
    (∀ v ∈ crRange p S, ∫ x, inner ℝ (v x) (g x) ∂cylMeasure = 0) ↔
      ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
        ∫ x, inner ℝ (crOp S u x) (g x) ∂cylMeasure = 0 := by
  set T : Triple n p →L[ℝ] LpCyl n p := crsT S hc hb
  constructor
  · intro h u hu
    have hmem : T (testTriple hu) ∈ crRange p S :=
      Submodule.subset_span ⟨testTriple hu, ckp_tt_mem hu, crsT_ae S hc hb _⟩
    rw [← h _ hmem]
    refine integral_congr_ae ?_
    filter_upwards [crsT_ae S hc hb (testTriple (p := p) hu), ckp_tt_ae (p := p) S hu] with x h1 h2
    rw [h1, h2]
  · intro h
    let Λ : Triple n p →L[ℝ] ℝ :=
      ((ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := q)).flip g).comp T
    have hΛ : ∀ w, Λ w = ∫ x, inner ℝ (T w x) (g x) ∂cylMeasure := fun w => rfl
    have hW := ckp_W1p_le_ker Λ fun u hu w _ h1 h2 h3 => by
      rw [hΛ, ← h u hu]
      refine integral_congr_ae ?_
      filter_upwards [crsT_ae S hc hb w, crApply_ae_crOp S h1 h2 h3] with x e1 e2
      rw [e1, e2]
    have hle : crRange p S ≤ LinearMap.ker
        (((ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := q)).flip g :
          LpCyl n p →L[ℝ] ℝ) : LpCyl n p →ₗ[ℝ] ℝ) := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨w, hw, hfw⟩ := hf
      have hfT : f = T w := Lp.ext (hfw.trans (crsT_ae S hc hb w).symm)
      show ckaPairL f g = 0
      rw [hfT]
      exact hW w hw
    intro v hv
    exact hle hv

/-- `C g` is a weak solution of `D_{S̄} η = 0` when `g` annihilates `D_S` on test sections. -/
lemma ckm_weak {q : ℝ≥0∞} [Fact (1 ≤ q)] (S : ℝ × ℝ → Mat n) (g : LpCyl n q)
    (hg : ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp S u x) (g x) ∂cylMeasure = 0) :
    ∀ φ : ℝ × ℝ → Vec n, IsTestSection φ →
      ∫ x, inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (cBar (S x))ᵀ (φ x))
          (((matCLM n (conjMat n)).compLpL q cylMeasure g) x) ∂cylMeasure =
        ∫ x, inner ℝ (φ x) ((0 : LpCyl n q) x) ∂cylMeasure := by
  intro φ hφ
  have hR : ∫ x, inner ℝ (φ x) ((0 : LpCyl n q) x) ∂cylMeasure = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))]
    · simp
    filter_upwards [Lp.coeFn_zero (Vec n) q cylMeasure] with x hx
    rw [hx]; simp
  rw [hR]
  have hψ := hφ.ckp_conj
  have e : (fun x => inner ℝ (-partialS φ x + Matrix.toEuclideanLin (J₀ n) (partialT φ x) +
          Matrix.toEuclideanLin (cBar (S x))ᵀ (φ x))
          (((matCLM n (conjMat n)).compLpL q cylMeasure g) x)) =ᵐ[cylMeasure]
      fun x => -inner ℝ (crOp S (fun y => Matrix.toEuclideanLin (conjMat n) (φ y)) x) (g x) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := q) (μ := cylMeasure)
      (matCLM n (conjMat n)) g] with x hx
    rw [hx, matCLM_apply, ← ckp_inner_conj, ckp_key1, crOp, ckp_partialS_conj hφ,
      ckp_partialT_conj hφ, inner_neg_left]
  rw [integral_congr_ae e, integral_neg, hg _ hψ, neg_zero]

/-- Elements of `C · ker D_{S̄}` annihilate `D_S` on test sections. -/
lemma ckm_adj {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (S : ℝ × ℝ → Mat n) (hc : Continuous S)
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (S x) v‖ ≤ M * ‖v‖)
    (hcb : Continuous fun x => cBar (S x))
    (hbb : ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec n), ‖Matrix.toEuclideanLin (cBar (S x)) v‖ ≤ M * ‖v‖)
    (w : Triple n q) (hw : w ∈ W1p q n) (h0 : crsT (fun x => cBar (S x)) hcb hbb w = 0)
    (u : ℝ × ℝ → Vec n) (hu : IsTestSection u) :
    ∫ x, inner ℝ (crOp S u x) (((matCLM n (conjMat n)).compLpL q cylMeasure w.1) x)
      ∂cylMeasure = 0 := by
  set Sb : ℝ × ℝ → Mat n := fun x => cBar (S x)
  set T : Triple n p →L[ℝ] LpCyl n p := crsT S hc hb
  set Tb : Triple n q →L[ℝ] LpCyl n q := crsT Sb hcb hbb
  set cL : LpCyl n q →L[ℝ] LpCyl n q := (matCLM n (conjMat n)).compLpL q cylMeasure
  set cLp : LpCyl n p →L[ℝ] LpCyl n p := (matCLM n (conjMat n)).compLpL p cylMeasure
  set P := ckaPairL (μ := cylMeasure) (E := Vec n) (p := p) (q := q)
  set t := testTriple (p := p) hu
  let Λ : Triple n q →L[ℝ] ℝ :=
    (P (T t)).comp (cL.comp (ContinuousLinearMap.fst ℝ _ _)) + (P (cLp t.1)).comp Tb
  have ht1 : (t.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] u := (hu.memLp (p := p)).coeFn_toLp
  have hT : (T t : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] crOp S u :=
    (crsT_ae S hc hb t).trans (ckp_tt_ae S hu)
  have hW := ckp_W1p_le_ker Λ fun ψ hψ v _ h1 h2 h3 => by
    have hCψ := hψ.ckp_conj
    have hA := crOp_formalAdjoint n S hc u _ hu hCψ
    have e1 : ∫ x, inner ℝ (T t x) (cL v.1 x) ∂cylMeasure =
        ∫ x, inner ℝ (crOp S u x) (Matrix.toEuclideanLin (conjMat n) (ψ x)) ∂cylMeasure := by
      refine integral_congr_ae ?_
      filter_upwards [hT, ContinuousLinearMap.coeFn_compLpL (p := q) (μ := cylMeasure)
        (matCLM n (conjMat n)) v.1, h1] with x e1 e2 e3
      rw [e1, e2, matCLM_apply, e3]
    have e2 : ∫ x, inner ℝ (cLp t.1 x) (Tb v x) ∂cylMeasure =
        -∫ x, inner ℝ (u x) (-partialS (fun y => Matrix.toEuclideanLin (conjMat n) (ψ y)) x +
          Matrix.toEuclideanLin (J₀ n)
            (partialT (fun y => Matrix.toEuclideanLin (conjMat n) (ψ y)) x) +
          Matrix.toEuclideanLin (S x)ᵀ (Matrix.toEuclideanLin (conjMat n) (ψ x))) ∂cylMeasure := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p) (μ := cylMeasure)
        (matCLM n (conjMat n)) t.1, ht1, crsT_ae Sb hcb hbb v,
        crApply_ae_crOp Sb h1 h2 h3] with x e1 e2 e3 e4
      rw [e1, matCLM_apply, e2, e3, e4, ckp_partialS_conj hψ, ckp_partialT_conj hψ, ckp_key2,
        inner_neg_right, neg_neg, ckp_inner_conj]
      rfl
    show P (T t) (cL v.1) + P (cLp t.1) (Tb v) = 0
    rw [ckaPairL_apply, ckaPairL_apply, e1, e2, hA]
    exact add_neg_cancel _
  have h := hW w hw
  have h2 : P (cLp t.1) (Tb w) = 0 := by rw [show Tb w = 0 from h0, map_zero]
  have h1 : P (T t) (cL w.1) = 0 := by
    have : P (T t) (cL w.1) + P (cLp t.1) (Tb w) = 0 := h
    rwa [h2, add_zero] at this
  rw [← h1, ckaPairL_apply]
  refine integral_congr_ae ?_
  filter_upwards [hT] with x e
  rw [e]

theorem cokernel_eq_kernel_adjoint_aux (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 1 < p)
    (hp' : p ≠ ⊤)
    (Splus Sminus : ℝ → Mat n) (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat n) (hS : IsAsymptoticTo S Splus Sminus) (hplus : IsNondegenerate Splus)
    (hminus : IsNondegenerate Sminus)
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (hpq : 1 / p + 1 / q = 1) :
    FiniteDimensional ℝ (LpCyl n p ⧸ crRange p S) ∧
      Module.finrank ℝ (LpCyl n p ⧸ crRange p S) =
        Module.finrank ℝ (crKernel q (fun x => -(conjMat n * (S x)ᵀ * conjMat n))) := by
  haveI hH : p.HolderConjugate q := ⟨by simpa [one_div] using hpq⟩
  haveI : SigmaFinite cylMeasure := by unfold cylMeasure; infer_instance
  have hq1 : 1 < q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).1 (lt_top_iff_ne_top.2 hp')
  have hqt : q ≠ ⊤ := (ENNReal.HolderConjugate.ne_top_iff_ne_one q p).2 hp.ne'
  set Sb : ℝ × ℝ → Mat n := fun x => cBar (S x) with hSbdef
  change FiniteDimensional ℝ (LpCyl n p ⧸ crRange p S) ∧
    Module.finrank ℝ (LpCyl n p ⧸ crRange p S) = Module.finrank ℝ (crKernel q Sb)
  have hSb := isAsymptoticTo_cBar hS
  have hSbp := isSymLoop_cBar hSplus
  have hSbm := isSymLoop_cBar hSminus
  have hnbp := isNondegenerate_cBar hSplus hplus
  have hnbm := isNondegenerate_cBar hSminus hminus
  have hb := crs_Sbound hSplus hSminus hS
  have hbb := crs_Sbound hSbp hSbm hSb
  set Tb : Triple n q →L[ℝ] LpCyl n q := crsT Sb hSb.1 hbb
  set cL : LpCyl n q →L[ℝ] LpCyl n q := (matCLM n (conjMat n)).compLpL q cylMeasure
  have hcc : ∀ g, cL (cL g) = g := by
    intro g
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := q) (μ := cylMeasure)
      (matCLM n (conjMat n)) (cL g), ContinuousLinearMap.coeFn_compLpL (p := q) (μ := cylMeasure)
      (matCLM n (conjMat n)) g] with x e1 e2
    rw [e1, e2, matCLM_apply, matCLM_apply, ckp_conj_conj]
  -- the annihilator
  let N : Submodule ℝ (LpCyl n q) := ⨅ v : crRange p S,
    LinearMap.ker (ckaPair (μ := cylMeasure) (E := Vec n) (p := p) (q := q) (v : LpCyl n p))
  have hN : ∀ g : LpCyl n q, g ∈ N ↔
      ∀ v ∈ crRange p S, ∫ x, inner ℝ (v x) (g x) ∂cylMeasure = 0 := by
    intro g
    simp only [N, Submodule.mem_iInf, LinearMap.mem_ker, ckaPair_apply, Subtype.forall]
  have hNt : ∀ g : LpCyl n q, g ∈ N ↔ ∀ u : ℝ × ℝ → Vec n, IsTestSection u →
      ∫ x, inner ℝ (crOp S u x) (g x) ∂cylMeasure = 0 := fun g =>
    (hN g).trans (ckm_ann_iff S hS.1 hb g)
  -- kernel elements lie in `W^{1,q}` and are killed by `D_{S̄}`
  have hK : crKernel q Sb ≤ W1p q n ⊓ LinearMap.ker (Tb : Triple n q →ₗ[ℝ] LpCyl n q) := by
    refine Submodule.span_le.2 fun w hw => ⟨hw.1, ?_⟩
    show Tb w = 0
    exact Lp.ext ((crsT_ae Sb hSb.1 hbb w).trans (hw.2.trans (Lp.coeFn_zero _ _ _).symm))
  have hmapN : ∀ w ∈ crKernel q Sb, cL w.1 ∈ N := by
    intro w hw
    have h := hK hw
    exact (hNt _).2 fun u hu => ckm_adj (p := p) S hS.1 hb hSb.1 hbb w h.1 h.2 u hu
  -- the map `w ↦ C w.1`
  let Φ : crKernel q Sb →ₗ[ℝ] N :=
    LinearMap.codRestrict N ((cL : LpCyl n q →ₗ[ℝ] LpCyl n q) ∘ₗ
      LinearMap.fst ℝ (LpCyl n q) (LpCyl n q × LpCyl n q) ∘ₗ (crKernel q Sb).subtype)
      fun w => hmapN w.1 w.2
  have hΦ : ∀ w, (Φ w : LpCyl n q) = cL (w : Triple n q).1 := fun _ => rfl
  -- injectivity from the global estimate
  obtain ⟨R, c, hest⟩ := global_estimate n q hq1 hqt _ _ hSbp hSbm Sb hSb hnbp hnbm
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro w hw
    have h0 : cL (w : Triple n q).1 = 0 := by rw [← hΦ, hw]; rfl
    have h1 : (w : Triple n q).1 = 0 := by rw [← hcc (w : Triple n q).1, h0, map_zero]
    have hkw := hK w.2
    have hT0 : Tb w = 0 := hkw.2
    have hKw : crsK n q R (w : Triple n q) = 0 := by
      simp [crsK, h1]
    have := crs_estimate Sb hSb.1 hbb R c hest _ hkw.1
    have hle : ‖(w : Triple n q)‖ ≤ 0 := by
      refine this.trans (le_of_eq ?_)
      change (c : ℝ) * ‖Tb w‖ + c * ‖crsK n q R (w : Triple n q)‖ = 0
      rw [hT0, hKw]; simp
    exact Subtype.ext (norm_le_zero_iff.1 hle)
  -- surjectivity from regularity of weak solutions
  have hsurj : Function.Surjective Φ := by
    rintro ⟨g, hg⟩
    have hweak := ckm_weak S g ((hNt g).1 hg)
    obtain ⟨w, hw, hw1, hw0⟩ := memW1p_of_weak_solution n q hq1 hqt _ _ hSbp hSbm Sb hSb
      (cL g) 0 hweak
    have hwk : w ∈ crKernel q Sb :=
      Submodule.subset_span ⟨hw, hw0.trans (Lp.coeFn_zero _ _ _)⟩
    refine ⟨⟨w, hwk⟩, Subtype.ext ?_⟩
    rw [hΦ]
    show cL w.1 = g
    rw [hw1, hcc]
  let e : crKernel q Sb ≃ₗ[ℝ] N := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  -- finite dimensionality and closed range
  have hfdK : FiniteDimensional ℝ (crKernel q Sb) :=
    (semiFredholm n q hq1 hqt _ _ hSbp hSbm Sb hSb hnbp hnbm).1
  have hfdN : FiniteDimensional ℝ N := LinearEquiv.finiteDimensional e
  have hcl : IsClosed (crRange p S : Set (LpCyl n p)) :=
    (semiFredholm n p hp hp' Splus Sminus hSplus hSminus S hS hplus hminus).2
  obtain ⟨hfd, hrank⟩ := finrank_quotient_eq_finrank_annihilator cylMeasure p q hp hp'
    (crRange p S) hcl N hN hfdN
  exact ⟨hfd, hrank.trans e.finrank_eq.symm⟩

end

end CauchyRiemannIndex

/-!
# Conjugation by `J₀` and the antilinear matrix

`jc A = J₀ᵀ A J₀`. Together with `cBar A = -C Aᵀ C` it turns `antilinearMat β` into
`antilinearMat β̄`, and it preserves symmetric loops, nondegeneracy and asymptotics.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-- `J₀ᵀ A J₀`. -/
def jc (A : Mat n) : Mat n := (J₀ n)ᵀ * A * J₀ n

lemma J₀_transpose_mul_self : (J₀ n)ᵀ * J₀ n = 1 := by
  rw [J₀, J_transpose, neg_mul, J_squared, neg_neg]

lemma J₀_mul_transpose_self : J₀ n * (J₀ n)ᵀ = 1 := by
  rw [J₀, J_transpose, mul_neg, J_squared, neg_neg]

lemma J₀_transpose_comm : J₀ n * (J₀ n)ᵀ = (J₀ n)ᵀ * J₀ n := by
  rw [J₀_transpose_mul_self, J₀_mul_transpose_self]

lemma jc_add (A B : Mat n) : jc (A + B) = jc A + jc B := by
  simp [jc, mul_add, add_mul]

lemma jc_smul (c : ℝ) (A : Mat n) : jc (c • A) = c • jc A := by
  simp [jc, Matrix.mul_smul, Matrix.smul_mul]

lemma jc_zero : jc (0 : Mat n) = 0 := by simp [jc]

lemma jc_transpose (A : Mat n) : (jc A)ᵀ = jc Aᵀ := by
  simp [jc, transpose_mul, mul_assoc]

lemma continuous_jc : Continuous (jc : Mat n → Mat n) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

lemma cBar_add (A B : Mat n) : cBar (A + B) = cBar A + cBar B := by
  simp [cBar, mul_add, add_mul, transpose_add]; abel

lemma cBar_smul (c : ℝ) (A : Mat n) : cBar (c • A) = c • cBar A := by
  simp [cBar, Matrix.mul_smul, Matrix.smul_mul, transpose_smul]

lemma cBar_zero : cBar (0 : Mat n) = 0 := by simp [cBar]

/-- Entries of `jc A`. -/
lemma jc_entry (A : Mat n) (i j : Fin n ⊕ Fin n) :
    |jc A i j| = |A (i.swap) (j.swap)| := by
  have hJ : J₀ n = Matrix.fromBlocks 0 (-1) 1 0 := rfl
  rw [← fromBlocks_toBlocks A]
  rcases i with a | a <;> rcases j with b | b <;>
    simp [jc, hJ, fromBlocks_transpose, fromBlocks_multiply, Sum.swap]

lemma isSymLoop_jc {T : ℝ → Mat n} (h : IsSymLoop T) : IsSymLoop (fun t => jc (T t)) := by
  refine ⟨continuous_jc.comp h.1, fun t => by simp only [h.2.1 t], fun t => ?_⟩
  show (jc (T t))ᵀ = jc (T t)
  rw [jc_transpose, (h.2.2 t).eq]

lemma isAsymptoticTo_jc {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n}
    (h : IsAsymptoticTo S Splus Sminus) :
    IsAsymptoticTo (fun x => jc (S x)) (fun t => jc (Splus t)) (fun t => jc (Sminus t)) := by
  refine ⟨continuous_jc.comp h.1, fun s t => by simp only [h.2.1 s t], fun ε hε => ?_⟩
  obtain ⟨R, hR⟩ := h.2.2 ε hε
  have e : ∀ A B : Mat n, ∀ i j, |jc A i j - jc B i j| = |A i.swap j.swap - B i.swap j.swap| :=
    fun A B i j => by
      have : jc A - jc B = jc (A - B) := by simp only [jc]; noncomm_ring
      rw [← Matrix.sub_apply, ← Matrix.sub_apply, this, jc_entry]
  refine ⟨R, fun s t i j => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · rw [e]; exact (hR s t _ _).1 hs
  · rw [e]; exact (hR s t _ _).2 hs

lemma isNondegenerate_jc {T : ℝ → Mat n} (h : IsNondegenerate T) :
    IsNondegenerate (fun t => jc (T t)) := by
  intro Ψ hΨ
  letI : NormedRing (Mat n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat n) := Matrix.linftyOpNormedAlgebra
  set J := J₀ n
  have h1 : Jᵀ * J = 1 := J₀_transpose_mul_self
  have h2 : J * Jᵀ = 1 := J₀_mul_transpose_self
  have hfund : IsFundamentalSolution T (fun t => J * Ψ t * Jᵀ) := by
    refine ⟨by simp [hΨ.1, h2], fun t => ?_⟩
    have hd := ((hΨ.2 t).const_mul J).mul_const Jᵀ
    refine hd.congr_deriv ?_
    simp only [jc]
    calc J * (J * (Jᵀ * T t * J) * Ψ t) * Jᵀ = J * (J * Jᵀ) * T t * (J * Ψ t * Jᵀ) := by
          noncomm_ring
      _ = J * T t * (J * Ψ t * Jᵀ) := by rw [h2, mul_one]
  have hdet := h _ hfund
  intro h0
  apply hdet
  have : (1 : Mat n) - J * Ψ 1 * Jᵀ = J * (1 - Ψ 1) * Jᵀ := by
    rw [mul_sub, sub_mul, mul_one, h2]
  rw [this, det_mul, det_mul, h0, mul_zero, zero_mul]

/-- `jc (cBar (antilinearMat β)) = antilinearMat β̄`. -/
lemma jc_cBar_antilinearMat (β : ℂ) :
    jc (cBar (antilinearMat β)) = antilinearMat ((starRingEnd ℂ) β) := by
  have hJ : J₀ 1 = Matrix.fromBlocks 0 (-1) 1 0 := rfl
  have hC : conjMat 1 = Matrix.fromBlocks 1 0 0 (-1) := rfl
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [jc, cBar, hJ, hC, antilinearMat, fromBlocks_transpose, fromBlocks_multiply,
      Matrix.one_apply, Subsingleton.elim a b]

end

end CauchyRiemannIndex

/-!
# Helpers for `D_σ = D_S + σ β ·̄`: bounds, matrix maps on `W^{1,p}`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ}

/-! ### The antilinear matrix -/

lemma cBar_antilinearMat (b : ℂ) :
    cBar (antilinearMat b) = -antilinearMat ((starRingEnd ℂ) b) := by
  have hC : conjMat 1 = Matrix.fromBlocks 1 0 0 (-1) := rfl
  ext i j
  rcases i with a | a <;> rcases j with c | c <;>
    simp [cBar, hC, antilinearMat, fromBlocks_transpose, fromBlocks_multiply,
      Matrix.one_apply, Subsingleton.elim a c]

lemma antilinearMat_transpose (b : ℂ) : (antilinearMat b)ᵀ = antilinearMat b := by
  ext i j
  rcases i with a | a <;> rcases j with c | c <;>
    simp [antilinearMat, fromBlocks_transpose]

lemma antilinearMat_smul (σ : ℝ) (b : ℂ) : σ • antilinearMat b = antilinearMat (σ • b) := by
  ext i j
  rcases i with a | a <;> rcases j with c | c <;>
    simp [antilinearMat]

lemma continuous_antilinearMat : Continuous antilinearMat := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  rcases i with a | a <;> rcases j with c | c <;>
    simp only [antilinearMat, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, of_apply]
  · exact Complex.continuous_re
  · exact Complex.continuous_im
  · exact Complex.continuous_im
  · exact Complex.continuous_re.neg

lemma norm_antilinearMat_apply (b : ℂ) (v : Vec 1) :
    ‖Matrix.toEuclideanLin (antilinearMat b) v‖ = ‖b‖ * ‖v‖ := by
  have key : ‖Matrix.toEuclideanLin (antilinearMat b) v‖ ^ 2 = (‖b‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Complex.sq_norm,
      Complex.normSq_apply]
    simp [Fintype.sum_sum_type, toEuclideanLin_apply, antilinearMat, mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 key

/-! ### Boundedness -/

lemma lapc_beta_bound {β : ℝ × ℝ → ℂ} (hc : Continuous β) (hper : ∀ s t, β (s, t + 1) = β (s, t))
    (hends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖β x‖ ≤ M := by
  obtain ⟨R, c, hc0, h⟩ := hends
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hc.continuousOn
  have hc1 : 0 < 1 / c := by positivity
  have hCm := le_max_left C 0
  refine ⟨max C 0 + 1 / c, by positivity, fun ⟨s, t⟩ => ?_⟩
  by_cases hs : R ≤ |s|
  · have := (h s t hs).2
    have := le_max_right C 0
    linarith
  · rw [← crs_per hper s t]
    push_neg at hs
    have hmem : (s, Int.fract t) ∈ Set.Icc (-|R|) |R| ×ˢ Set.Icc (0 : ℝ) 1 :=
      ⟨abs_le.1 (hs.le.trans (le_abs_self R)), Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
    have := hC _ hmem
    linarith

/-- `S + σ · antilinearMat ∘ β` is continuous and bounded. -/
lemma lapc_Sσ_bound {S : ℝ × ℝ → Mat 1} {Splus Sminus : ℝ → Mat 1} (hSp : IsSymLoop Splus)
    (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) {β : ℝ × ℝ → ℂ}
    (hc : Continuous β) (hper : ∀ s t, β (s, t + 1) = β (s, t))
    (hends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (σ : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x (v : Vec 1),
      ‖Matrix.toEuclideanLin (S x + σ • antilinearMat (β x)) v‖ ≤ M * ‖v‖ := by
  obtain ⟨K, hK0, hK⟩ := crs_Sbound hSp hSm hS
  obtain ⟨B, hB0, hB⟩ := lapc_beta_bound hc hper hends
  refine ⟨K + |σ| * B, by positivity, fun x v => ?_⟩
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_antilinearMat_apply, Real.norm_eq_abs, add_mul]
  have := hK x v
  have h2 : |σ| * (‖β x‖ * ‖v‖) ≤ |σ| * B * ‖v‖ := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB x) (abs_nonneg σ))
      (norm_nonneg v)
  linarith

lemma lapc_Sσ_cont {S : ℝ × ℝ → Mat 1} (hS : Continuous S) {β : ℝ × ℝ → ℂ}
    (hc : Continuous β) (σ : ℝ) : Continuous fun x => S x + σ • antilinearMat (β x) :=
  hS.add ((continuous_antilinearMat.comp hc).const_smul σ)

/-! ### Constant matrices act on `W^{1,p}` -/

lemma IsTestSection.matMul (M : Mat n) {φ : ℝ × ℝ → Vec n} (hφ : IsTestSection φ) :
    IsTestSection (fun y => Matrix.toEuclideanLin M (φ y)) := by
  obtain ⟨R, hR⟩ := hφ.2.2
  refine ⟨(matCLM n M).contDiff.comp hφ.1, fun s t => by simp only [hφ.2.1], R,
    fun s t hs => by simp [hR s t hs]⟩

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- `(u, v, w) ↦ (M u, M v, M w)`. -/
def triMap (M : Mat n) : Triple n p →L[ℝ] Triple n p :=
  ((matCLM n M).compLpL p cylMeasure).prodMap
    (((matCLM n M).compLpL p cylMeasure).prodMap ((matCLM n M).compLpL p cylMeasure))

variable {p}

lemma triMap_fst (M : Mat n) (w : Triple n p) :
    ((triMap p M w).1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
      fun x => Matrix.toEuclideanLin M (w.1 x) :=
  ContinuousLinearMap.coeFn_compLpL (matCLM n M) w.1

lemma triMap_snd_fst (M : Mat n) (w : Triple n p) :
    ((triMap p M w).2.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
      fun x => Matrix.toEuclideanLin M (w.2.1 x) :=
  ContinuousLinearMap.coeFn_compLpL (matCLM n M) w.2.1

lemma triMap_snd_snd (M : Mat n) (w : Triple n p) :
    ((triMap p M w).2.2 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure]
      fun x => Matrix.toEuclideanLin M (w.2.2 x) :=
  ContinuousLinearMap.coeFn_compLpL (matCLM n M) w.2.2

lemma triMap_mem_W1p (M : Mat n) {w : Triple n p} (hw : w ∈ W1p p n) :
    triMap p M w ∈ W1p p n := by
  have hle : W1p p n ≤ (W1p p n).comap (triMap p M : Triple n p →ₗ[ℝ] Triple n p) := by
    have hcl : IsClosed ((W1p p n).comap
        (triMap p M : Triple n p →ₗ[ℝ] Triple n p) : Set (Triple n p)) :=
      (Submodule.isClosed_topologicalClosure _).preimage (triMap p M).continuous
    refine Submodule.topologicalClosure_minimal _ ?_ hcl
    rw [Submodule.span_le]
    rintro w ⟨u, hu, h1, h2, h3⟩
    show triMap p M w ∈ W1p p n
    refine Submodule.le_topologicalClosure _ (Submodule.subset_span
      ⟨fun y => Matrix.toEuclideanLin M (u y), hu.matMul M, ?_, ?_, ?_⟩)
    · filter_upwards [triMap_fst M w, h1] with x e1 e2
      rw [e1, e2]
    · filter_upwards [triMap_snd_fst M w, h2] with x e1 e2
      rw [e1, e2, partialS, partialS, fderiv_matCLM_comp M (hu.1.differentiable (by simp) x)]
    · filter_upwards [triMap_snd_snd M w, h3] with x e1 e2
      rw [e1, e2, partialT, partialT, fderiv_matCLM_comp M (hu.1.differentiable (by simp) x)]
  exact hle hw

/-- `D_{jc A}(J₀ᵀ w) = J₀ᵀ D_A w`. -/
lemma crApply_triMap_jc (A : ℝ × ℝ → Mat n) (w : Triple n p) :
    crApply (fun x => jc (A x)) (triMap p (J₀ n)ᵀ w) =ᵐ[cylMeasure]
      fun x => Matrix.toEuclideanLin (J₀ n)ᵀ (crApply A w x) := by
  filter_upwards [triMap_fst (J₀ n)ᵀ w, triMap_snd_fst (J₀ n)ᵀ w,
    triMap_snd_snd (J₀ n)ᵀ w] with x e1 e2 e3
  simp only [crApply]
  rw [e1, e2, e3, map_add, map_add]
  simp only [ckp_toEL_mul]
  rw [jc, J₀_transpose_comm, mul_assoc, mul_assoc, J₀_mul_transpose_self, mul_one]

end

end CauchyRiemannIndex

/-!
# The cross term `∫ ⟨∂̄u, β ū⟩` of `D_S + σ β ·̄`

For a test section `u` and smooth periodic `β`,
`2 ∫ ⟨∂ₛu + J₀∂ₜu, A(β) u⟩ = ∫ ⟨u, (-A(∂ₛβ) + J₀ A(∂ₜβ)) u⟩`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `antilinearMat` as an `ℝ`-linear map. -/
def alin : ℂ →ₗ[ℝ] Mat 1 where
  toFun := antilinearMat
  map_add' a b := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat] <;> ring
  map_smul' c b := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [antilinearMat]

/-- `b ↦ (v ↦ b v̄)` as a continuous linear map. -/
def alinCLM : ℂ →L[ℝ] (Vec 1 →L[ℝ] Vec 1) :=
  LinearMap.toContinuousLinearMap ((matCLM 1).comp alin)

lemma alinCLM_apply (b : ℂ) (v : Vec 1) :
    alinCLM b v = Matrix.toEuclideanLin (antilinearMat b) v := rfl

lemma J₀_antilinearMat (b : ℂ) : J₀ 1 * antilinearMat b = -(antilinearMat b * J₀ 1) := by
  have hJ : J₀ 1 = Matrix.fromBlocks 0 (-1) 1 0 := rfl
  ext i j
  rcases i with a | a <;> rcases j with c | c <;>
    simp [hJ, antilinearMat, fromBlocks_multiply, Subsingleton.elim a c]

lemma toEL_J₀_antilinearMat (b : ℂ) (w : Vec 1) :
    Matrix.toEuclideanLin (J₀ 1) (Matrix.toEuclideanLin (antilinearMat b) w) =
      -Matrix.toEuclideanLin (antilinearMat b) (Matrix.toEuclideanLin (J₀ 1) w) := by
  rw [ckp_toEL_mul, ckp_toEL_mul, J₀_antilinearMat, ckp_toEL_neg]

lemma norm_toEL_J₀ {n : ℕ} (w : Vec n) : ‖Matrix.toEuclideanLin (J₀ n) w‖ = ‖w‖ := by
  have h : ‖Matrix.toEuclideanLin (J₀ n) w‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_toEuclideanLin,
      ckp_toEL_mul, J₀_transpose_mul_self]
    simp [toEuclideanLin_apply]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

lemma inner_antilinearMat_comm (b : ℂ) (x y : Vec 1) :
    ⟪x, Matrix.toEuclideanLin (antilinearMat b) y⟫ = ⟪Matrix.toEuclideanLin (antilinearMat b) x, y⟫ := by
  rw [inner_toEuclideanLin, antilinearMat_transpose]

variable {β : ℝ × ℝ → ℂ} {u : ℝ × ℝ → Vec 1}

lemma lsf_test (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hu : IsTestSection u) :
    IsTestSection (fun x => Matrix.toEuclideanLin (antilinearMat (β x)) (u x)) := by
  obtain ⟨R, hR⟩ := hu.2.2
  refine ⟨(alinCLM.contDiff.comp hβ).clm_apply hu.1, fun s t => ?_, R, fun s t hs => ?_⟩
  · simp only [hβper, hu.2.1]
  · simp [hR s t hs]

lemma lsf_fderiv (hβ : ContDiff ℝ ∞ β) (hu : IsTestSection u) (x h : ℝ × ℝ) :
    fderiv ℝ (fun y => Matrix.toEuclideanLin (antilinearMat (β y)) (u y)) x h =
      Matrix.toEuclideanLin (antilinearMat (fderiv ℝ β x h)) (u x) +
        Matrix.toEuclideanLin (antilinearMat (β x)) (fderiv ℝ u x h) := by
  have hβd : DifferentiableAt ℝ β x := hβ.differentiable (by simp) x
  have hud : DifferentiableAt ℝ u x := hu.1.differentiable (by simp) x
  have e : (fun y => Matrix.toEuclideanLin (antilinearMat (β y)) (u y)) =
      fun y => (alinCLM ∘ β) y (u y) := rfl
  have hc : DifferentiableAt ℝ (alinCLM ∘ β) x := alinCLM.differentiableAt.comp x hβd
  rw [e, fderiv_clm_apply hc hud, fderiv_comp x alinCLM.differentiableAt hβd,
    ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, Function.comp_apply, alinCLM_apply]
  abel

/-- `∂̄ u = ∂ₛu + J₀ ∂ₜu`. -/
lemma crOp_zero_apply (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) :
    crOp (fun _ => (0 : Mat 1)) u x = partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x) := by
  simp [crOp]

/-- The curvature term `M u = -A(∂ₛβ) u + J₀ A(∂ₜβ) u`. -/
def lsfM (β : ℝ × ℝ → ℂ) (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) : Vec 1 :=
  -Matrix.toEuclideanLin (antilinearMat (fderiv ℝ β x (1, 0))) (u x) +
    Matrix.toEuclideanLin (J₀ 1) (Matrix.toEuclideanLin (antilinearMat (fderiv ℝ β x (0, 1))) (u x))

lemma lsf_integrable {f : ℝ × ℝ → ℝ} (hf : Continuous f) (R : ℝ)
    (hz : ∀ s t, R < |s| → f (s, t) = 0) : Integrable f cylMeasure := by
  rw [← memLp_one_iff_integrable]
  exact memLp_of_vanish f hf R hz

lemma continuous_lsfM (hβ : ContDiff ℝ ∞ β) (hu : IsTestSection u) : Continuous (lsfM β u) := by
  have hd : Continuous (fderiv ℝ β) := hβ.continuous_fderiv (by simp)
  have h1 : Continuous fun x => alinCLM (fderiv ℝ β x (1, 0)) :=
    alinCLM.continuous.comp (hd.clm_apply continuous_const)
  have h2 : Continuous fun x => alinCLM (fderiv ℝ β x (0, 1)) :=
    alinCLM.continuous.comp (hd.clm_apply continuous_const)
  exact (h1.clm_apply hu.continuous).neg.add
    ((matCLM 1 (J₀ 1)).continuous.comp (h2.clm_apply hu.continuous))

/-- The Weitzenböck identity for the cross term. -/
lemma lsf_cross (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hu : IsTestSection u) :
    2 * ∫ x, ⟪crOp (fun _ => (0 : Mat 1)) u x,
        Matrix.toEuclideanLin (antilinearMat (β x)) (u x)⟫ ∂cylMeasure =
      ∫ x, ⟪u x, lsfM β u x⟫ ∂cylMeasure := by
  set v : ℝ × ℝ → Vec 1 := fun x => Matrix.toEuclideanLin (antilinearMat (β x)) (u x) with hv
  have hvt : IsTestSection v := lsf_test hβ hβper hu
  have hA := crOp_formalAdjoint 1 (fun _ => (0 : Mat 1)) continuous_const u v hu hvt
  obtain ⟨R, hR⟩ := hu.2.2
  have hcD : Continuous fun x => crOp (fun _ => (0 : Mat 1)) u x := by
    have : (fun x => crOp (fun _ => (0 : Mat 1)) u x) =
        fun x => partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x) :=
      funext (crOp_zero_apply u)
    rw [this]
    exact hu.continuous_partialS.add ((matCLM 1 (J₀ 1)).continuous.comp hu.continuous_partialT)
  have hvc : Continuous v := hvt.continuous
  have hI1 : Integrable (fun x => ⟪crOp (fun _ => (0 : Mat 1)) u x, v x⟫) cylMeasure :=
    lsf_integrable (hcD.inner hvc) R fun s t hs => by simp [v, hR s t hs]
  have hI2 : Integrable (fun x => ⟪u x, lsfM β u x⟫) cylMeasure :=
    lsf_integrable (hu.continuous.inner (continuous_lsfM hβ hu)) R fun s t hs => by
      simp [hR s t hs]
  have hpt : ∀ x, ⟪u x, -partialS v x + Matrix.toEuclideanLin (J₀ 1) (partialT v x) +
      Matrix.toEuclideanLin ((fun _ => (0 : Mat 1)) x)ᵀ (v x)⟫ =
      ⟪u x, lsfM β u x⟫ - ⟪crOp (fun _ => (0 : Mat 1)) u x, v x⟫ := by
    intro x
    rw [partialS, partialT, lsf_fderiv hβ hu, lsf_fderiv hβ hu, crOp_zero_apply, lsfM]
    simp only [transpose_zero, map_zero, LinearMap.zero_apply, add_zero, map_add,
      toEL_J₀_antilinearMat]
    rw [show ⟪partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x), v x⟫ =
        ⟪u x, Matrix.toEuclideanLin (antilinearMat (β x))
          (partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x))⟫ by
      rw [inner_antilinearMat_comm, real_inner_comm]]
    rw [← inner_sub_right, partialS, partialT, map_add]
    congr 1
    abel
  have hA' : ∫ x, ⟪crOp (fun _ => (0 : Mat 1)) u x, v x⟫ ∂cylMeasure =
      ∫ x, ⟪u x, lsfM β u x⟫ ∂cylMeasure -
        ∫ x, ⟪crOp (fun _ => (0 : Mat 1)) u x, v x⟫ ∂cylMeasure := by
    have hs := integral_sub hI2 hI1
    rw [← hs, hA]
    exact integral_congr_ae (Eventually.of_forall hpt)
  linarith

/-- `⟨u, M u⟩ ≥ -2 C |u|²` when `‖Dβ‖ ≤ C`. -/
lemma lsf_M_bound {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C) (x : ℝ × ℝ) :
    -(2 * C * ‖u x‖ ^ 2) ≤ ⟪u x, lsfM β u x⟫ := by
  have h10 : ‖fderiv ℝ β x (1, 0)‖ ≤ C :=
    ((fderiv ℝ β x).le_opNorm _).trans (by simpa using hC x)
  have h01 : ‖fderiv ℝ β x (0, 1)‖ ≤ C :=
    ((fderiv ℝ β x).le_opNorm _).trans (by simpa using hC x)
  have hM : ‖lsfM β u x‖ ≤ 2 * C * ‖u x‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, norm_toEL_J₀, norm_antilinearMat_apply, norm_antilinearMat_apply]
    have := norm_nonneg (u x)
    nlinarith
  have := abs_real_inner_le_norm (u x) (lsfM β u x)
  have h2 : ‖u x‖ * ‖lsfM β u x‖ ≤ ‖u x‖ * (2 * C * ‖u x‖) :=
    mul_le_mul_of_nonneg_left hM (norm_nonneg _)
  have := neg_abs_le ⟪u x, lsfM β u x⟫
  nlinarith

end

end CauchyRiemannIndex

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff

noncomputable section

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

instance crs_complete : CompleteSpace (W1p p n) := by
  have h : IsClosed ((Submodule.span ℝ (testTriples n p)).topologicalClosure : Set (Triple n p)) :=
    Submodule.isClosed_topologicalClosure _
  exact h.completeSpace_coe

/-- The restriction to `[-R, R] × S¹` is compact on `W^{1,p}`. -/
lemma crs_compact (hp : 1 < p) (hp' : p ≠ ⊤) (R : ℝ) :
    IsCompactOperator ((crsK n p R).comp (W1p p n).subtypeL) := by
  set K0 := crsK n p R with hK0
  set K := K0.comp (W1p p n).subtypeL
  have key : IsCompact (closure ((K : W1p p n →ₗ[ℝ] Lp (Vec n) p (crsμ R)) ''
      Metric.ball 0 (1 / 4))) := by
    rw [isCompact_iff_isSeqCompact]
    intro y hy
    set e : ℕ → ℝ := fun k => (1 / 12 : ℝ) * (1 / ((k : ℝ) + 1)) with he
    have epos : ∀ k, 0 < e k := fun k => by simp only [he]; positivity
    have ele : ∀ k, e k ≤ 1 / 12 := fun k => by
      simp only [he]
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      nlinarith
    -- step 1: points of the ball
    have h1 : ∀ k, ∃ x : W1p p n, x ∈ Metric.ball 0 (1 / 4) ∧ dist (y k) (K x) < e k := by
      intro k
      obtain ⟨b, ⟨x, hx, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 (hy k) (e k) (epos k)
      exact ⟨x, hx, hb⟩
    choose x hx hxy using h1
    -- step 2: nearby test triples
    have h2 : ∀ k, ∃ v ∈ testTriples n p, dist (x k : Triple n p) v < e k := by
      intro k
      have hmem : (x k : Triple n p) ∈ closure (Submodule.span ℝ (testTriples n p) : Set _) := by
        rw [← Submodule.topologicalClosure_coe]; exact (x k).2
      obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.1 hmem (e k) (epos k)
      exact ⟨b, span_testTriples_subset hb, hd⟩
    choose v hv hxv using h2
    choose u hu hu1 hu2 hu3 using hv
    have hvn : ∀ k, ‖v k‖ ≤ 1 / 3 := by
      intro k
      have a1 : ‖(x k : Triple n p)‖ < 1 / 4 := by
        have := hx k
        rwa [mem_ball_zero_iff, Submodule.coe_norm] at this
      have a2 : ‖v k‖ ≤ ‖(x k : Triple n p)‖ + dist (x k : Triple n p) (v k) := by
        rw [dist_eq_norm]
        have := norm_sub_norm_le (v k) (x k : Triple n p)
        rw [norm_sub_rev] at this
        linarith
      linarith [hxv k, ele k]
    have hb : ∀ k, w1pNorm p (u k) ≤ 1 := by
      intro k
      refine (crs_w1p_le (hu1 k) (hu2 k) (hu3 k)).trans ?_
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by linarith [hvn k])
    obtain ⟨φ, hφ, hC⟩ :=
      compact_restriction n p hp hp' R u hu hb
    -- step 3: the restricted test triples are Cauchy
    set z : ℕ → Lp (Vec n) p (crsμ R) := fun i => K0 (v (φ i)) with hz
    have hdz : ∀ i j, dist (z i) (z j) =
        (eLpNorm (u (φ i) - u (φ j)) p (crsμ R)).toReal := by
      intro i j
      rw [Lp.dist_def]
      congr 1
      refine eLpNorm_congr_ae ?_
      filter_upwards [crsK_ae (p := p) R (v (φ i)), crsK_ae (p := p) R (v (φ j)),
        ae_restrict_of_ae (hu1 (φ i)), ae_restrict_of_ae (hu1 (φ j))] with t a1 a2 a3 a4
      simp only [Pi.sub_apply, hz]
      rw [hK0, a1, a2, a3, a4]
    have hcz : CauchySeq z := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hC (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
      refine ⟨N, fun i hi j hj => ?_⟩
      rw [hdz]
      exact ENNReal.toReal_lt_of_lt_ofReal (hN i hi j hj)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcz
    -- step 4: the original subsequence has the same limit
    have hdist : ∀ i, dist (z i) (y (φ i)) ≤ (1 + ‖K0‖) * e i := by
      intro i
      have d1 : dist (y (φ i)) (K (x (φ i))) < e (φ i) := hxy (φ i)
      have d2 : dist (K (x (φ i))) (z i) ≤ ‖K0‖ * e (φ i) := by
        change dist (K0 (x (φ i) : Triple n p)) (K0 (v (φ i))) ≤ _
        rw [dist_eq_norm, ← map_sub]
        refine (K0.le_opNorm _).trans ?_
        rw [← dist_eq_norm]
        exact mul_le_mul_of_nonneg_left (hxv (φ i)).le (norm_nonneg _)
      have emono : e (φ i) ≤ e i := by
        simp only [he]
        have : (i : ℝ) ≤ φ i := by exact_mod_cast hφ.id_le i
        gcongr
      calc dist (z i) (y (φ i)) ≤ dist (z i) (K (x (φ i))) + dist (K (x (φ i))) (y (φ i)) :=
            dist_triangle _ _ _
        _ ≤ ‖K0‖ * e (φ i) + e (φ i) := by
            rw [dist_comm (z i)]
            exact add_le_add d2 (by rw [dist_comm]; exact d1.le)
        _ ≤ (1 + ‖K0‖) * e i := by
            have := norm_nonneg K0
            nlinarith [epos (φ i)]
    have he0 : Tendsto e atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (1 / 12 : ℝ)
      rw [mul_zero] at this
      exact this
    have hd0 : Tendsto (fun i => dist (z i) (y (φ i))) atTop (𝓝 0) := by
      have := he0.const_mul (1 + ‖K0‖)
      rw [mul_zero] at this
      exact squeeze_zero (fun _ => dist_nonneg) hdist this
    have hyL : Tendsto (y ∘ φ) atTop (𝓝 L) := hL.congr_dist hd0
    exact ⟨L, isClosed_closure.mem_of_tendsto hyL (Eventually.of_forall fun i => hy (φ i)),
      φ, hφ, hyL⟩
  exact (isCompactOperator_iff_isCompact_closure_image_ball
    (K : W1p p n →ₗ[ℝ] Lp (Vec n) p (crsμ R)) (by norm_num)).2 key

end

end CauchyRiemannIndex

/-!
# Semi-Fredholm property of `D_S + σ β ·̄` for large `σ`

For test sections, `‖u‖_{W^{1,2}} ≤ c (‖D_σ u‖_{L²} + ‖u‖_{L²([-R,R] × S¹)})` once `σ` is large;
the restriction to `[-R, R] × S¹` is compact on `W^{1,2}`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma lsf_enorm_rpow_two (v : Vec 1) : ‖v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
    Real.rpow_two]

lemma lsf_eLpNorm_two {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Vec 1}
    (hf : Integrable (fun x => ‖f x‖ ^ 2) μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (√(∫ x, ‖f x‖ ^ 2 ∂μ)) := by
  have h1 : eLpNorm f 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, one_div]
    rw [ENNReal.rpow_inv_rpow (by norm_num)]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    simp_rw [lsf_enorm_rpow_two]
    rw [ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun _ => by positivity)]
  have h3 : eLpNorm f 2 μ = (eLpNorm f 2 μ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    rw [← ENNReal.rpow_mul]; norm_num
  rw [h3, h1, h2, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => by positivity)
    (by norm_num), Real.sqrt_eq_rpow]

lemma lsf_sqrt_bound {X A K L : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hX : X ≤ 2 * A + L * K) : √X ≤ √2 * √A + √L * √K := by
  refine (Real.sqrt_le_sqrt hX).trans ?_
  have e : 2 * A + L * K = (√2 * √A) ^ 2 + (√L * √K) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hA, Real.sq_sqrt hL,
      Real.sq_sqrt hK]
  have ha : 0 ≤ √2 * √A := by positivity
  have hb : 0 ≤ √L * √K := by positivity
  rw [e]
  calc √((√2 * √A) ^ 2 + (√L * √K) ^ 2) ≤ √((√2 * √A + √L * √K) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
    _ = √2 * √A + √L * √K := Real.sqrt_sq (by positivity)

variable {S : ℝ × ℝ → Mat 1} {β : ℝ × ℝ → ℂ}

/-- `D_σ u = ∂̄u + σ A(β) u + S u`. -/
lemma lsf_crOp_split (σ : ℝ) (u : ℝ × ℝ → Vec 1) (x : ℝ × ℝ) :
    crOp (fun x => S x + σ • antilinearMat (β x)) u x =
      crOp (fun _ => (0 : Mat 1)) u x +
        σ • Matrix.toEuclideanLin (antilinearMat (β x)) (u x) +
          Matrix.toEuclideanLin (S x) (u x) := by
  simp only [crOp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply, add_zero]
  abel

/-- The `L²` estimate on test sections, in squared form. -/
lemma lsf_est_sq (hSc : Continuous S) {K : ℝ}
    (hK : ∀ x (v : Vec 1), ‖Matrix.toEuclideanLin (S x) v‖ ≤ K * ‖v‖)
    (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    {C : ℝ} (hC : ∀ x, ‖fderiv ℝ β x‖ ≤ C) {R c : ℝ} (hc : 0 < c)
    (hends : ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖) {σ : ℝ} (hσ : 0 ≤ σ)
    (hcoef : 1 ≤ σ ^ 2 * c ^ 2 - 2 * σ * C - 2 * K ^ 2)
    {u : ℝ × ℝ → Vec 1} (hu : IsTestSection u) :
    let B := 2 * ∫ x, ‖crOp (fun x => S x + σ • antilinearMat (β x)) u x‖ ^ 2 ∂cylMeasure +
      σ ^ 2 * c ^ 2 * ∫ x, ‖u x‖ ^ 2 ∂(crsμ R)
    ∫ x, ‖u x‖ ^ 2 ∂cylMeasure ≤ B ∧ ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure ≤ B ∧
      ∫ x, ‖partialT u x‖ ^ 2 ∂cylMeasure ≤ B := by
  intro B
  obtain ⟨Ru, hRu⟩ := hu.2.2
  set D := crOp (fun x => S x + σ • antilinearMat (β x)) u with hD
  set Db := crOp (fun _ => (0 : Mat 1)) u with hDb
  set v : ℝ × ℝ → Vec 1 := fun x => Matrix.toEuclideanLin (antilinearMat (β x)) (u x) with hv
  set Kset : Set (ℝ × ℝ) := Set.Icc (-R) R ×ˢ Set.univ with hKset
  have hKm : MeasurableSet Kset := measurableSet_Icc.prod MeasurableSet.univ
  -- continuity
  have hcDb : Continuous Db := by
    have : Db = fun x => partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x) :=
      funext (crOp_zero_apply u)
    rw [this]
    exact hu.continuous_partialS.add ((matCLM 1 (J₀ 1)).continuous.comp hu.continuous_partialT)
  have hcv : Continuous v := (lsf_test hβ hβper hu).continuous
  have hcSu : Continuous fun x => Matrix.toEuclideanLin (S x) (u x) :=
    (continuous_matCLM.comp hSc).clm_apply hu.continuous
  have hDeq : D = fun x => Db x + σ • v x + Matrix.toEuclideanLin (S x) (u x) :=
    funext (lsf_crOp_split σ u)
  have hcD : Continuous D := by
    rw [hDeq]; exact (hcDb.add (hcv.const_smul σ)).add hcSu
  have hβc : Continuous β := hβ.continuous
  -- vanishing
  have z0 : ∀ s t, Ru < |s| → u (s, t) = 0 := hRu
  have zS : ∀ s t, Ru < |s| → partialS u (s, t) = 0 := fun s t hs => partialS_eq_zero Ru hRu hs
  have zT : ∀ s t, Ru < |s| → partialT u (s, t) = 0 := fun s t hs => partialT_eq_zero Ru hRu hs
  have zDb : ∀ s t, Ru < |s| → Db (s, t) = 0 := fun s t hs => by
    rw [hDb, crOp_zero_apply, zS s t hs, zT s t hs]; simp
  have zv : ∀ s t, Ru < |s| → v (s, t) = 0 := fun s t hs => by simp [v, z0 s t hs]
  have zD : ∀ s t, Ru < |s| → D (s, t) = 0 := fun s t hs => by
    rw [hDeq]; simp only []; rw [zDb s t hs, zv s t hs, z0 s t hs]; simp
  -- integrability
  have iu : Integrable (fun x => ‖u x‖ ^ 2) cylMeasure :=
    lsf_integrable (hu.continuous.norm.pow 2) Ru fun s t hs => by simp [z0 s t hs]
  have iS : Integrable (fun x => ‖partialS u x‖ ^ 2) cylMeasure :=
    lsf_integrable (hu.continuous_partialS.norm.pow 2) Ru fun s t hs => by simp [zS s t hs]
  have iT : Integrable (fun x => ‖partialT u x‖ ^ 2) cylMeasure :=
    lsf_integrable (hu.continuous_partialT.norm.pow 2) Ru fun s t hs => by simp [zT s t hs]
  have iDb : Integrable (fun x => ‖Db x‖ ^ 2) cylMeasure :=
    lsf_integrable (hcDb.norm.pow 2) Ru fun s t hs => by simp [zDb s t hs]
  have iD : Integrable (fun x => ‖D x‖ ^ 2) cylMeasure :=
    lsf_integrable (hcD.norm.pow 2) Ru fun s t hs => by simp [zD s t hs]
  have iβ : Integrable (fun x => ‖β x‖ ^ 2 * ‖u x‖ ^ 2) cylMeasure :=
    lsf_integrable ((hβc.norm.pow 2).mul (hu.continuous.norm.pow 2)) Ru fun s t hs => by
      simp [z0 s t hs]
  have iI : Integrable (fun x => ⟪Db x, v x⟫) cylMeasure :=
    lsf_integrable (hcDb.inner hcv) Ru fun s t hs => by simp [zDb s t hs]
  have iM : Integrable (fun x => ⟪u x, lsfM β u x⟫) cylMeasure :=
    lsf_integrable (hu.continuous.inner (continuous_lsfM hβ hu)) Ru fun s t hs => by
      simp [z0 s t hs]
  have iP : Integrable (fun x => ‖Db x + σ • v x‖ ^ 2) cylMeasure :=
    lsf_integrable ((hcDb.add (hcv.const_smul σ)).norm.pow 2) Ru fun s t hs => by
      simp [zDb s t hs, zv s t hs]
  have iK : Integrable (Kset.indicator fun x => ‖u x‖ ^ 2) cylMeasure := iu.indicator hKm
  -- named integrals
  set Iu := ∫ x, ‖u x‖ ^ 2 ∂cylMeasure
  set Is := ∫ x, ‖partialS u x‖ ^ 2 ∂cylMeasure
  set It := ∫ x, ‖partialT u x‖ ^ 2 ∂cylMeasure
  set IDb := ∫ x, ‖Db x‖ ^ 2 ∂cylMeasure
  set ID := ∫ x, ‖D x‖ ^ 2 ∂cylMeasure
  set Iβ := ∫ x, ‖β x‖ ^ 2 * ‖u x‖ ^ 2 ∂cylMeasure
  set Ic := ∫ x, ⟪Db x, v x⟫ ∂cylMeasure
  set IM := ∫ x, ⟪u x, lsfM β u x⟫ ∂cylMeasure
  set IP := ∫ x, ‖Db x + σ • v x‖ ^ 2 ∂cylMeasure
  set Ik := ∫ x, ‖u x‖ ^ 2 ∂(crsμ R)
  have hIk : Ik = ∫ x, Kset.indicator (fun x => ‖u x‖ ^ 2) x ∂cylMeasure := by
    rw [integral_indicator hKm]
  -- (E) energy identity
  have hE : IDb = Is + It := by
    have h := crOp_energy_identity 1 (fun _ => (0 : Mat 1)) continuous_const
      (fun _ => by simp [Matrix.IsSymm]) u hu
    simp only [map_zero, LinearMap.zero_apply, add_zero, norm_toEL_J₀] at h
    exact h
  -- (P) expansion of `‖∂̄u + σ A u‖²`
  have hP : IP = IDb + 2 * σ * Ic + σ ^ 2 * Iβ := by
    have e : (fun x => ‖Db x + σ • v x‖ ^ 2) =
        fun x => (‖Db x‖ ^ 2 + 2 * σ * ⟪Db x, v x⟫) + σ ^ 2 * (‖β x‖ ^ 2 * ‖u x‖ ^ 2) := by
      funext x
      rw [norm_add_sq_real, inner_smul_right, norm_smul, hv]
      simp only []
      rw [norm_antilinearMat_apply, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
      ring
    have j1 : Integrable (fun x => ‖Db x‖ ^ 2 + 2 * σ * ⟪Db x, v x⟫) cylMeasure :=
      iDb.add (iI.const_mul _)
    have j2 : Integrable (fun x => σ ^ 2 * (‖β x‖ ^ 2 * ‖u x‖ ^ 2)) cylMeasure := iβ.const_mul _
    have j3 : Integrable (fun x => 2 * σ * ⟪Db x, v x⟫) cylMeasure := iI.const_mul _
    simp only [IP, Ic, IDb, Iβ]
    rw [e, integral_add j1 j2, integral_add iDb j3, integral_const_mul, integral_const_mul]
  -- (Q) `‖∂̄u + σ A u‖² ≤ 2 ‖D u‖² + 2 K² ‖u‖²`
  have hQ : IP ≤ 2 * ID + 2 * K ^ 2 * Iu := by
    have hpt : ∀ x, ‖Db x + σ • v x‖ ^ 2 ≤ 2 * ‖D x‖ ^ 2 + 2 * K ^ 2 * ‖u x‖ ^ 2 := by
      intro x
      have e : Db x + σ • v x = D x - Matrix.toEuclideanLin (S x) (u x) := by
        rw [hDeq]; simp only []; abel
      have h1 : ‖Db x + σ • v x‖ ≤ ‖D x‖ + K * ‖u x‖ := by
        rw [e]; exact (norm_sub_le _ _).trans (by linarith [hK x (u x)])
      have h0 : 0 ≤ ‖Db x + σ • v x‖ := norm_nonneg _
      have h2 : ‖Db x + σ • v x‖ ^ 2 ≤ (‖D x‖ + K * ‖u x‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg (‖D x‖ - K * ‖u x‖)]
    have j1 : Integrable (fun x => 2 * ‖D x‖ ^ 2) cylMeasure := iD.const_mul 2
    have j2 : Integrable (fun x => 2 * K ^ 2 * ‖u x‖ ^ 2) cylMeasure := iu.const_mul _
    have j3 : Integrable (fun x => 2 * ‖D x‖ ^ 2 + 2 * K ^ 2 * ‖u x‖ ^ 2) cylMeasure := j1.add j2
    have := integral_mono iP j3 hpt
    rw [integral_add j1 j2, integral_const_mul, integral_const_mul] at this
    exact this
  -- (W) and (M): the cross term
  have hW : 2 * Ic = IM := lsf_cross hβ hβper hu
  have hM : -(2 * C * Iu) ≤ IM := by
    have j1 : Integrable (fun x => -(2 * C * ‖u x‖ ^ 2)) cylMeasure := (iu.const_mul (2 * C)).neg
    have := integral_mono j1 iM fun x => lsf_M_bound hC x
    rw [integral_neg, integral_const_mul] at this
    exact this
  -- (B) `c² ‖u‖² ≤ |β|² ‖u‖² + c² 1_K ‖u‖²`
  have hB : c ^ 2 * Iu ≤ Iβ + c ^ 2 * Ik := by
    have hpt : ∀ x, c ^ 2 * ‖u x‖ ^ 2 ≤
        ‖β x‖ ^ 2 * ‖u x‖ ^ 2 + c ^ 2 * Kset.indicator (fun x => ‖u x‖ ^ 2) x := by
      rintro ⟨s, t⟩
      by_cases hx : (s, t) ∈ Kset
      · rw [Set.indicator_of_mem hx]
        have := mul_nonneg (sq_nonneg ‖β (s, t)‖) (sq_nonneg ‖u (s, t)‖)
        linarith
      · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
        have hs : R ≤ |s| := by
          by_contra h
          push_neg at h
          exact hx ⟨abs_le.1 h.le, Set.mem_univ _⟩
        have h1 := hends s t hs
        have h2 : c ^ 2 ≤ ‖β (s, t)‖ ^ 2 := pow_le_pow_left₀ hc.le h1 2
        exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    have j1 : Integrable (fun x => c ^ 2 * Kset.indicator (fun x => ‖u x‖ ^ 2) x) cylMeasure :=
      iK.const_mul _
    have j2 : Integrable (fun x => ‖β x‖ ^ 2 * ‖u x‖ ^ 2 +
        c ^ 2 * Kset.indicator (fun x => ‖u x‖ ^ 2) x) cylMeasure := iβ.add j1
    have j3 : Integrable (fun x => c ^ 2 * ‖u x‖ ^ 2) cylMeasure := iu.const_mul _
    have := integral_mono j3 j2 hpt
    rw [integral_add iβ j1, integral_const_mul, integral_const_mul, ← hIk] at this
    exact this
  -- nonnegativity
  have hIu0 : 0 ≤ Iu := integral_nonneg fun _ => by positivity
  have hIs0 : 0 ≤ Is := integral_nonneg fun _ => by positivity
  have hIt0 : 0 ≤ It := integral_nonneg fun _ => by positivity
  -- combine
  have hσM : σ * (-(2 * C * Iu)) ≤ σ * IM := mul_le_mul_of_nonneg_left hM hσ
  have hσB : σ ^ 2 * (c ^ 2 * Iu) ≤ σ ^ 2 * (Iβ + c ^ 2 * Ik) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hcoefIu : Iu ≤ (σ ^ 2 * c ^ 2 - 2 * σ * C - 2 * K ^ 2) * Iu := by nlinarith
  have key : IDb + (σ ^ 2 * c ^ 2 - 2 * σ * C - 2 * K ^ 2) * Iu ≤
      2 * ID + σ ^ 2 * c ^ 2 * Ik := by
    nlinarith
  have hIDb0 : 0 ≤ IDb := integral_nonneg fun _ => by positivity
  have hB' : B = 2 * ID + σ ^ 2 * c ^ 2 * Ik := rfl
  refine ⟨?_, ?_, ?_⟩ <;> rw [hB'] <;> nlinarith

end

end CauchyRiemannIndex

/-!
# Semi-Fredholm property of `D_S + σ β ·̄` for large `σ`: assembly
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

lemma lsf_sq_int {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → Vec 1} (hf : MemLp f 2 μ) :
    Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf

theorem large_antilinear_semiFredholm_aux (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      IsClosed (crRange 2 (fun x => S x + σ • antilinearMat (β x)) : Set (LpCyl 1 2)) := by
  obtain ⟨K, hK0, hK⟩ := crs_Sbound hSplus hSminus hS
  obtain ⟨C, hC⟩ := hβC1
  obtain ⟨R, c, hc, hends⟩ := hβends
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨max 1 ((2 * C + 2 * K ^ 2 + 1) / c ^ 2), fun σ hσ => ?_⟩
  have hσ1 : 1 ≤ σ := le_trans (le_max_left _ _) hσ
  have hσ2 : (2 * C + 2 * K ^ 2 + 1) / c ^ 2 ≤ σ := le_trans (le_max_right _ _) hσ
  have hσc : 2 * C + 2 * K ^ 2 + 1 ≤ σ * c ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hσ2
  have hcoef : 1 ≤ σ ^ 2 * c ^ 2 - 2 * σ * C - 2 * K ^ 2 := by nlinarith
  set Sσ : ℝ × ℝ → Mat 1 := fun x => S x + σ • antilinearMat (β x) with hSσ
  set L : ℝ := σ ^ 2 * c ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  set cc : ℝ≥0 := Real.toNNReal (3 * (√2 + √L)) with hcc
  have hβc : Continuous β := hβ.continuous
  have hcσ : Continuous Sσ := lapc_Sσ_cont hS.1 hβc σ
  have hbσ := lapc_Sσ_bound hSplus hSminus hS hβc hβper ⟨R, c, hc, hends⟩ σ
  /- the estimate on test sections -/
  have hest : ∀ u : ℝ × ℝ → Vec 1, IsTestSection u →
      w1pNorm 2 u ≤ cc * eLpNorm (crOp Sσ u) 2 cylMeasure + cc * eLpNorm u 2 (crsμ R) := by
    intro u hu
    obtain ⟨h1, h2, h3⟩ := lsf_est_sq hS.1 hK hβ hβper hC hc (fun s t hs => (hends s t hs).1)
      (by linarith) hcoef hu
    obtain ⟨Ru, hRu⟩ := hu.2.2
    have hcD : Continuous (crOp Sσ u) := by
      have e : crOp Sσ u = fun x => partialS u x + Matrix.toEuclideanLin (J₀ 1) (partialT u x) +
          Matrix.toEuclideanLin (Sσ x) (u x) := rfl
      rw [e]
      exact (hu.continuous_partialS.add
        ((matCLM 1 (J₀ 1)).continuous.comp hu.continuous_partialT)).add
        ((continuous_matCLM.comp hcσ).clm_apply hu.continuous)
    have mD : MemLp (crOp Sσ u) 2 cylMeasure := memLp_of_vanish _ hcD Ru fun s t hs => by
      simp [crOp, partialS_eq_zero Ru hRu hs, partialT_eq_zero Ru hRu hs, hRu s t hs]
    have mu : MemLp u 2 cylMeasure := hu.memLp
    rw [w1pNorm, lsf_eLpNorm_two (lsf_sq_int mu), lsf_eLpNorm_two (lsf_sq_int hu.memLp_partialS),
      lsf_eLpNorm_two (lsf_sq_int hu.memLp_partialT), lsf_eLpNorm_two (lsf_sq_int mD),
      lsf_eLpNorm_two (lsf_sq_int (mu.restrict _))]
    set ID := ∫ x, ‖crOp Sσ u x‖ ^ 2 ∂cylMeasure
    set Ik := ∫ x, ‖u x‖ ^ 2 ∂(crsμ R)
    have hID : 0 ≤ ID := integral_nonneg fun _ => by positivity
    have hIk : 0 ≤ Ik := integral_nonneg fun _ => by positivity
    have b1 := lsf_sqrt_bound hID hIk hL0 h1
    have b2 := lsf_sqrt_bound hID hIk hL0 h2
    have b3 := lsf_sqrt_bound hID hIk hL0 h3
    have hs2 : 0 ≤ √2 := Real.sqrt_nonneg _
    have hsL : 0 ≤ √L := Real.sqrt_nonneg _
    have hsD : 0 ≤ √ID := Real.sqrt_nonneg _
    have hsk : 0 ≤ √Ik := Real.sqrt_nonneg _
    have hccr : ((cc : ℝ≥0∞)) = ENNReal.ofReal (3 * (√2 + √L)) := by
      rfl
    rw [hccr, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [mul_nonneg hs2 hsD, mul_nonneg hsL hsk, mul_nonneg hsL hsD, mul_nonneg hs2 hsk]
  /- the abstract semi-Fredholm argument -/
  set T : W1p 2 1 →L[ℝ] LpCyl 1 2 := (crsT Sσ hcσ hbσ).comp (W1p 2 1).subtypeL with hT
  set Kc := (crsK 1 2 R).comp (W1p 2 1).subtypeL with hKc
  have hest' : ∀ x : W1p 2 1, ‖x‖ ≤ (cc : ℝ) * ‖T x‖ + (cc : ℝ) * ‖Kc x‖ := fun x =>
    crs_estimate Sσ hcσ hbσ R cc hest x x.2
  obtain ⟨hfin, hcl⟩ := finiteDimensional_ker_isClosed_range_of_estimate T Kc
    (crs_compact (by norm_num) (by norm_num) R) cc hest'
  constructor
  · have hle : crKernel 2 Sσ ≤ (LinearMap.ker (T : W1p 2 1 →ₗ[ℝ] LpCyl 1 2)).map
        (W1p 2 1).subtype := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨hw, hz⟩
      refine ⟨⟨w, hw⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      apply Lp.ext
      exact (crsT_ae Sσ hcσ hbσ w).trans (hz.trans (Lp.coeFn_zero _ _ _).symm)
    exact Submodule.finiteDimensional_of_le hle
  · have he : (crRange 2 Sσ : Set (LpCyl 1 2)) = Set.range T := by
      apply Set.Subset.antisymm
      · have : crRange 2 Sσ ≤ LinearMap.range (T : W1p 2 1 →ₗ[ℝ] LpCyl 1 2) := by
          refine Submodule.span_le.2 ?_
          rintro f ⟨w, hw, hf⟩
          refine ⟨⟨w, hw⟩, ?_⟩
          apply Lp.ext
          exact (crsT_ae Sσ hcσ hbσ w).trans hf.symm
        intro f hf
        obtain ⟨x, hx⟩ := this hf
        exact ⟨x, hx⟩
      · rintro f ⟨x, rfl⟩
        refine Submodule.subset_span ⟨(x : Triple 1 2), x.2, ?_⟩
        show (⇑(crsT Sσ hcσ hbσ (x : Triple 1 2)) : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] _
        exact crsT_ae Sσ hcσ hbσ (x : Triple 1 2)
    rw [he]
    exact hcl

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀,
      FiniteDimensional ℝ (crKernel 2 (fun x => S x + σ • antilinearMat (β x))) ∧
      IsClosed (crRange 2 (fun x => S x + σ • antilinearMat (β x)) : Set (LpCyl 1 2)) :=
  large_antilinear_semiFredholm_aux Splus Sminus hSplus hSminus S hS β hβ hβper hβC1 hβends
