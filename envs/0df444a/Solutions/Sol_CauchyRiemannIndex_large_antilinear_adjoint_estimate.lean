-- Prove2me | solution 1 for CauchyRiemannIndex.large_antilinear_adjoint_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:03:30.665495+00:00
-- url     : https://prove2.me/submissions/408fbe44-eab6-40ab-ab00-e330857f0c7e

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
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Theorems.Thm_CauchyRiemannIndex_global_estimate
import Theorems.Thm_CauchyRiemannIndex_compact_restriction
import Theorems.Thm_CauchyRiemannIndex_finiteDimensional_ker_isClosed_range_of_estimate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Theorems.Thm_CauchyRiemannIndex_antilinear_adjoint_energy_identity
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Group.Bounded



/-!
# Pointwise algebra of `antilinearMat β` and `J₀` on `ℝ² = ℂ`
-/

namespace CauchyRiemannIndex

open Matrix
open scoped RealInnerProductSpace

noncomputable section


lemma lap_inner (v w : Vec 1) : ⟪v, w⟫ = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) * w (Sum.inl 0 : Fin 1 ⊕ Fin 1) + v (Sum.inr 0 : Fin 1 ⊕ Fin 1) * w (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fintype.sum_sum_type, mul_comm]

lemma lap_norm_sq (v : Vec 1) : ‖v‖ ^ 2 = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) ^ 2 + v (Sum.inr 0 : Fin 1 ⊕ Fin 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lap_inner]; ring

lemma lap_alm_1 (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v (Sum.inl 0 : Fin 1 ⊕ Fin 1) = b.re * v (Sum.inl 0 : Fin 1 ⊕ Fin 1) + b.im * v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

lemma lap_alm_2 (b : ℂ) (v : Vec 1) :
    Matrix.toEuclideanLin (antilinearMat b) v (Sum.inr 0 : Fin 1 ⊕ Fin 1) = b.im * v (Sum.inl 0 : Fin 1 ⊕ Fin 1) - b.re * v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, antilinearMat, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]
  ring

lemma lap_J_1 (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v (Sum.inl 0 : Fin 1 ⊕ Fin 1) = -v (Sum.inr 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma lap_J_2 (v : Vec 1) : Matrix.toEuclideanLin (J₀ 1) v (Sum.inr 0 : Fin 1 ⊕ Fin 1) = v (Sum.inl 0 : Fin 1 ⊕ Fin 1) := by
  simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

lemma lap_alm_transpose (b : ℂ) : (antilinearMat b)ᵀ = antilinearMat b := by
  simp only [antilinearMat, Matrix.fromBlocks_transpose]
  congr 1 <;> (ext; simp)

lemma lap_alm_add (b c : ℂ) : antilinearMat (b + c) = antilinearMat b + antilinearMat c := by
  simp only [antilinearMat, Complex.add_re, Complex.add_im, neg_add, Matrix.fromBlocks_add]
  congr 1 <;> (ext; simp)

lemma lap_alm_smul (c : ℝ) (b : ℂ) : antilinearMat ((c : ℂ) * b) = c • antilinearMat b := by
  simp only [antilinearMat, Complex.re_ofReal_mul, Complex.im_ofReal_mul, Matrix.fromBlocks_smul]
  congr 1 <;> (ext; simp)

lemma lap_inner_alm_sym (b : ℂ) (v w : Vec 1) :
    ⟪Matrix.toEuclideanLin (antilinearMat b) v, w⟫ =
      ⟪v, Matrix.toEuclideanLin (antilinearMat b) w⟫ := by
  rw [lap_inner, lap_inner, lap_alm_1, lap_alm_2, lap_alm_1, lap_alm_2]; ring

lemma lap_norm_alm_sq (b : ℂ) (v : Vec 1) :
    ‖Matrix.toEuclideanLin (antilinearMat b) v‖ ^ 2 = ‖b‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [lap_norm_sq, lap_norm_sq, lap_alm_1, lap_alm_2, Complex.sq_norm, Complex.normSq_apply]
  ring

lemma lap_inner_J_alm (b : ℂ) (a w : Vec 1) :
    ⟪Matrix.toEuclideanLin (J₀ 1) a, Matrix.toEuclideanLin (antilinearMat b) w⟫ =
      -⟪a, Matrix.toEuclideanLin (antilinearMat (Complex.I * b)) w⟫ := by
  rw [lap_inner, lap_inner, lap_J_1, lap_J_2, lap_alm_1, lap_alm_2, lap_alm_1, lap_alm_2]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

lemma lap_inner_alm_self_le (b : ℂ) (v : Vec 1) :
    |⟪v, Matrix.toEuclideanLin (antilinearMat b) v⟫| ≤ ‖b‖ * ‖v‖ ^ 2 := by
  calc |⟪v, Matrix.toEuclideanLin (antilinearMat b) v⟫|
      ≤ ‖v‖ * ‖Matrix.toEuclideanLin (antilinearMat b) v‖ := abs_real_inner_le_norm _ _
    _ = ‖b‖ * ‖v‖ ^ 2 := by
      have h := lap_norm_alm_sq b v
      have h' : ‖Matrix.toEuclideanLin (antilinearMat b) v‖ = ‖b‖ * ‖v‖ := by
        rw [← Real.sqrt_sq (norm_nonneg _), h, ← mul_pow, Real.sqrt_sq (by positivity)]
      rw [h']; ring

lemma lap_norm_J (v : Vec 1) : ‖Matrix.toEuclideanLin (J₀ 1) v‖ = ‖v‖ := by
  have h : ‖Matrix.toEuclideanLin (J₀ 1) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [lap_norm_sq, lap_norm_sq, lap_J_1, lap_J_2]; ring
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin (J₀ 1) v)), h,
    Real.sqrt_sq (norm_nonneg _)]

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
# Calculus helpers for the antilinear term on the cylinder
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `β ↦ A(β)` as a real-linear map. -/
def almL : ℂ →ₗ[ℝ] Mat 1 where
  toFun := antilinearMat
  map_add' := lap_alm_add
  map_smul' c b := by
    rw [RingHom.id_apply, ← lap_alm_smul, Complex.real_smul]

/-- `β ↦ (v ↦ A(β) v)` as a continuous real-linear map. -/
def almK : ℂ →L[ℝ] (Vec 1 →L[ℝ] Vec 1) :=
  LinearMap.toContinuousLinearMap (matCLM 1 ∘ₗ almL)

lemma almK_apply (b : ℂ) (v : Vec 1) :
    almK b v = Matrix.toEuclideanLin (antilinearMat b) v := rfl

/-- `∂ₛβ`. -/
def dS (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (1, 0)

/-- `∂ₜβ`. -/
def dT (β : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ℂ := fderiv ℝ β x (0, 1)

lemma hasDerivAt_slice_s {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × ℝ → E} (hu : Differentiable ℝ u) (s t : ℝ) :
    HasDerivAt (fun s => u (s, t)) (fderiv ℝ u (s, t) (1, 0)) s := by
  have h1 : HasDerivAt (fun s : ℝ => (s, t)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s t)
  exact (hu (s, t)).hasFDerivAt.comp_hasDerivAt s h1

lemma hasDerivAt_slice_t {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ × ℝ → E} (hu : Differentiable ℝ u) (s t : ℝ) :
    HasDerivAt (fun t => u (s, t)) (fderiv ℝ u (s, t) (0, 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t :=
    (hasDerivAt_const t s).prodMk (hasDerivAt_id t)
  exact (hu (s, t)).hasFDerivAt.comp_hasDerivAt t h1

/-- `∫ g = 0` over the cylinder when `g = ∂ₛF` slice-wise, with `g` continuous and both `g` and
`F` vanishing for large `|s|`. -/
lemma lap_integral_s_eq_zero (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
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

/-- `∫ g = 0` over the cylinder when `g = ∂ₜF` slice-wise, `F` is `1`-periodic in `t`, and `g`
is continuous and vanishes for large `|s|`. -/
lemma integral_t_eq_zero_of_hasDerivAt (g F : ℝ × ℝ → ℝ) (hg : Continuous g) (R : ℝ)
    (hgR : ∀ s t, R < |s| → g (s, t) = 0) (hper : ∀ s t, F (s, t + 1) = F (s, t))
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
    have := hper s 0
    simp only [zero_add] at this
    rw [this, sub_self]
  simp [h]

lemma lap_integrable {F : ℝ × ℝ → ℝ} (hF : Continuous F) (R : ℝ)
    (hR : ∀ s t, R < |s| → F (s, t) = 0) : Integrable F cylMeasure := by
  rw [← memLp_one_iff_integrable]
  exact memLp_of_vanish F hF R hR

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

/-!
# The adjoint estimate `‖φ‖₂ ≤ ‖D_σ^* φ‖₂` for large `σ` when all zeros of `β` are positive
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `∫ (∂ₛh - h²) |φ|² ≤ ∫ |∂ₛφ|²` for a weight `h` that is `C¹` in `s`. -/
lemma lap_weighted (h hs : ℝ × ℝ → ℝ) (hc : Continuous h) (hsc : Continuous hs)
    (hd : ∀ s t, HasDerivAt (fun s => h (s, t)) (hs (s, t)) s) {n : ℕ} (φ : ℝ × ℝ → Vec n)
    (hφ : IsTestSection φ) :
    ∫ x, (hs x - h x ^ 2) * ‖φ x‖ ^ 2 ∂cylMeasure ≤ ∫ x, ‖partialS φ x‖ ^ 2 ∂cylMeasure := by
  obtain ⟨R, hR⟩ := hφ.2.2
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hS0 : ∀ s t, R < |s| → partialS φ (s, t) = 0 := fun s t hs => partialS_eq_zero R hR hs
  have hφc := hφ.continuous
  have hSc := hφ.continuous_partialS
  have vanish : ∀ (F : ℝ × ℝ → ℝ), Continuous F → (∀ s t, R < |s| → F (s, t) = 0) →
      Integrable F cylMeasure := fun F hF h => lap_integrable hF R h
  have i1 := vanish (fun x => ‖partialS φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hS0 s t hs]
  have i2 := vanish (fun x => h x * ⟪partialS φ x, φ x⟫) (hc.mul (hSc.inner hφc))
    fun s t hs => by simp [hS0 s t hs]
  have i3 := vanish (fun x => h x ^ 2 * ‖φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hR s t hs]
  have i4 := vanish (fun x => hs x * ‖φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hR s t hs]
  -- `∫ ∂ₛ(h |φ|²) = 0`
  have hF : ∀ s t, HasDerivAt (fun s => h (s, t) * ⟪φ (s, t), φ (s, t)⟫)
      (hs (s, t) * ‖φ (s, t)‖ ^ 2 + 2 * (h (s, t) * ⟪partialS φ (s, t), φ (s, t)⟫)) s := by
    intro s t
    have h1 := hasDerivAt_slice_s hφd s t
    have h2 := (hd s t).mul (h1.inner ℝ h1)
    refine h2.congr_deriv ?_
    unfold partialS
    rw [real_inner_comm (φ (s, t)) (fderiv ℝ φ (s, t) (1, 0)), real_inner_self_eq_norm_sq]
    ring
  have hI := lap_integral_s_eq_zero
    (fun x => hs x * ‖φ x‖ ^ 2 + 2 * (h x * ⟪partialS φ x, φ x⟫))
    (fun x => h x * ⟪φ x, φ x⟫) (by fun_prop) R
    (fun s t hs => by simp [hS0 s t hs, hR s t hs]) (fun s t hs => by simp [hR s t hs]) hF
  rw [integral_add i4 (i2.const_mul 2), integral_const_mul] at hI
  have hpt : ∀ x, ‖partialS φ x + h x • φ x‖ ^ 2 =
      ‖partialS φ x‖ ^ 2 + 2 * (h x * ⟪partialS φ x, φ x⟫) + h x ^ 2 * ‖φ x‖ ^ 2 := by
    intro x
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h0 : 0 ≤ ∫ x, ‖partialS φ x + h x • φ x‖ ^ 2 ∂cylMeasure :=
    integral_nonneg fun x => by positivity
  simp_rw [hpt] at h0
  have j1 : Integrable (fun x => ‖partialS φ x‖ ^ 2 + 2 * (h x * ⟪partialS φ x, φ x⟫)) cylMeasure :=
    i1.add (i2.const_mul 2)
  rw [integral_add j1 i3, integral_add i1 (i2.const_mul 2), integral_const_mul] at h0
  have e : ∫ x, (hs x - h x ^ 2) * ‖φ x‖ ^ 2 ∂cylMeasure =
      ∫ x, hs x * ‖φ x‖ ^ 2 ∂cylMeasure - ∫ x, h x ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure := by
    rw [← integral_sub i4 i3]; congr 1; funext x; ring
  rw [e]
  linarith

lemma lap_transpose_asymptotic {n : ℕ} {S : ℝ × ℝ → Mat n} {Splus Sminus : ℝ → Mat n}
    (hSp : IsSymLoop Splus) (hSm : IsSymLoop Sminus) (hS : IsAsymptoticTo S Splus Sminus) :
    IsAsymptoticTo (fun x => (S x)ᵀ) Splus Sminus := by
  refine ⟨hS.1.matrix_transpose, fun s t => by simp only [hS.2.1], fun ε hε => ?_⟩
  obtain ⟨R, hR⟩ := hS.2.2 ε hε
  refine ⟨R, fun s t i j => ?_⟩
  have h := hR s t j i
  simp only [Matrix.transpose_apply]
  rw [← (hSp.2.2 t).apply i j, ← (hSm.2.2 t).apply i j]
  exact h

lemma lap_ae_strip : ∀ᵐ x ∂cylMeasure, x.2 ∈ Set.Ico (0 : ℝ) 1 := by
  have hm : MeasurableSet (Set.univ ×ˢ Set.Ico (0 : ℝ) 1 : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ico
  filter_upwards [ae_restrict_mem hm] with x hx using hx.2

/-- The adjoint estimate from the weight `g` adapted to the zeros of `β`. -/
theorem lap_est_of_geom (Splus Sminus : ℝ → Mat 1) (hSplus : IsSymLoop Splus)
    (hSminus : IsSymLoop Sminus) (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hgeom : ∃ (g gs : ℝ × ℝ → ℝ) (K : ℝ), 0 ≤ K ∧ Continuous g ∧ Continuous gs ∧
      (∀ s t, HasDerivAt (fun s => g (s, t)) (gs (s, t)) s) ∧
      ∀ x : ℝ × ℝ, x.2 ∈ Set.Ico (0 : ℝ) 1 → |g x| ≤ ‖β x‖ ∧ 1 - K * ‖β x‖ ^ 2 ≤ gs x ∧
        ‖dS β x + Complex.I * dT β x‖ ≤ K * ‖β x‖ ^ 2) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ φ : ℝ × ℝ → Vec 1, IsTestSection φ →
      ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
          Matrix.toEuclideanLin (S x + σ • antilinearMat (β x))ᵀ (φ x)‖ ^ 2 ∂cylMeasure := by
  obtain ⟨g, gs, K, hK, hgc, hgsc, hgd, hpt⟩ := hgeom
  obtain ⟨M, hM0, hM⟩ := crs_Sbound hSplus hSminus (lap_transpose_asymptotic hSplus hSminus hS)
  refine ⟨max (2 * K) (4 * (M ^ 2 + 1)), fun σ hσ φ hφ => ?_⟩
  have hσK : 2 * K ≤ σ := (le_max_left _ _).trans hσ
  have hσM : 4 * (M ^ 2 + 1) ≤ σ := (le_max_right _ _).trans hσ
  have hσ0 : 0 ≤ σ := by nlinarith
  obtain ⟨R, hR⟩ := hφ.2.2
  have hS0 : ∀ s t, R < |s| → partialS φ (s, t) = 0 := fun s t hs => partialS_eq_zero R hR hs
  have hT0 : ∀ s t, R < |s| → partialT φ (s, t) = 0 := fun s t hs => partialT_eq_zero R hR hs
  have hφc := hφ.continuous
  have hSc := hφ.continuous_partialS
  have hTc := hφ.continuous_partialT
  have hβc : Continuous β := hβ.continuous
  have hdS : Continuous (dS β) := (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdT : Continuous (dT β) := (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
  have vanish : ∀ (F : ℝ × ℝ → ℝ), Continuous F → (∀ s t, R < |s| → F (s, t) = 0) →
      Integrable F cylMeasure := fun F hF h => lap_integrable hF R h
  set X : ℝ × ℝ → Vec 1 := fun x => -partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
    Matrix.toEuclideanLin (σ • antilinearMat (β x)) (φ x) with hXdef
  set Y : ℝ × ℝ → Vec 1 := fun x => Matrix.toEuclideanLin (S x)ᵀ (φ x) with hYdef
  have hXc : Continuous X := by
    have : Continuous fun x => matCLM 1 (σ • antilinearMat (β x)) := by
      have e : (fun x => matCLM 1 (σ • antilinearMat (β x))) = fun x => σ • almK (β x) := by
        funext x; ext v; simp [matCLM_apply, almK_apply]
      rw [e]; exact (almK.continuous.comp hβc).const_smul σ
    exact ((hSc.neg).add ((matCLM 1 (J₀ 1)).continuous.comp hTc)).add (this.clm_apply hφc)
  have hYc : Continuous Y :=
    (continuous_matCLM.comp hS.1.matrix_transpose).clm_apply hφc
  have hadj : ∀ x, -partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
      Matrix.toEuclideanLin (S x + σ • antilinearMat (β x))ᵀ (φ x) = X x + Y x := by
    intro x
    simp only [hXdef, hYdef, Matrix.transpose_add, Matrix.transpose_smul, lap_alm_transpose,
      map_add, LinearMap.add_apply]
    abel
  simp_rw [hadj]
  -- step 1: `∫ |X|² ≥ (σ/2) ∫ |φ|²`
  have hW : ∫ x, ‖X x‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS φ x‖ ^ 2 ∂cylMeasure + ∫ x, ‖partialT φ x‖ ^ 2 ∂cylMeasure +
        σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ * ∫ x, ⟪φ x, Matrix.toEuclideanLin (antilinearMat (dS β x + Complex.I * dT β x))
          (φ x)⟫ ∂cylMeasure :=
    antilinear_adjoint_energy_identity β hβ hβper σ φ hφ
  have hwt := lap_weighted (fun x => σ / 2 * g x) (fun x => σ / 2 * gs x)
    (continuous_const.mul hgc) (continuous_const.mul hgsc)
    (fun s t => (hgd s t).const_mul (σ / 2)) φ hφ
  have iN := vanish (fun x => ‖φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hR s t hs]
  have iT := vanish (fun x => ‖partialT φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hT0 s t hs]
  have iB := vanish (fun x => ‖β x‖ ^ 2 * ‖φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hR s t hs]
  have iMM := vanish (fun x => ⟪φ x, Matrix.toEuclideanLin
      (antilinearMat (dS β x + Complex.I * dT β x)) (φ x)⟫)
    (hφc.inner ((almK.continuous.comp (hdS.add (continuous_const.mul hdT))).clm_apply hφc))
    fun s t hs => by simp [hR s t hs]
  have iWt := vanish (fun x => (σ / 2 * gs x - (σ / 2 * g x) ^ 2) * ‖φ x‖ ^ 2) (by fun_prop)
    fun s t hs => by simp [hR s t hs]
  have hAt : 0 ≤ ∫ x, ‖partialT φ x‖ ^ 2 ∂cylMeasure := integral_nonneg fun x => by positivity
  have hstep1 : σ / 2 * ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤ ∫ x, ‖X x‖ ^ 2 ∂cylMeasure := by
    have hsum : ∫ x, (σ / 2 * gs x - (σ / 2 * g x) ^ 2) * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ * ∫ x, ⟪φ x, Matrix.toEuclideanLin (antilinearMat (dS β x + Complex.I * dT β x))
          (φ x)⟫ ∂cylMeasure =
        ∫ x, ((σ / 2 * gs x - (σ / 2 * g x) ^ 2) * ‖φ x‖ ^ 2 +
          σ ^ 2 * (‖β x‖ ^ 2 * ‖φ x‖ ^ 2) + σ * ⟪φ x, Matrix.toEuclideanLin
            (antilinearMat (dS β x + Complex.I * dT β x)) (φ x)⟫) ∂cylMeasure := by
      have j1 : Integrable (fun x => (σ / 2 * gs x - (σ / 2 * g x) ^ 2) * ‖φ x‖ ^ 2 +
          σ ^ 2 * (‖β x‖ ^ 2 * ‖φ x‖ ^ 2)) cylMeasure := iWt.add (iB.const_mul _)
      rw [integral_add j1 (iMM.const_mul _), integral_add iWt (iB.const_mul _),
        integral_const_mul, integral_const_mul]
    have hmono : σ / 2 * ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        ∫ x, ((σ / 2 * gs x - (σ / 2 * g x) ^ 2) * ‖φ x‖ ^ 2 +
          σ ^ 2 * (‖β x‖ ^ 2 * ‖φ x‖ ^ 2) + σ * ⟪φ x, Matrix.toEuclideanLin
            (antilinearMat (dS β x + Complex.I * dT β x)) (φ x)⟫) ∂cylMeasure := by
      rw [← integral_const_mul]
      refine integral_mono_ae (iN.const_mul _) ((iWt.add (iB.const_mul _)).add
        (iMM.const_mul _)) ?_
      filter_upwards [lap_ae_strip] with x hx
      obtain ⟨h1, h2, h3⟩ := hpt x hx
      have hm := lap_inner_alm_self_le (dS β x + Complex.I * dT β x) (φ x)
      have hm' := (abs_le.1 hm).1
      set b := ‖β x‖
      set v := ‖φ x‖ ^ 2
      set m := ⟪φ x, Matrix.toEuclideanLin (antilinearMat (dS β x + Complex.I * dT β x)) (φ x)⟫
      have hv : 0 ≤ v := by positivity
      have hg2 : g x ^ 2 ≤ b ^ 2 := by
        have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2; simpa using this
      have hmK : -(K * b ^ 2 * v) ≤ m := by
        have : ‖dS β x + Complex.I * dT β x‖ * v ≤ K * b ^ 2 * v :=
          mul_le_mul_of_nonneg_right h3 hv
        linarith
      have e1 : σ / 2 * gs x * v ≥ σ / 2 * (1 - K * b ^ 2) * v := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ σ / 2)
        exact mul_le_mul_of_nonneg_right this hv
      have e2 : (σ / 2 * g x) ^ 2 * v ≤ (σ / 2) ^ 2 * b ^ 2 * v := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hg2 (by positivity)) hv
      have e3 : σ * m ≥ -(σ * (K * b ^ 2 * v)) := by nlinarith
      have hbv : 0 ≤ b ^ 2 * v := by positivity
      nlinarith [mul_nonneg hσ0 hbv, mul_nonneg (sub_nonneg.2 hσK) (mul_nonneg hσ0 hbv)]
    rw [hW]
    linarith
  -- step 2: absorb `Y`
  have iX := vanish (fun x => ‖X x‖ ^ 2) (by fun_prop) fun s t hs => by
    simp [hXdef, hR s t hs, hS0 s t hs, hT0 s t hs]
  have iY := vanish (fun x => ‖Y x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hYdef, hR s t hs]
  have iXY := vanish (fun x => ‖X x + Y x‖ ^ 2) (by fun_prop) fun s t hs => by
    simp [hXdef, hYdef, hR s t hs, hS0 s t hs, hT0 s t hs]
  have hYb : ∫ x, ‖Y x‖ ^ 2 ∂cylMeasure ≤ M ^ 2 * ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure := by
    rw [← integral_const_mul]
    refine integral_mono iY (iN.const_mul _) fun x => ?_
    have := hM x (φ x)
    have h0 : 0 ≤ ‖Y x‖ := norm_nonneg _
    calc ‖Y x‖ ^ 2 ≤ (M * ‖φ x‖) ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = M ^ 2 * ‖φ x‖ ^ 2 := by ring
  have hXY : ∫ x, ‖X x‖ ^ 2 ∂cylMeasure ≤
      2 * ∫ x, ‖X x + Y x‖ ^ 2 ∂cylMeasure + 2 * ∫ x, ‖Y x‖ ^ 2 ∂cylMeasure := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iXY.const_mul _)
      (iY.const_mul _)]
    refine integral_mono iX ((iXY.const_mul _).add (iY.const_mul _)) fun x => ?_
    have h := norm_sub_le (X x + Y x) (Y x)
    rw [add_sub_cancel_right] at h
    have h' := pow_le_pow_left₀ (norm_nonneg _) h 2
    nlinarith [sq_nonneg (‖X x + Y x‖ - ‖Y x‖)]
  have hN : 0 ≤ ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure := integral_nonneg fun x => by positivity
  nlinarith

end

end CauchyRiemannIndex

/-!
# Cutoffs and the zeros of `β`
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- The tent `τ_a(v) = max 0 (min 1 (2 - 2|v|/a))`. -/
def lapTau (a v : ℝ) : ℝ := max 0 (min 1 (2 - 2 * |v| / a))

lemma lapTau_continuous (a : ℝ) : Continuous (lapTau a) := by
  unfold lapTau; fun_prop

lemma lapTau_nonneg (a v : ℝ) : 0 ≤ lapTau a v := le_max_left _ _

lemma lapTau_le_one (a v : ℝ) : lapTau a v ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma lapTau_eq_one {a v : ℝ} (ha : 0 < a) (hv : |v| ≤ a / 2) : lapTau a v = 1 := by
  unfold lapTau
  have : 1 ≤ 2 - 2 * |v| / a := by
    rw [le_sub_comm, div_le_iff₀ ha]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

lemma lapTau_eq_zero {a v : ℝ} (ha : 0 < a) (hv : a ≤ |v|) : lapTau a v = 0 := by
  unfold lapTau
  have : 2 - 2 * |v| / a ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ ha]; linarith
  exact max_eq_left ((min_le_right _ _).trans this)

/-- The bump `ψ`, `= 1` on `[-a/2, a/2]`, supported in `(-3a/4, 3a/4)`. -/
def lapPsi {a : ℝ} (ha : 0 < a) : ContDiffBump (0 : ℝ) :=
  ⟨a / 2, 3 * a / 4, by positivity, by linarith⟩

/-- `k(u) = u ψ(u)`. -/
def lapK {a : ℝ} (ha : 0 < a) (u : ℝ) : ℝ := u * lapPsi ha u

/-- `k'(u) = ψ(u) + u ψ'(u)`. -/
def lapKd {a : ℝ} (ha : 0 < a) (u : ℝ) : ℝ := lapPsi ha u + u * deriv (lapPsi ha) u

lemma lapPsi_diff {a : ℝ} (ha : 0 < a) : Differentiable ℝ (lapPsi ha) :=
  (lapPsi ha).contDiff.differentiable (n := 1) one_ne_zero

lemma lapK_hasDerivAt {a : ℝ} (ha : 0 < a) (u : ℝ) : HasDerivAt (lapK ha) (lapKd ha u) u := by
  have h := (hasDerivAt_id u).mul ((lapPsi_diff ha) u).hasDerivAt
  unfold lapK lapKd
  refine h.congr_deriv ?_
  simp

lemma lapK_continuous {a : ℝ} (ha : 0 < a) : Continuous (lapK ha) :=
  continuous_id.mul ((lapPsi ha).contDiff (n := 0)).continuous

lemma lapKd_continuous {a : ℝ} (ha : 0 < a) : Continuous (lapKd ha) :=
  ((lapPsi ha).contDiff (n := 0)).continuous.add
    (continuous_id.mul (((lapPsi ha).contDiff (n := 1)).continuous_deriv le_rfl))

lemma lapPsi_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 3 * a / 4 ≤ |u|) : lapPsi ha u = 0 :=
  (lapPsi ha).zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact hu)

lemma lapPsi_deriv_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : 3 * a / 4 < |u|) :
    deriv (lapPsi ha) u = 0 := by
  have hU : IsOpen {u : ℝ | 3 * a / 4 < |u|} := isOpen_lt continuous_const continuous_abs
  have hev : (lapPsi ha : ℝ → ℝ) =ᶠ[𝓝 u] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds hu) fun v hv => lapPsi_eq_zero ha (le_of_lt hv)
  rw [hev.deriv_eq]; simp

lemma lapPsi_eq_one {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ a / 2) : lapPsi ha u = 1 :=
  (lapPsi ha).one_of_mem_closedBall (by
    rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hu)

lemma lapPsi_deriv_eq_zero' {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| < a / 2) :
    deriv (lapPsi ha) u = 0 := by
  have hU : IsOpen {u : ℝ | |u| < a / 2} := isOpen_lt continuous_abs continuous_const
  have hev : (lapPsi ha : ℝ → ℝ) =ᶠ[𝓝 u] fun _ => 1 :=
    Filter.eventually_of_mem (hU.mem_nhds hu) fun v hv => lapPsi_eq_one ha (le_of_lt hv)
  rw [hev.deriv_eq]; simp

lemma lapK_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a ≤ |u|) : lapK ha u = 0 := by
  unfold lapK; rw [lapPsi_eq_zero ha (by linarith), mul_zero]

lemma lapKd_eq_zero {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : a ≤ |u|) : lapKd ha u = 0 := by
  unfold lapKd
  rw [lapPsi_eq_zero ha (by linarith), lapPsi_deriv_eq_zero ha (by linarith)]; ring

lemma lapKd_eq_one {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| < a / 2) : lapKd ha u = 1 := by
  unfold lapKd
  rw [lapPsi_eq_one ha hu.le, lapPsi_deriv_eq_zero' ha hu]; ring

lemma lapK_abs_le {a : ℝ} (ha : 0 < a) (u : ℝ) : |lapK ha u| ≤ |u| := by
  unfold lapK
  rw [abs_mul]
  have h0 := (lapPsi ha).nonneg (x := u)
  have h1 := (lapPsi ha).le_one (x := u)
  rw [abs_of_nonneg h0]
  nlinarith [abs_nonneg u]

lemma lapKd_bounded {a : ℝ} (ha : 0 < a) : ∃ B : ℝ, 0 ≤ B ∧ ∀ u, |lapKd ha u| ≤ B := by
  obtain ⟨B, hB⟩ := (lapKd_continuous ha).bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
      refine lapKd_eq_zero ha ?_
      by_contra h
      exact hu (abs_le.1 (le_of_lt (not_le.1 h)))
  )
  exact ⟨max B 0, le_max_right _ _, fun u => (hB u).trans (le_max_left _ _)⟩

/-! ### The zeros of `β` -/

section zeros

variable {β : ℝ × ℝ → ℂ} {Z : Finset (ℝ × ℝ)} {r : ℝ}

lemma lap_per_int (hβper : ∀ s t, β (s, t + 1) = β (s, t)) (s t : ℝ) (m : ℤ) :
    β (s, t + m) = β (s, t) := by
  have hp : Function.Periodic (fun t => β (s, t)) 1 := fun t => hβper s t
  have := hp.int_mul m t
  simpa [mul_one, add_comm] using this

/-- The normal form near every translate of a zero. -/
lemma lap_local (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hplusZ : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ : ℝ × ℝ} (hζ : ζ ∈ Z) (m : ℤ) {u v : ℝ} (huv : ‖(⟨u, v⟩ : ℂ)‖ < r) :
    β (ζ.1 + u, ζ.2 + m + v) = ⟨u, v⟩ := by
  have := hplusZ ζ hζ ⟨u, v⟩ huv
  have e : ζ.2 + m + v = ζ.2 + v + m := by ring
  rw [e, lap_per_int hβper]
  exact this

lemma lap_norm_lt {u v a : ℝ} (hu : |u| < a) (hv : |v| < a) : ‖(⟨u, v⟩ : ℂ)‖ < 2 * a := by
  have := Complex.norm_le_abs_re_add_abs_im ⟨u, v⟩
  simp only at this
  linarith

/-- Distinct translates of zeros are at distance `≥ r` (in the box norm, `≥ r / 2`). -/
lemma lap_sep (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hZ : ∀ ζ ∈ Z, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Z, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (hplusZ : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z)
    {ζ ζ' : ℝ × ℝ} (hζ : ζ ∈ Z) (hζ' : ζ' ∈ Z) {m m' : ℤ}
    (h1 : |ζ'.1 - ζ.1| < r / 2) (h2 : |ζ'.2 + m' - (ζ.2 + m)| < r / 2) :
    ζ = ζ' ∧ m = m' := by
  have hn := lap_norm_lt h1 h2
  rw [show 2 * (r / 2) = r by ring] at hn
  have hloc := lap_local hβper hplusZ hζ m hn
  have e : (ζ.1 + (ζ'.1 - ζ.1), ζ.2 + m + (ζ'.2 + m' - (ζ.2 + m))) = (ζ'.1, ζ'.2 + m') := by
    ext <;> simp
  rw [e, (hzero _).2 ⟨ζ', hζ', m', rfl⟩] at hloc
  have hre := congrArg Complex.re hloc
  have him := congrArg Complex.im hloc
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hmm : (m : ℝ) = m' := by
    have hd : ((m' - m : ℤ) : ℝ) = ζ.2 - ζ'.2 := by push_cast; linarith
    have hlt : |((m' - m : ℤ) : ℝ)| < 1 := by
      rw [hd, abs_lt]
      constructor <;> linarith [hZ ζ hζ, hZ ζ' hζ']
    have : m' - m = 0 := by
      rw [← Int.cast_abs] at hlt
      have : |m' - m| < 1 := by exact_mod_cast hlt
      exact Int.abs_lt_one_iff.1 this
    have : (m : ℝ) = m' := by exact_mod_cast (by omega : m = m')
    exact this
  have hm : m = m' := by exact_mod_cast hmm
  refine ⟨Prod.ext (by linarith) (by rw [hmm] at him; linarith), hm⟩

end zeros

end

end CauchyRiemannIndex

/-!
# A weight adapted to the positive zeros of `β`

Around each zero `ζ` (and its translate by `(0, 1)`) we put
`k(s - ζₛ) τ(t - ζₜ - m)` with `k(u) = u ψ(u)` for a bump `ψ` and a tent `τ`; on the inner boxes
`∂ₛ` of the weight is `1`, everywhere its modulus is at most `|β|`, and off the inner boxes `|β|`
is bounded below.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- The weight adapted to the zeros of `β` when all of them are positive. -/
theorem lap_geom (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Z : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Z, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Z, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Z, ∀ z : ℂ, ‖z‖ < r → β (ζ.1 + z.re, ζ.2 + z.im) = z) :
    ∃ (g gs : ℝ × ℝ → ℝ) (K : ℝ), 0 ≤ K ∧ Continuous g ∧ Continuous gs ∧
      (∀ s t, HasDerivAt (fun s => g (s, t)) (gs (s, t)) s) ∧
      ∀ x : ℝ × ℝ, x.2 ∈ Set.Ico (0 : ℝ) 1 → |g x| ≤ ‖β x‖ ∧ 1 - K * ‖β x‖ ^ 2 ≤ gs x ∧
        ‖dS β x + Complex.I * dT β x‖ ≤ K * ‖β x‖ ^ 2 := by
  set a : ℝ := r / 4 with ha_def
  have ha : 0 < a := by positivity
  set I : Finset ((ℝ × ℝ) × ℤ) := Z ×ˢ ({0, 1} : Finset ℤ)
  set U : ℝ × ℝ → (ℝ × ℝ) × ℤ → ℝ := fun x p => x.1 - p.1.1
  set V : ℝ × ℝ → (ℝ × ℝ) × ℤ → ℝ := fun x p => x.2 - p.1.2 - p.2
  set g : ℝ × ℝ → ℝ := fun x => ∑ p ∈ I, lapK ha (U x p) * lapTau a (V x p)
  set gs : ℝ × ℝ → ℝ := fun x => ∑ p ∈ I, lapKd ha (U x p) * lapTau a (V x p)
  -- the point in local coordinates
  have hloc : ∀ x p, p ∈ I → |U x p| < a → |V x p| < a → β x = ⟨U x p, V x p⟩ := by
    intro x p hp hu hv
    have hpZ : p.1 ∈ Z := (Finset.mem_product.1 hp).1
    have hn : ‖(⟨U x p, V x p⟩ : ℂ)‖ < r := by
      have := lap_norm_lt hu hv; linarith
    have := lap_local hβper hplusZ hpZ p.2 hn
    have e : (p.1.1 + U x p, p.1.2 + p.2 + V x p) = x := by
      simp only [U, V]; ext <;> simp
    rwa [e] at this
  -- at most one term is nonzero
  have huniq : ∀ x p q, p ∈ I → q ∈ I → |U x p| < a → |V x p| < a → |U x q| < a →
      |V x q| < a → p = q := by
    intro x p q hp hq hu hv hu' hv'
    have hpZ : p.1 ∈ Z := (Finset.mem_product.1 hp).1
    have hqZ : q.1 ∈ Z := (Finset.mem_product.1 hq).1
    have h1 : |q.1.1 - p.1.1| < r / 2 := by
      have : q.1.1 - p.1.1 = U x p - U x q := by simp only [U]; ring
      rw [this]; calc |U x p - U x q| ≤ |U x p| + |U x q| := abs_sub _ _
        _ < r / 2 := by linarith
    have h2 : |q.1.2 + q.2 - (p.1.2 + p.2)| < r / 2 := by
      have : q.1.2 + q.2 - (p.1.2 + p.2) = V x p - V x q := by simp only [V]; ring
      rw [this]; calc |V x p - V x q| ≤ |V x p| + |V x q| := abs_sub _ _
        _ < r / 2 := by linarith
    obtain ⟨e1, e2⟩ := lap_sep hβper hZ hzero hplusZ hpZ hqZ h1 h2
    exact Prod.ext e1 e2
  have hterm0 : ∀ (F : ℝ → ℝ), (∀ u, a ≤ |u| → F u = 0) → ∀ x p,
      ¬ (|U x p| < a ∧ |V x p| < a) → F (U x p) * lapTau a (V x p) = 0 := by
    intro F hF x p h
    by_cases hu : |U x p| < a
    · have hv : a ≤ |V x p| := by by_contra hv; exact h ⟨hu, not_le.1 hv⟩
      rw [lapTau_eq_zero ha hv, mul_zero]
    · rw [hF _ (not_lt.1 hu), zero_mul]
  -- the sum reduces to the near term
  have hsum : ∀ (F : ℝ → ℝ), (∀ u, a ≤ |u| → F u = 0) → ∀ x,
      (∑ p ∈ I, F (U x p) * lapTau a (V x p) = 0) ∨
      ∃ p ∈ I, |U x p| < a ∧ |V x p| < a ∧
        ∑ q ∈ I, F (U x q) * lapTau a (V x q) = F (U x p) * lapTau a (V x p) := by
    intro F hF x
    by_cases h : ∃ p ∈ I, |U x p| < a ∧ |V x p| < a
    · obtain ⟨p, hp, hu, hv⟩ := h
      refine Or.inr ⟨p, hp, hu, hv, Finset.sum_eq_single p (fun q hq hqp => ?_) (fun h => ?_)⟩
      · refine hterm0 F hF x q fun ⟨hu', hv'⟩ => hqp ?_
        exact (huniq x p q hp hq hu hv hu' hv').symm
      · exact absurd hp h
    · push Not at h
      refine Or.inl (Finset.sum_eq_zero fun p hp => hterm0 F hF x p fun ⟨hu, hv⟩ =>
        absurd (h p hp hu) (not_le.2 hv))
  -- bounds
  obtain ⟨Bk, hBk0, hBk⟩ := lapKd_bounded ha
  have hgs_le : ∀ x, |gs x| ≤ Bk := by
    intro x
    rcases hsum (lapKd ha) (fun u hu => lapKd_eq_zero ha hu) x with h | ⟨p, _, _, _, h⟩
    · simp only [gs, h, abs_zero]; exact hBk0
    · simp only [gs, h, abs_mul]
      rw [abs_of_nonneg (lapTau_nonneg _ _)]
      calc |lapKd ha (U x p)| * lapTau a (V x p) ≤ Bk * 1 :=
            mul_le_mul (hBk _) (lapTau_le_one _ _) (lapTau_nonneg _ _) hBk0
        _ = Bk := mul_one _
  obtain ⟨C, hC⟩ := hβC1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hdS_le : ∀ x, ‖dS β x‖ ≤ C := fun x => by
    unfold dS
    calc ‖fderiv ℝ β x (1, 0)‖ ≤ ‖fderiv ℝ β x‖ * ‖((1 : ℝ), (0 : ℝ))‖ :=
          (fderiv ℝ β x).le_opNorm _
      _ ≤ C * 1 := by gcongr; exact hC x; simp
      _ = C := mul_one _
  have hdT_le : ∀ x, ‖dT β x‖ ≤ C := fun x => by
    unfold dT
    calc ‖fderiv ℝ β x (0, 1)‖ ≤ ‖fderiv ℝ β x‖ * ‖((0 : ℝ), (1 : ℝ))‖ :=
          (fderiv ℝ β x).le_opNorm _
      _ ≤ C * 1 := by gcongr; exact hC x; simp
      _ = C := mul_one _
  -- the inner region and the lower bound for `|β|` off it
  set Uin : Set (ℝ × ℝ) := {x | ∃ p ∈ I, |U x p| < a / 2 ∧ |V x p| < a / 2}
  have hUo : IsOpen Uin := by
    have e : Uin = ⋃ p ∈ I, ({x : ℝ × ℝ | |U x p| < a / 2} ∩ {x | |V x p| < a / 2}) := by
      ext x; simp only [Uin, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, exists_prop]
    rw [e]
    refine isOpen_biUnion fun p _ => IsOpen.inter ?_ ?_
    · exact isOpen_lt (continuous_abs.comp (continuous_fst.sub continuous_const))
        continuous_const
    · exact isOpen_lt (continuous_abs.comp ((continuous_snd.sub continuous_const).sub
        continuous_const)) continuous_const
  obtain ⟨R₀, c, hc, hends⟩ := hβends
  have hlow : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ x : ℝ × ℝ, x.2 ∈ Set.Ico (0 : ℝ) 1 → x ∉ Uin →
      c₀ ≤ ‖β x‖ := by
    set Kset := (Set.Icc (-|R₀|) |R₀| ×ˢ Set.Icc (0 : ℝ) 1) ∩ Uinᶜ
    have hK : IsCompact Kset :=
      (isCompact_Icc.prod isCompact_Icc).inter_right hUo.isClosed_compl
    have hne : ∀ x ∈ Kset, 0 < ‖β x‖ := by
      intro x hx
      rw [norm_pos_iff]
      intro h0
      obtain ⟨ζ, hζ, m, rfl⟩ := (hzero x).1 h0
      have ht := (Set.mem_prod.1 hx.1).2
      have hz := hZ ζ hζ
      have hm : m = 0 ∨ m = 1 := by
        have h1 : (-1 : ℝ) < m := by simp only [Set.mem_Icc] at ht; linarith
        have h2 : (m : ℝ) ≤ 1 := by simp only [Set.mem_Icc] at ht; linarith
        have h1' : -1 < m := by exact_mod_cast h1
        have h2' : m ≤ 1 := by exact_mod_cast h2
        omega
      refine hx.2 ⟨(ζ, m), Finset.mem_product.2 ⟨hζ, by rcases hm with h | h <;> simp [h]⟩,
        ?_, ?_⟩ <;> simp [U, V, ha]
    rcases Kset.eq_empty_or_nonempty with he | hne'
    · refine ⟨c, hc, fun x hx hxU => ?_⟩
      by_cases hs : |x.1| ≤ |R₀|
      · have : x ∈ Kset := ⟨Set.mk_mem_prod (abs_le.1 hs) ⟨hx.1, hx.2.le⟩, hxU⟩
        rw [he] at this; exact absurd this (Set.notMem_empty x)
      · exact (hends x.1 x.2 ((le_abs_self R₀).trans (not_le.1 hs).le)).1
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne' (continuous_norm.comp hβ.continuous).continuousOn
      refine ⟨min c ‖β x₀‖, lt_min hc (hne x₀ hx₀), fun x hx hxU => ?_⟩
      by_cases hs : |x.1| ≤ |R₀|
      · have : x ∈ Kset := ⟨Set.mk_mem_prod (abs_le.1 hs) ⟨hx.1, hx.2.le⟩, hxU⟩
        exact (min_le_right _ _).trans (hmin this)
      · exact (min_le_left _ _).trans
          (hends x.1 x.2 ((le_abs_self R₀).trans (not_le.1 hs).le)).1
  obtain ⟨c₀, hc₀, hlow⟩ := hlow
  -- the derivatives of `β` on the inner region
  have hβd : Differentiable ℝ β := hβ.differentiable one_ne_zero
  have hMzero : ∀ x ∈ Uin, dS β x + Complex.I * dT β x = 0 := by
    rintro x ⟨p, hp, hu, hv⟩
    have hnear : ∀ y : ℝ × ℝ, |U y p| < a → |V y p| < a → β y = ⟨U y p, V y p⟩ :=
      fun y => hloc y p hp
    have hS : dS β x = 1 := by
      have h1 := hasDerivAt_slice_s hβd x.1 x.2
      have h2 : HasDerivAt (fun s => (((s - p.1.1 : ℝ) : ℂ) + ((V x p : ℝ) : ℂ) * Complex.I))
          1 x.1 := by
        have := ((hasDerivAt_id x.1).sub_const p.1.1).ofReal_comp.add_const
          (((V x p : ℝ) : ℂ) * Complex.I)
        simpa using this
      have hev : (fun s => β (s, x.2)) =ᶠ[𝓝 x.1]
          fun s => (((s - p.1.1 : ℝ) : ℂ) + ((V x p : ℝ) : ℂ) * Complex.I) := by
        have hO : IsOpen {s : ℝ | |s - p.1.1| < a} :=
          isOpen_lt (continuous_abs.comp (continuous_sub_right _)) continuous_const
        refine Filter.eventually_of_mem (hO.mem_nhds (by simp only [Set.mem_ofPred_eq]; exact
          (show |U x p| < a by linarith))) fun s hs => ?_
        have := hnear (s, x.2) hs (by simp only [V] at hv ⊢; linarith)
        dsimp only
        rw [this]
        apply Complex.ext <;> simp [U, V]
      have := h2.congr_of_eventuallyEq hev
      exact h1.unique this
    have hT : dT β x = Complex.I := by
      have h1 := hasDerivAt_slice_t hβd x.1 x.2
      have h2 : HasDerivAt (fun t => (((U x p : ℝ) : ℂ) +
          ((t - p.1.2 - p.2 : ℝ) : ℂ) * Complex.I)) Complex.I x.2 := by
        have := ((((hasDerivAt_id x.2).sub_const p.1.2).sub_const (p.2 : ℝ)).ofReal_comp.mul_const
          Complex.I).const_add ((U x p : ℝ) : ℂ)
        simpa using this
      have hev : (fun t => β (x.1, t)) =ᶠ[𝓝 x.2]
          fun t => (((U x p : ℝ) : ℂ) + ((t - p.1.2 - p.2 : ℝ) : ℂ) * Complex.I) := by
        have hO : IsOpen {t : ℝ | |t - p.1.2 - p.2| < a} :=
          isOpen_lt (continuous_abs.comp ((continuous_sub_right _).sub continuous_const))
            continuous_const
        refine Filter.eventually_of_mem (hO.mem_nhds (by simp only [Set.mem_ofPred_eq]; exact
          (show |V x p| < a by linarith))) fun t ht => ?_
        have := hnear (x.1, t) (by simp only [U] at hu ⊢; linarith) ht
        dsimp only
        rw [this]
        apply Complex.ext <;> simp [U, V]
      have := h2.congr_of_eventuallyEq hev
      exact h1.unique this
    rw [hS, hT, Complex.I_mul_I]; ring
  -- the constant
  set K : ℝ := (1 + Bk + 2 * C) / c₀ ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hKc : 1 + Bk + 2 * C ≤ K * c₀ ^ 2 := by
    rw [div_mul_cancel₀ _ (by positivity)]
  refine ⟨g, gs, K, hK0, ?_, ?_, ?_, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · exact continuous_finsetSum _ fun p _ =>
      ((lapK_continuous ha).comp (continuous_fst.sub continuous_const)).mul
        ((lapTau_continuous a).comp ((continuous_snd.sub continuous_const).sub continuous_const))
  · exact continuous_finsetSum _ fun p _ =>
      ((lapKd_continuous ha).comp (continuous_fst.sub continuous_const)).mul
        ((lapTau_continuous a).comp ((continuous_snd.sub continuous_const).sub continuous_const))
  · intro s t
    refine HasDerivAt.fun_sum fun p _ => ?_
    have := ((lapK_hasDerivAt ha (s - p.1.1)).comp s ((hasDerivAt_id s).sub_const p.1.1)).mul_const
      (lapTau a (t - p.1.2 - p.2))
    simpa [U, V] using this
  · -- `|g| ≤ |β|`
    rcases hsum (lapK ha) (fun u hu => lapK_eq_zero ha hu) x with h | ⟨p, hp, hu, hv, h⟩
    · simp only [g, h, abs_zero]; exact norm_nonneg _
    · simp only [g, h]
      rw [hloc x p hp hu hv, abs_mul, abs_of_nonneg (lapTau_nonneg _ _)]
      calc |lapK ha (U x p)| * lapTau a (V x p) ≤ |U x p| * 1 :=
            mul_le_mul (lapK_abs_le ha _) (lapTau_le_one _ _) (lapTau_nonneg _ _) (abs_nonneg _)
        _ = |(⟨U x p, V x p⟩ : ℂ).re| := by simp
        _ ≤ ‖(⟨U x p, V x p⟩ : ℂ)‖ := Complex.abs_re_le_norm _
  · -- `1 - K |β|² ≤ ∂ₛg`
    by_cases hxU : x ∈ Uin
    · obtain ⟨p, hp, hu, hv⟩ := hxU
      have hgs1 : gs x = 1 := by
        rcases hsum (lapKd ha) (fun u hu => lapKd_eq_zero ha hu) x with h | ⟨q, hq, hu', hv', h⟩
        · exfalso
          have h' : gs x = lapKd ha (U x p) * lapTau a (V x p) := by
            simp only [gs]
            refine Finset.sum_eq_single p (fun q hq hqp => hterm0 _
              (fun u hu => lapKd_eq_zero ha hu) x q fun ⟨hu', hv'⟩ => hqp ?_) (fun h => absurd hp h)
            exact (huniq x p q hp hq (by linarith) (by linarith) hu' hv').symm
          rw [lapKd_eq_one ha hu, lapTau_eq_one ha hv.le, one_mul] at h'
          simp only [gs] at h'; rw [h] at h'; norm_num at h'
        · have hqp : q = p := huniq x q p hq hp hu' hv' (by linarith) (by linarith)
          subst hqp
          simp only [gs, h]
          rw [lapKd_eq_one ha hu, lapTau_eq_one ha hv.le, one_mul]
      rw [hgs1]
      have : 0 ≤ K * ‖β x‖ ^ 2 := by positivity
      linarith
    · have hb := hlow x hx hxU
      have hb2 : c₀ ^ 2 ≤ ‖β x‖ ^ 2 := pow_le_pow_left₀ hc₀.le hb 2
      have h1 := (abs_le.1 (hgs_le x)).1
      have : K * c₀ ^ 2 ≤ K * ‖β x‖ ^ 2 := mul_le_mul_of_nonneg_left hb2 hK0
      linarith
  · -- the curvature term
    by_cases hxU : x ∈ Uin
    · rw [hMzero x hxU, norm_zero]; positivity
    · have hb := hlow x hx hxU
      have hb2 : c₀ ^ 2 ≤ ‖β x‖ ^ 2 := pow_le_pow_left₀ hc₀.le hb 2
      have : K * c₀ ^ 2 ≤ K * ‖β x‖ ^ 2 := mul_le_mul_of_nonneg_left hb2 hK0
      calc ‖dS β x + Complex.I * dT β x‖ ≤ ‖dS β x‖ + ‖Complex.I * dT β x‖ := norm_add_le _ _
        _ ≤ C + C := by
          rw [norm_mul, Complex.norm_I, one_mul]; exact add_le_add (hdS_le x) (hdT_le x)
        _ ≤ K * ‖β x‖ ^ 2 := by linarith

/-- Wendl, Lemma 5.22 for the adjoint, when all zeros of `β` are positive: for large `σ`,
`‖φ‖₂ ≤ ‖D_σ^* φ‖₂` on test sections. -/
theorem large_antilinear_adjoint_estimate_aux (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus Zminus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus ∪ Zminus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus ∪ Zminus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0)
    (hZminus : Zminus = ∅) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ φ : ℝ × ℝ → Vec 1, IsTestSection φ →
      ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
          Matrix.toEuclideanLin (S x + σ • antilinearMat (β x))ᵀ (φ x)‖ ^ 2 ∂cylMeasure := by
  subst hZminus
  simp only [Finset.union_empty] at hZ hzero
  have hβ1 : ContDiff ℝ 1 β := hβ.of_le (by simp)
  exact lap_est_of_geom Splus Sminus hSplus hSminus S hS β hβ1 hβper
    (lap_geom β hβ1 hβper hβC1 hβends Zplus hZ hzero r hr fun ζ hζ z hz => (hplusZ ζ hζ z hz).1)

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (Splus Sminus : ℝ → Mat 1)
    (hSplus : IsSymLoop Splus) (hSminus : IsSymLoop Sminus)
    (S : ℝ × ℝ → Mat 1) (hS : IsAsymptoticTo S Splus Sminus)
    (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ ∞ β) (hβper : ∀ s t, β (s, t + 1) = β (s, t))
    (hβC1 : ∃ C : ℝ, ∀ x, ‖fderiv ℝ β x‖ ≤ C)
    (hβends : ∃ (R c : ℝ), 0 < c ∧ ∀ s t, R ≤ |s| → c ≤ ‖β (s, t)‖ ∧ ‖β (s, t)‖ ≤ 1 / c)
    (Zplus : Finset (ℝ × ℝ)) (hZ : ∀ ζ ∈ Zplus, 0 ≤ ζ.2 ∧ ζ.2 < 1)
    (hzero : ∀ x : ℝ × ℝ, β x = 0 ↔ ∃ ζ ∈ Zplus, ∃ m : ℤ, x = (ζ.1, ζ.2 + m))
    (r : ℝ) (hr : 0 < r)
    (hplusZ : ∀ ζ ∈ Zplus, ∀ z : ℂ, ‖z‖ < r →
      β (ζ.1 + z.re, ζ.2 + z.im) = z ∧ S (ζ.1 + z.re, ζ.2 + z.im) = 0) :
    ∃ σ₀ : ℝ, ∀ σ ≥ σ₀, ∀ φ : ℝ × ℝ → Vec 1, IsTestSection φ →
      ∫ x, ‖φ x‖ ^ 2 ∂cylMeasure ≤
        ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
          Matrix.toEuclideanLin (S x + σ • antilinearMat (β x))ᵀ (φ x)‖ ^ 2 ∂cylMeasure :=
  large_antilinear_adjoint_estimate_aux Splus Sminus hSplus hSminus S hS β hβ hβper hβC1 hβends Zplus ∅ (by simpa using hZ) (by simpa using hzero) r hr hplusZ rfl
