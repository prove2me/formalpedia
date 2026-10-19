-- Prove2me | solution 1 for CauchyRiemannIndex.antilinear_adjoint_energy_identity
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T14:02:35.580583+00:00
-- url     : https://prove2.me/submissions/cf20ece2-5b7c-443d-824c-43962e423a1c

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
import Theorems.Thm_CauchyRiemannIndex_crOp_energy_identity



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

/-!
# The `L²` norm of `-∂ₛφ + J₀∂ₜφ + σ β φ̄`

For a test section `φ` and a `C¹`, `t`-periodic `β`,
`∫ |-∂ₛφ + J₀∂ₜφ + σ A(β) φ|² = ∫ |∂ₛφ|² + ∫ |∂ₜφ|² + σ² ∫ |β|² |φ|² + σ ∫ ⟨φ, A(∂ₛβ + i ∂ₜβ) φ⟩`.
-/

namespace CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

/-- `∫ |-a + b + c|²` expanded, given `∫ ⟨a, b⟩ = 0`. -/
lemma lap_expand {μ : Measure (ℝ × ℝ)} (a b c : ℝ × ℝ → Vec 1)
    (iaa : Integrable (fun x => ‖a x‖ ^ 2) μ) (ibb : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (icc : Integrable (fun x => ‖c x‖ ^ 2) μ) (iab : Integrable (fun x => ⟪a x, b x⟫) μ)
    (iac : Integrable (fun x => ⟪a x, c x⟫) μ) (ibc : Integrable (fun x => ⟪b x, c x⟫) μ)
    (hab : ∫ x, ⟪a x, b x⟫ ∂μ = 0) :
    ∫ x, ‖-a x + b x + c x‖ ^ 2 ∂μ =
      ∫ x, ‖a x‖ ^ 2 ∂μ + ∫ x, ‖b x‖ ^ 2 ∂μ + ∫ x, ‖c x‖ ^ 2 ∂μ -
        2 * ∫ x, ⟪a x, c x⟫ ∂μ + 2 * ∫ x, ⟪b x, c x⟫ ∂μ := by
  have hpt : ∀ x, ‖-a x + b x + c x‖ ^ 2 =
      ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c x‖ ^ 2 - 2 * ⟪a x, b x⟫ - 2 * ⟪a x, c x⟫ + 2 * ⟪b x, c x⟫ := by
    intro x
    rw [norm_add_sq_real, norm_add_sq_real, norm_neg, inner_add_left, inner_neg_left,
      inner_neg_left]
    ring
  simp_rw [hpt]
  have i1 : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2) μ := iaa.add ibb
  have i2 : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c x‖ ^ 2) μ := i1.add icc
  have i3 : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c x‖ ^ 2 - 2 * ⟪a x, b x⟫) μ :=
    i2.sub (iab.const_mul 2)
  have i4 : Integrable (fun x => ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c x‖ ^ 2 - 2 * ⟪a x, b x⟫ -
    2 * ⟪a x, c x⟫) μ := i3.sub (iac.const_mul 2)
  rw [integral_add i4 (ibc.const_mul 2), integral_sub i3 (iac.const_mul 2),
    integral_sub i2 (iab.const_mul 2), integral_add i1 icc, integral_add iaa ibb,
    integral_const_mul, integral_const_mul, integral_const_mul, hab]
  ring

theorem antilinear_adjoint_energy_aux (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) (σ : ℝ) (φ : ℝ × ℝ → Vec 1)
    (hφ : IsTestSection φ) :
    ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        Matrix.toEuclideanLin (σ • antilinearMat (β x)) (φ x)‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS φ x‖ ^ 2 ∂cylMeasure + ∫ x, ‖partialT φ x‖ ^ 2 ∂cylMeasure +
        σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ * ∫ x, ⟪φ x, Matrix.toEuclideanLin (antilinearMat (dS β x + Complex.I * dT β x))
          (φ x)⟫ ∂cylMeasure := by
  obtain ⟨R, hR⟩ := hφ.2.2
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hβd : Differentiable ℝ β := hβ.differentiable one_ne_zero
  have hβc : Continuous β := hβ.continuous
  have hdS : Continuous (dS β) := (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdT : Continuous (dT β) := (hβ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hS0 : ∀ s t, R < |s| → partialS φ (s, t) = 0 := fun s t hs => partialS_eq_zero R hR hs
  have hT0 : ∀ s t, R < |s| → partialT φ (s, t) = 0 := fun s t hs => partialT_eq_zero R hR hs
  have hφc := hφ.continuous
  have hSc := hφ.continuous_partialS
  have hTc := hφ.continuous_partialT
  have hKc : ∀ {f : ℝ × ℝ → ℂ}, Continuous f → Continuous fun x => almK (f x) :=
    fun hf => almK.continuous.comp hf
  have hbc : Continuous fun x => Matrix.toEuclideanLin (J₀ 1) (partialT φ x) :=
    (matCLM 1 (J₀ 1)).continuous.comp hTc
  have hcc : Continuous fun x => σ • almK (β x) (φ x) := ((hKc hβc).clm_apply hφc).const_smul σ
  have vanish : ∀ (F : ℝ × ℝ → ℝ), Continuous F → (∀ s t, R < |s| → F (s, t) = 0) →
      Integrable F cylMeasure := fun F hF h => lap_integrable hF R h
  have iaa := vanish (fun x => ‖partialS φ x‖ ^ 2) (by fun_prop) fun s t hs => by simp [hS0 s t hs]
  have ibb := vanish (fun x => ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x)‖ ^ 2)
    (by fun_prop) fun s t hs => by simp [hT0 s t hs]
  have icc := vanish (fun x => ‖σ • almK (β x) (φ x)‖ ^ 2) (by fun_prop)
    fun s t hs => by simp [hR s t hs]
  have iab := vanish (fun x => ⟪partialS φ x, Matrix.toEuclideanLin (J₀ 1) (partialT φ x)⟫)
    (hSc.inner hbc) fun s t hs => by simp [hS0 s t hs]
  have iac := vanish (fun x => ⟪partialS φ x, σ • almK (β x) (φ x)⟫) (hSc.inner hcc)
    fun s t hs => by simp [hS0 s t hs]
  have ibc := vanish (fun x => ⟪Matrix.toEuclideanLin (J₀ 1) (partialT φ x),
    σ • almK (β x) (φ x)⟫) (hbc.inner hcc) fun s t hs => by simp [hT0 s t hs]
  -- (1) the cross term `⟨∂ₛφ, J₀∂ₜφ⟩` integrates to zero
  have hE := crOp_energy_identity 1 (fun _ => 0) continuous_const
    (fun _ => Matrix.isSymm_zero) φ hφ
  have hab : ∫ x, ⟪partialS φ x, Matrix.toEuclideanLin (J₀ 1) (partialT φ x)⟫ ∂cylMeasure =
      0 := by
    have e : ∀ x, ‖crOp (fun x : ℝ × ℝ => (fun _ : ℝ => (0 : Mat 1)) x.2) φ x‖ ^ 2 =
        ‖partialS φ x‖ ^ 2 + ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x)‖ ^ 2 +
          2 * ⟪partialS φ x, Matrix.toEuclideanLin (J₀ 1) (partialT φ x)⟫ := by
      intro x
      simp only [crOp, map_zero, LinearMap.zero_apply, add_zero]
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_comm (partialS φ x)]
      ring
    have e2 : ∀ x, ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        Matrix.toEuclideanLin ((fun _ : ℝ => (0 : Mat 1)) x.2) (φ x)‖ ^ 2 =
        ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x)‖ ^ 2 := fun x => by simp
    simp only [e, e2] at hE
    have i1 : Integrable (fun x => ‖partialS φ x‖ ^ 2 +
        ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x)‖ ^ 2) cylMeasure := iaa.add ibb
    rw [integral_add i1 (iab.const_mul 2), integral_add iaa ibb, integral_const_mul] at hE
    linarith
  have hgoal : (fun x => ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        Matrix.toEuclideanLin (σ • antilinearMat (β x)) (φ x)‖ ^ 2) =
      fun x => ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        σ • almK (β x) (φ x)‖ ^ 2 := by
    funext x; simp [almK_apply]
  rw [hgoal, lap_expand _ _ _ iaa ibb icc iab iac ibc hab]
  -- (2) the cross terms with `A(β)` integrate to the curvature term
  have hsym : ∀ (z : ℂ) (v w : Vec 1), ⟪v, almK z w⟫ = ⟪almK z v, w⟫ := fun z v w =>
    (lap_inner_alm_sym z v w).symm
  have hF₁ : ∀ s t, HasDerivAt (fun s => ⟪φ (s, t), almK (β (s, t)) (φ (s, t))⟫)
      (2 * ⟪partialS φ (s, t), almK (β (s, t)) (φ (s, t))⟫ +
        ⟪φ (s, t), almK (dS β (s, t)) (φ (s, t))⟫) s := by
    intro s t
    have h1 := hasDerivAt_slice_s hφd s t
    have h2 : HasDerivAt (fun s => almK (β (s, t))) (almK (dS β (s, t))) s :=
      almK.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_slice_s hβd s t)
    have h4 := h1.inner ℝ (h2.clm_apply h1)
    refine h4.congr_deriv ?_
    unfold partialS
    rw [inner_add_right]
    linarith [real_inner_comm (almK (β (s, t)) (φ (s, t))) (fderiv ℝ φ (s, t) (1, 0)),
      hsym (β (s, t)) (φ (s, t)) (fderiv ℝ φ (s, t) (1, 0))]
  have hF₂ : ∀ s t, HasDerivAt (fun t => ⟪φ (s, t), almK (Complex.I * β (s, t)) (φ (s, t))⟫)
      (2 * ⟪partialT φ (s, t), almK (Complex.I * β (s, t)) (φ (s, t))⟫ +
        ⟪φ (s, t), almK (Complex.I * dT β (s, t)) (φ (s, t))⟫) t := by
    intro s t
    have h1 := hasDerivAt_slice_t hφd s t
    have h2 : HasDerivAt (fun t => almK (Complex.I * β (s, t)))
        (almK (Complex.I * dT β (s, t))) t :=
      almK.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_slice_t hβd s t).const_mul Complex.I)
    have h4 := h1.inner ℝ (h2.clm_apply h1)
    refine h4.congr_deriv ?_
    unfold partialT
    rw [inner_add_right]
    linarith [real_inner_comm (almK (Complex.I * β (s, t)) (φ (s, t))) (fderiv ℝ φ (s, t) (0, 1)),
      hsym (Complex.I * β (s, t)) (φ (s, t)) (fderiv ℝ φ (s, t) (0, 1))]
  have iP₁ := vanish (fun x => ⟪partialS φ x, almK (β x) (φ x)⟫)
    (hSc.inner ((hKc hβc).clm_apply hφc)) fun s t hs => by simp [hS0 s t hs]
  have iP₂ := vanish (fun x => ⟪partialT φ x, almK (Complex.I * β x) (φ x)⟫)
    (hTc.inner ((hKc (continuous_const.mul hβc)).clm_apply hφc)) fun s t hs => by
      simp [hT0 s t hs]
  have iM₁ := vanish (fun x => ⟪φ x, almK (dS β x) (φ x)⟫)
    (hφc.inner ((hKc hdS).clm_apply hφc)) fun s t hs => by simp [hR s t hs]
  have iM₂ := vanish (fun x => ⟪φ x, almK (Complex.I * dT β x) (φ x)⟫)
    (hφc.inner ((hKc (continuous_const.mul hdT)).clm_apply hφc)) fun s t hs => by
      simp [hR s t hs]
  have hI₁ := lap_integral_s_eq_zero
    (fun x => 2 * ⟪partialS φ x, almK (β x) (φ x)⟫ + ⟪φ x, almK (dS β x) (φ x)⟫)
    (fun x => ⟪φ x, almK (β x) (φ x)⟫)
    ((continuous_const.mul (hSc.inner ((hKc hβc).clm_apply hφc))).add
      (hφc.inner ((hKc hdS).clm_apply hφc))) R
    (fun s t hs => by simp [hS0 s t hs, hR s t hs])
    (fun s t hs => by simp [hR s t hs]) hF₁
  have hI₂ := integral_t_eq_zero_of_hasDerivAt
    (fun x => 2 * ⟪partialT φ x, almK (Complex.I * β x) (φ x)⟫ +
      ⟪φ x, almK (Complex.I * dT β x) (φ x)⟫)
    (fun x => ⟪φ x, almK (Complex.I * β x) (φ x)⟫)
    ((continuous_const.mul (hTc.inner ((hKc (continuous_const.mul hβc)).clm_apply hφc))).add
      (hφc.inner ((hKc (continuous_const.mul hdT)).clm_apply hφc))) R
    (fun s t hs => by simp [hT0 s t hs, hR s t hs])
    (fun s t => by simp only [hφ.2.1, hβper]) hF₂
  rw [integral_add (iP₁.const_mul 2) iM₁, integral_const_mul] at hI₁
  rw [integral_add (iP₂.const_mul 2) iM₂, integral_const_mul] at hI₂
  have hac : ∀ x, ⟪partialS φ x, σ • almK (β x) (φ x)⟫ =
      σ * ⟪partialS φ x, almK (β x) (φ x)⟫ := fun x => by rw [inner_smul_right]
  have hbc' : ∀ x, ⟪Matrix.toEuclideanLin (J₀ 1) (partialT φ x), σ • almK (β x) (φ x)⟫ =
      -(σ * ⟪partialT φ x, almK (Complex.I * β x) (φ x)⟫) := by
    intro x
    rw [inner_smul_right, almK_apply, lap_inner_J_alm, almK_apply]; ring
  have hM : ∀ x, ⟪φ x, Matrix.toEuclideanLin (antilinearMat (dS β x + Complex.I * dT β x))
      (φ x)⟫ = ⟪φ x, almK (dS β x) (φ x)⟫ + ⟪φ x, almK (Complex.I * dT β x) (φ x)⟫ := by
    intro x
    rw [← almK_apply, map_add, _root_.add_apply, inner_add_right]
  have hcc' : ∀ x, ‖σ • almK (β x) (φ x)‖ ^ 2 = σ ^ 2 * (‖β x‖ ^ 2 * ‖φ x‖ ^ 2) := by
    intro x
    rw [norm_smul, mul_pow, almK_apply, lap_norm_alm_sq, Real.norm_eq_abs, sq_abs]
  have hbb' : ∀ x, ‖Matrix.toEuclideanLin (J₀ 1) (partialT φ x)‖ ^ 2 =
      ‖partialT φ x‖ ^ 2 := fun x => by rw [lap_norm_J]
  simp_rw [hac, hbc', hcc', hbb', hM]
  rw [integral_const_mul, integral_neg, integral_const_mul, integral_const_mul,
    integral_add iM₁ iM₂]
  linear_combination (-σ) * hI₁ + (-σ) * hI₂

end

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (β : ℝ × ℝ → ℂ) (hβ : ContDiff ℝ 1 β)
    (hβper : ∀ s t, β (s, t + 1) = β (s, t)) (σ : ℝ) (φ : ℝ × ℝ → Vec 1)
    (hφ : IsTestSection φ) :
    ∫ x, ‖-partialS φ x + Matrix.toEuclideanLin (J₀ 1) (partialT φ x) +
        Matrix.toEuclideanLin (σ • antilinearMat (β x)) (φ x)‖ ^ 2 ∂cylMeasure =
      ∫ x, ‖partialS φ x‖ ^ 2 ∂cylMeasure + ∫ x, ‖partialT φ x‖ ^ 2 ∂cylMeasure +
        σ ^ 2 * ∫ x, ‖β x‖ ^ 2 * ‖φ x‖ ^ 2 ∂cylMeasure +
        σ * ∫ x, ⟪φ x, Matrix.toEuclideanLin
          (antilinearMat (fderiv ℝ β x (1, 0) + Complex.I * fderiv ℝ β x (0, 1)))
          (φ x)⟫ ∂cylMeasure :=
  antilinear_adjoint_energy_aux β hβ hβper σ φ hφ
