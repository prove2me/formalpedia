-- Prove2me | solution 1 for CauchyRiemannIndex.weak_identity_of_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-14T20:50:42.327412+00:00
-- url     : https://prove2.me/submissions/c1496d2a-9fc1-4324-9802-d99566850ca2

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

open MeasureTheory Matrix Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Convolution

namespace CauchyRiemannIndex

lemma crPerC_bdd {E : Type*} [NormedAddCommGroup E] (g : ℝ → E) (hc : Continuous g)
    (hp : Function.Periodic g 1) : ∃ M, ∀ x, ‖g x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hc.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ one_pos x
  rw [hxy]; exact hM y (Ico_subset_Icc_self hy)

/-- Bumps of radius `1/(k+2)`. -/
noncomputable def crPerC_bump (k : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * ((k : ℝ) + 2)), 1 / ((k : ℝ) + 2), by positivity, by
    have : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; linarith⟩

lemma crPerC_bump_tendsto : Tendsto (fun k => (crPerC_bump k).rOut) atTop (𝓝 0) := by
  show Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1) |>.congr
    (fun k => by simp; ring_nf)

section Moll

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma crPerC_conv_bound (k : ℕ) (g : ℝ → E) (M : ℝ) (hg : Continuous g) (hM : ∀ x, ‖g x‖ ≤ M)
    (x : ℝ) :
    ‖((crPerC_bump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ M := by
  set b := (crPerC_bump k).normed volume
  have hbi : Integrable b := (crPerC_bump k).integrable_normed
  rw [convolution_def]
  calc ‖∫ t, (ContinuousLinearMap.lsmul ℝ ℝ) (b t) (g (x - t))‖ ≤ ∫ t, b t * M := by
        refine norm_integral_le_of_norm_le (hbi.mul_const M) (Eventually.of_forall fun t => ?_)
        rw [ContinuousLinearMap.lsmul_apply, norm_smul]
        have hb0 := (crPerC_bump k).nonneg_normed (μ := volume) t
        exact mul_le_mul (le_of_eq (by rw [Real.norm_eq_abs, abs_of_nonneg hb0])) (hM _)
          (norm_nonneg _) hb0
    _ = M := by rw [integral_mul_const, (crPerC_bump k).integral_normed, one_mul]

lemma crPerC_conv_periodic (k : ℕ) (g : ℝ → E) (hp : Function.Periodic g 1) :
    Function.Periodic ((crPerC_bump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      1 := by
  intro x
  simp only [convolution_def]
  congr 1; funext t
  rw [show x + 1 - t = (x - t) + 1 by ring, hp]

lemma crPerC_conv_hasDerivAt (k : ℕ) (g g' : ℝ → E) (M' : ℝ) (hg : Continuous g)
    (hg' : Continuous g') (hd : ∀ x, HasDerivAt g (g' x) x) (hM' : ∀ x, ‖g' x‖ ≤ M')
    (M : ℝ) (hM : ∀ x, ‖g x‖ ≤ M) (x₀ : ℝ) :
    HasDerivAt ((crPerC_bump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g)
      (((crPerC_bump k).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g') x₀) x₀ := by
  set b := (crPerC_bump k).normed volume
  have hbi : Integrable b := (crPerC_bump k).integrable_normed
  have hb0 : ∀ t, 0 ≤ b t := (crPerC_bump k).nonneg_normed
  have hbc : Continuous b := (crPerC_bump k).continuous_normed
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := x₀)
    (F := fun y t => b t • g (y - t)) (F' := fun y t => b t • g' (y - t))
    (bound := fun t => b t * M') (s := univ) univ_mem
    (Eventually.of_forall fun y =>
      (hbc.smul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (by
      refine Integrable.mono' (hbi.mul_const M)
        (hbc.smul (hg.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun t => ?_)
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb0 t)]
      exact mul_le_mul_of_nonneg_left (hM _) (hb0 t))
    ((hbc.smul (hg'.comp (continuous_const.sub continuous_id))).aestronglyMeasurable)
    (Eventually.of_forall fun t y _ => by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hb0 t)]
      exact mul_le_mul_of_nonneg_left (hM' _) (hb0 t))
    (hbi.mul_const M')
    (Eventually.of_forall fun t y _ => ((hd (y - t)).comp_sub_const y t).const_smul (b t))
  have e : ∀ h : ℝ → E, (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) =
      fun y => ∫ t, b t • h (y - t) := by
    intro h; funext y; rw [convolution_def]; rfl
  rw [e g, e g']
  exact key.2

end Moll

lemma crPerC_clm_cont {n : ℕ} :
    Continuous (fun A : Mat n => (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A)) :=
  LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap

lemma crPerC_lin_norm {n : ℕ} (A : Mat n) (v : Vec n) :
    ‖Matrix.toEuclideanLin A v‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) A).le_opNorm v

theorem solution_aux (n : ℕ) (Sinf : ℝ → Mat n) (hS : Continuous Sinf)
    (η f : ℝ → Vec n) (hη : IntegrableOn η (Set.Ico 0 1)) (hf : IntegrableOn f (Set.Ico 0 1))
    (hw : ∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) :
    ∀ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t) := by
  intro ψ hψ hp
  have hψc : Continuous ψ := hψ.continuous
  set ψ' := deriv ψ with hψ'_def
  have hψ'c : Continuous ψ' := hψ.continuous_deriv le_rfl
  have hder : ∀ x, HasDerivAt ψ (ψ' x) x := fun x =>
    ((hψ.differentiable one_ne_zero) x).hasDerivAt
  have hp' : Function.Periodic ψ' 1 := by
    intro x
    have h1 : (fun y => ψ (y + 1)) = ψ := funext hp
    have := deriv_comp_add_const (f := ψ) (a := 1) (x := x)
    rw [h1] at this
    simp only [ψ']; rw [← this]
  obtain ⟨M, hM⟩ := crPerC_bdd ψ hψc hp
  obtain ⟨M', hM'⟩ := crPerC_bdd ψ' hψ'c hp'
  let b : ℕ → ℝ → ℝ := fun k => (crPerC_bump k).normed volume
  let P : ℕ → ℝ → Vec n := fun k => b k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ
  let P' : ℕ → ℝ → Vec n := fun k => b k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ψ'
  have hPd : ∀ k x, HasDerivAt (P k) (P' k x) x := fun k x =>
    crPerC_conv_hasDerivAt k ψ ψ' M' hψc hψ'c hder hM' M hM x
  have hPderiv : ∀ k, deriv (P k) = P' k := fun k => funext fun x => (hPd k x).deriv
  have hPsmooth : ∀ k, ContDiff ℝ ∞ (P k) := fun k =>
    HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (crPerC_bump k).hasCompactSupport_normed (crPerC_bump k).contDiff_normed
      hψc.locallyIntegrable
  have hPc : ∀ k, Continuous (P k) := fun k => (hPsmooth k).continuous
  have hP'c : ∀ k, Continuous (P' k) := fun k => by
    rw [← hPderiv k]; exact (hPsmooth k).continuous_deriv (by simp)
  have hPp : ∀ k, Function.Periodic (P k) 1 := fun k => crPerC_conv_periodic k ψ hp
  have hPb : ∀ k x, ‖P k x‖ ≤ M := fun k x => crPerC_conv_bound k ψ M hψc hM x
  have hP'b : ∀ k x, ‖P' k x‖ ≤ M' := fun k x => crPerC_conv_bound k ψ' M' hψ'c hM' x
  have hPt : ∀ x, Tendsto (fun k => P k x) atTop (𝓝 (ψ x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous crPerC_bump_tendsto hψc x
  have hP't : ∀ x, Tendsto (fun k => P' k x) atTop (𝓝 (ψ' x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous crPerC_bump_tendsto hψ'c x
  -- operator bounds
  let T : ℝ → (Vec n →L[ℝ] Vec n) := fun t => Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ)
    (Sinf t)
  have hTc : Continuous T := crPerC_clm_cont.comp hS
  obtain ⟨MS, hMS⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0 : ℝ) 1)
    hTc.continuousOn
  set MJ := ‖Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (J₀ n)‖
  have hIco : ∀ᵐ t ∂(volume.restrict (Set.Ico (0 : ℝ) 1)), t ∈ Set.Ico (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ico
  have hGb : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin (J₀ n) (P' k t) + Matrix.toEuclideanLin (Sinf t) (P k t)‖ ≤
        MJ * M' + MS * M := by
    intro k t ht
    have h1 := crPerC_lin_norm (J₀ n) (P' k t)
    have h2 := crPerC_lin_norm (Sinf t) (P k t)
    have h3 : ‖T t‖ ≤ MS := hMS t (Ico_subset_Icc_self ht)
    have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hP'b k t)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hPb k t)
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ MJ * M' + MS * M := add_le_add
          (h1.trans (mul_le_mul_of_nonneg_left (hP'b k t) (norm_nonneg _)))
          (h2.trans (mul_le_mul (h3) (hPb k t) (norm_nonneg _) ((norm_nonneg _).trans h3)))
  have hL : Tendsto (fun k => ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ
        (Matrix.toEuclideanLin (J₀ n) (P' k t) + Matrix.toEuclideanLin (Sinf t) (P k t)) (η t))
      atTop (𝓝 (∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (ψ' t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => (MJ * M' + MS * M) * ‖η t‖)
      (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
      (hη.norm.const_mul _) (Eventually.of_forall fun t => ?_)
    · have hc : Continuous fun t =>
          Matrix.toEuclideanLin (J₀ n) (P' k t) + Matrix.toEuclideanLin (Sinf t) (P k t) := by
        have e : (fun t => Matrix.toEuclideanLin (J₀ n) (P' k t) +
            Matrix.toEuclideanLin (Sinf t) (P k t)) =
            fun t => Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (J₀ n) (P' k t) +
              T t (P k t) := rfl
        rw [e]
        exact ((Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (J₀ n)).continuous.comp
          (hP'c k)).add (hTc.clm_apply (hPc k))
      exact hc.aestronglyMeasurable.inner hη.aestronglyMeasurable
    · filter_upwards [hIco] with t ht
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hGb k t ht) (norm_nonneg _))
    · have h1 : Tendsto (fun k => Matrix.toEuclideanLin (J₀ n) (P' k t)) atTop
          (𝓝 (Matrix.toEuclideanLin (J₀ n) (ψ' t))) :=
        ((Matrix.toEuclideanCLM (n := Fin n ⊕ Fin n) (𝕜 := ℝ) (J₀ n)).continuous.tendsto _).comp
          (hP't t)
      have h2 : Tendsto (fun k => Matrix.toEuclideanLin (Sinf t) (P k t)) atTop
          (𝓝 (Matrix.toEuclideanLin (Sinf t) (ψ t))) :=
        ((T t).continuous.tendsto _).comp (hPt t)
      exact (h1.add h2).inner tendsto_const_nhds
  have hR : Tendsto (fun k => ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (P k t) (f t))
      atTop (𝓝 (∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => M * ‖f t‖)
      (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
      (hf.norm.const_mul _) (Eventually.of_forall fun t => ?_)
    · exact (hPc k).aestronglyMeasurable.inner hf.aestronglyMeasurable
    · exact Eventually.of_forall fun t => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hPb k t) (norm_nonneg _))
    · exact (hPt t).inner tendsto_const_nhds
  have heq : ∀ k, ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ
        (Matrix.toEuclideanLin (J₀ n) (P' k t) + Matrix.toEuclideanLin (Sinf t) (P k t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (P k t) (f t) := fun k => by
    have := hw (P k) (hPsmooth k) (hPp k)
    rw [hPderiv k] at this
    exact this
  exact tendsto_nhds_unique (hL.congr heq) hR

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (Sinf : ℝ → Mat n) (hS : Continuous Sinf)
    (η f : ℝ → Vec n) (hη : IntegrableOn η (Set.Ico 0 1)) (hf : IntegrableOn f (Set.Ico 0 1))
    (hw : ∀ ψ : ℝ → Vec n, ContDiff ℝ ∞ ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t)) :
    ∀ ψ : ℝ → Vec n, ContDiff ℝ 1 ψ → Function.Periodic ψ 1 →
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (Matrix.toEuclideanLin (J₀ n) (deriv ψ t) +
        Matrix.toEuclideanLin (Sinf t) (ψ t)) (η t) =
      ∫ t in Set.Ico (0 : ℝ) 1, inner ℝ (ψ t) (f t) :=
  solution_aux n Sinf hS η f hη hf hw
