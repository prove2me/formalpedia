-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T19:03:48.950163+00:00
-- url     : https://prove2.me/submissions/2d128a02-a5c0-4efb-8345-b3c02f175ca8

import Definitions.Def_GaussLocalMaxColoring_Main_Basic
import Definitions.Def_GaussLocalMaxColoring_Main_Iterative
import Definitions.Def_GaussLocalMaxColoring_Main_VectorRounding
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_29

set_option autoImplicit false

/- Bundled module: Solutions.GaussLocalMaxGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem strict_edge_residual_vector_norm_sq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ‖v y+(1/2:ℝ) • v x‖^2=3/4 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hv.1 x,hv.1 y,hv.2 x y hxy,hv.2 y x hxy.symm]
  norm_num [norm_smul, hv.1 x]

theorem strict_edge_residual_vector_norm {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ‖v y+(1/2:ℝ) • v x‖=Real.sqrt 3/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤3 by norm_num)
  have hsq := strict_edge_residual_vector_norm_sq G v hv x y hxy
  have hn := norm_nonneg (v y+(1/2:ℝ) • v x)
  have hp := Real.sqrt_nonneg (3:ℝ)
  nlinarith

theorem strict_edge_residual_eq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    residual v x y=(2/Real.sqrt 3) • (v y+(1/2:ℝ) • v x) := by
  rw [residual,hv.2 x y hxy,neg_smul,sub_neg_eq_add,strict_edge_residual_vector_norm G v hv x y hxy]
  congr 1
  have hs : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp

theorem strict_edge_residual_orthogonal {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ⟪v x,residual v x y⟫=0 := by
  rw [strict_edge_residual_eq G v hv x y hxy]
  simp only [real_inner_smul_right,inner_add_right,real_inner_smul_right,
    hv.2 x y hxy,real_inner_self_eq_norm_sq,hv.1 x]
  ring

theorem strict_edge_residual_norm {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ‖residual v x y‖=1 := by
  have hs : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [strict_edge_residual_eq G v hv x y hxy,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos (by norm_num) hs),strict_edge_residual_vector_norm G v hv x y hxy]
  field_simp

theorem strict_edge_vector_decomposition {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    v y=-(1/2:ℝ) • v x+(Real.sqrt 3/2) • residual v x y := by
  have hs : Real.sqrt (3:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  rw [strict_edge_residual_eq G v hv x y hxy,smul_smul]
  have hcoeff : Real.sqrt (3:ℝ)/2*(2/Real.sqrt 3)=1 := by field_simp
  rw [hcoeff,one_smul]
  module

theorem strict_edge_projection_decomposition {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y)
    (g : Space d) :
    ⟪g,v y⟫=-(1/2:ℝ)*⟪g,v x⟫+(Real.sqrt 3/2)*⟪g,residual v x y⟫ := by
  conv_lhs => rw [strict_edge_vector_decomposition G v hv x y hxy]
  simp only [inner_add_right,real_inner_smul_right]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussian -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_inner_covariance {d : ℕ} (u w : Space d) :
    cov[fun g : Space d => ⟪u,g⟫,fun g : Space d => ⟪w,g⟫;stdGaussian (Space d)]=⟪u,w⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,innerSL_apply_apply]

theorem gaussian_inner_law {d : ℕ} (u : Space d) :
    HasGaussianLaw (fun g : Space d => ⟪u,g⟫) (stdGaussian (Space d)) := by
  exact IsGaussian.hasGaussianLaw_id.map_fun (innerSL ℝ u)

theorem gaussian_inner_mean {d : ℕ} (u : Space d) :
    ∫ g : Space d, ⟪u,g⟫ ∂stdGaussian (Space d)=0 := by
  exact integral_strongDual_stdGaussian (innerSL ℝ u)

theorem gaussian_inner_variance {d : ℕ} (u : Space d) :
    Var[fun g : Space d => ⟪u,g⟫;stdGaussian (Space d)]=‖u‖^2 := by
  rw [← covariance_self (by fun_prop),gaussian_inner_covariance,
    real_inner_self_eq_norm_sq]

theorem gaussian_inner_map {d : ℕ} (u : Space d) (hu : ‖u‖=1) :
    (stdGaussian (Space d)).map (fun g : Space d => ⟪u,g⟫)=gaussianReal 0 1 := by
  rw [(gaussian_inner_law u).map_eq_gaussianReal,gaussian_inner_mean,
    gaussian_inner_variance,hu]
  norm_num

theorem gaussian_inner_map_variance {d : ℕ} (u : Space d) :
    (stdGaussian (Space d)).map (fun g : Space d => ⟪u,g⟫)=
      gaussianReal 0 (‖u‖^2).toNNReal := by
  rw [(gaussian_inner_law u).map_eq_gaussianReal,gaussian_inner_mean,gaussian_inner_variance]

theorem gaussian_inner_ne_zero_ae {d : ℕ} (u : Space d) (hu : u≠0) :
    ∀ᵐ g : Space d ∂stdGaussian (Space d),⟪u,g⟫≠0 := by
  have hv : (‖u‖^2).toNNReal≠0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hu)))
  letI := nullSingletonClass_gaussianReal (μ:=0) hv
  have h := Measure.map_apply (μ:=stdGaussian (Space d)) (f:=fun g : Space d => ⟪u,g⟫)
    (by fun_prop) (measurableSet_singleton (0:ℝ))
  rw [gaussian_inner_map_variance] at h
  simpa only [ae_iff,not_not,Set.preimage,Set.mem_singleton_iff,measure_singleton] using h.symm

theorem gaussian_orthogonal_family_independent {d : ℕ} {ι : Type*} [Fintype ι]
    (u : Space d) (w : ι → Space d) (hw : ∀ i,⟪u,w i⟫=0) :
    IndepFun (fun g : Space d => ⟪u,g⟫) (fun g i => ⟪w i,g⟫)
      (stdGaussian (Space d)) := by
  let L₁ : Space d →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi (fun _ => innerSL ℝ u)
  let L₂ : Space d →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi (fun i => innerSL ℝ (w i))
  have hG : HasGaussianLaw (fun g : Space d => (fun _ : Fin 1 => ⟪u,g⟫,
      fun i : ι => ⟪w i,g⟫)) (stdGaussian (Space d)) :=
    IsGaussian.hasGaussianLaw_id.map_fun (L₁.prod L₂)
  have hI := hG.indepFun_of_covariance_eval (fun _ i => by
    rw [gaussian_inner_covariance,hw i])
  simpa only [Function.comp_def,id_eq] using
    (hI.comp (measurable_pi_apply (0 : Fin 1)) measurable_id)

theorem strict_residuals_independent {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (F : Finset (Fin n)) (x : Fin n) :
    IndepFun (fun g : Space d => ⟪g,v x⟫)
      (fun g (y : ↥(nbr G F x)) => ⟪g,residual v x y⟫)
      (stdGaussian (Space d)) := by
  classical
  simpa only [real_inner_comm] using
    (gaussian_orthogonal_family_independent (v x) (fun y : ↥(nbr G F x) => residual v x y)
      (fun y => strict_edge_residual_orthogonal G v hv x y
        (Finset.mem_filter.mp y.2).2))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def ordinaryResidual {n d : ℕ} (k : ℝ) (v : Fin n→Space d) (x y : Fin n) : Space d :=
  (cA k/(1-⟪v x,v y⟫)) • (v y-⟪v x,v y⟫ • v x)

theorem cA_pos (k : ℝ) (hk : 2 < k) : 0 < cA k := by
  unfold cA
  apply Real.sqrt_pos.mpr
  exact div_pos (by linarith) (by linarith)

theorem cA_sq (k : ℝ) (hk : 2 < k) : (cA k)^2=k/(k-2) := by
  unfold cA
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

theorem ordinary_edge_inner_neg {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) (hxy : G.Adj x y) : ⟪v x,v y⟫ < 0 := by
  have h := hv.2 x y hxy
  have hp : 0 < 1/(k-1) := div_pos zero_lt_one (by linarith)
  linarith

theorem ordinary_residual_orthogonal {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) : ⟪v x,ordinaryResidual k v x y⟫=0 := by
  unfold ordinaryResidual
  simp only [real_inner_smul_right,inner_sub_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hv.1 x]
  ring

theorem ordinary_residual_base_norm_sq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) : ‖v y-⟪v x,v y⟫ • v x‖^2=1-⟪v x,v y⟫^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq,hv.1 y]
  rw [real_inner_comm (v y) (v x)]
  simp only [norm_smul,Real.norm_eq_abs,hv.1 x,mul_one,sq_abs]
  ring

theorem ordinary_residual_norm_le {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) (hxy : G.Adj x y) : ‖ordinaryResidual k v x y‖ ≤ 1 := by
  have hc := cA_pos k hk
  have hneg := ordinary_edge_inner_neg G v k hk hv x y hxy
  have hden : 0 < 1-⟪v x,v y⟫ := by linarith
  have hkm : 0 < k-2 := by linarith
  have hi : (k-1)*⟪v x,v y⟫ ≤ -1 := by
    have h := (mul_le_mul_iff_right₀ (show 0 < k-1 by linarith)).mpr (hv.2 x y hxy)
    field_simp at h
    simpa only [div_self (show k-1≠0 by linarith)] using h
  have hbase := ordinary_residual_base_norm_sq G v k hv x y
  have hn : ‖ordinaryResidual k v x y‖^2=
      (k/(k-2))/(1-⟪v x,v y⟫)^2*(1-⟪v x,v y⟫^2) := by
    rw [ordinaryResidual,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,cA_sq k hk,hbase]
  have hsq : ‖ordinaryResidual k v x y‖^2 ≤ 1 := by
    rw [hn]
    have heq : (k/(k-2))/(1-⟪v x,v y⟫)^2*(1-⟪v x,v y⟫^2)=
        (k*(1+⟪v x,v y⟫))/((k-2)*(1-⟪v x,v y⟫)) := by
      field_simp
      ring
    rw [heq]
    apply (div_le_iff₀ (mul_pos hkm hden)).mpr
    nlinarith [hi]
  nlinarith [norm_nonneg (ordinaryResidual k v x y)]

theorem ordinary_edge_decomposition {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) (hxy : G.Adj x y) :
    v y=⟪v x,v y⟫ • v x+((1-⟪v x,v y⟫)/cA k) • ordinaryResidual k v x y := by
  have hc := (cA_pos k hk).ne'
  have hd : 1-⟪v x,v y⟫≠0 := ne_of_gt (by
    have h := ordinary_edge_inner_neg G v k hk hv x y hxy
    linarith)
  rw [ordinaryResidual,smul_smul]
  have hcoeff : ((1-⟪v x,v y⟫)/cA k)*(cA k/(1-⟪v x,v y⟫))=1 := by field_simp
  rw [hcoeff,one_smul]
  module

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxTail -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_eq_Ioi (a : ℝ) : PhiTail a=(gaussianReal 0 1).real (Set.Ioi a) := by
  rw [PhiTail,Cohen2019.Robust.Phi,cdf_eq_real]
  simpa only [Set.compl_Iic] using
    (probReal_compl_eq_one_sub (μ:=gaussianReal 0 1) (s:=Set.Iic a) measurableSet_Iic).symm

theorem phiTail_pos (a : ℝ) : 0<PhiTail a := by
  rw [phiTail_eq_Ioi,measureReal_def]
  apply ENNReal.toReal_pos (ne_of_gt ?_) (measure_ne_top _ _)
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1:NNReal)≠0)).isOpenPosMeasure
  exact isOpen_Ioi.measure_pos _ Set.nonempty_Ioi

theorem phiTail_nonneg (a : ℝ) : 0≤PhiTail a := le_of_lt (phiTail_pos a)

theorem phiTail_le_one (a : ℝ) : PhiTail a≤1 := by
  rw [PhiTail,Cohen2019.Robust.Phi]
  linarith [cdf_nonneg (gaussianReal 0 1) a]

theorem phiTail_antitone : Antitone PhiTail := by
  intro a b hab
  simp only [PhiTail,Cohen2019.Robust.Phi]
  linarith [monotone_cdf (gaussianReal 0 1) hab]

theorem phiTail_measurable : Measurable PhiTail := by
  exact phiTail_antitone.measurable

theorem independent_gaussian_threshold {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω→ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hI : IndepFun X Y μ)
    (hN : μ.map X=gaussianReal 0 1) (c : ℝ) (hc : 0<c) :
    μ.real {ω | Y ω<c*X ω}=∫ ω,PhiTail (Y ω/c) ∂μ := by
  let E : Set (ℝ×ℝ) := {z | z.1<c*z.2}
  let f : ℝ×ℝ→ℝ := E.indicator 1
  have hE : MeasurableSet E := measurableSet_lt measurable_fst
    (measurable_const.mul measurable_snd)
  have hf : Measurable f := measurable_const.indicator hE
  have hfint : Integrable f ((μ.map Y).prod (gaussianReal 0 1)) := by
    refine (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with z
    by_cases hz : z∈E <;> simp [f,hz]
  calc
    μ.real {ω | Y ω<c*X ω} = ∫ ω,f (Y ω,X ω) ∂μ := by
      simpa only [f,E,Set.indicator_apply,Set.mem_setOf_eq,Pi.one_apply] using
        (integral_indicator_one (μ:=μ) (s:={ω | Y ω<c*X ω})
          (measurableSet_lt hY (measurable_const.mul hX))).symm
    _ = ∫ z,f z ∂μ.map (fun ω => (Y ω,X ω)) :=
      (integral_map (hY.prodMk hX).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z,f z ∂(μ.map Y).prod (gaussianReal 0 1) := by
      rw [hI.symm.map_prod_eq_prod_map_map hY.aemeasurable hX.aemeasurable,hN]
    _ = ∫ y,∫ t,f (y,t) ∂gaussianReal 0 1 ∂μ.map Y := integral_prod f hfint
    _ = ∫ y,PhiTail (y/c) ∂μ.map Y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [phiTail_eq_Ioi,← integral_indicator_one measurableSet_Ioi]
      congr 1
      ext t
      simp only [f,E,Set.indicator_apply,Set.mem_setOf_eq,Set.mem_Ioi,Pi.one_apply]
      simp only [div_lt_iff₀ hc,mul_comm t c]
    _ = ∫ ω,PhiTail (Y ω/c) ∂μ := integral_map hY.aemeasurable
      (phiTail_measurable.comp (measurable_id.div_const c)).aestronglyMeasurable

theorem gaussian_tail_integral_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω→ℝ) (hY : Measurable Y)
    (c a : ℝ) (hc : 0<c) :
    μ.real {ω | Y ω≤a} ≤ (∫ ω,PhiTail (Y ω/c) ∂μ)/PhiTail (a/c) := by
  have hT : Measurable (fun ω => PhiTail (Y ω/c)) :=
    phiTail_measurable.comp (hY.div_const c)
  have hi : Integrable (fun ω => PhiTail (Y ω/c)) μ := by
    refine (integrable_const (1:ℝ)).mono' hT.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (phiTail_nonneg _)]
    exact phiTail_le_one _
  apply (le_div_iff₀ (phiTail_pos _)).mpr
  rw [← smul_eq_mul,← integral_indicator_const (PhiTail (a/c)) (measurableSet_le hY measurable_const)]
  apply integral_mono ((integrable_const _).indicator (measurableSet_le hY measurable_const)) hi
  intro ω
  by_cases h : Y ω≤a
  · simpa [Set.indicator,h] using
      phiTail_antitone ((div_le_div_iff_of_pos_right hc).mpr h)
  · simpa [Set.indicator,h] using phiTail_nonneg (Y ω/c)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxProbability -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem strict_edge_no_tie {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ∀ᵐ g : Space d ∂stdGaussian (Space d),⟪g,v y⟫≠⟪g,v x⟫ := by
  have hne : v y-v x≠0 := by
    intro h
    have hyx := sub_eq_zero.mp h
    have hi := hv.2 x y hxy
    rw [hyx,real_inner_self_eq_norm_sq,hv.1 x] at hi
    norm_num at hi
  simpa only [inner_sub_left,real_inner_comm,sub_ne_zero] using
    gaussian_inner_ne_zero_ae (v y-v x) hne

theorem strict_edge_lt_iff {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y)
    (g : Space d) :
    ⟪g,v y⟫<⟪g,v x⟫ ↔ ⟪g,residual v x y⟫<Real.sqrt 3*⟪g,v x⟫ := by
  have hi := strict_edge_projection_decomposition G v hv x y hxy g
  have hp : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  have hm : Real.sqrt (3:ℝ)*(Real.sqrt 3*⟪g,v x⟫)=3*⟪g,v x⟫ := by
    rw [← mul_assoc,← sq,hs]
  constructor
  · intro h
    apply (mul_lt_mul_iff_right₀ hp).mp
    rw [hm]
    linarith
  · intro h
    have hmul := (mul_lt_mul_iff_right₀ hp).mpr h
    rw [hm] at hmul
    linarith

def finiteMax {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι→ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty z

theorem finiteMax_measurable {ι : Type*} [Fintype ι] [Nonempty ι] :
    Measurable (finiteMax (ι:=ι)) :=
  (Continuous.finset_sup'_apply Finset.univ_nonempty (fun i _ => continuous_apply i)).measurable

theorem finiteMax_lt_iff {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι→ℝ) (a : ℝ) :
    finiteMax z<a ↔ ∀ i,z i<a := by
  simp [finiteMax,Finset.sup'_lt_iff]

theorem finiteMax_le_iff {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι→ℝ) (a : ℝ) :
    finiteMax z≤a ↔ ∀ i,z i≤a := by
  simp [finiteMax,Finset.sup'_le_iff]

theorem nbrMax_eq_coe_finiteMax {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n)
    [Nonempty ↥(nbr G F x)] (g : Space d) :
    nbrMax G v F x g=(finiteMax (fun y : ↥(nbr G F x) => ⟪g,residual v x y⟫):WithBot ℝ) := by
  classical
  rw [finiteMax,Finset.coe_sup']
  have ha : (nbr G F x).attach=Finset.univ := by ext; simp
  rw [← ha]
  simp only [Function.comp_def]
  exact (Finset.sup_attach (nbr G F x)
    (fun y : Fin n => (⟪g,residual v x y⟫:WithBot ℝ))).symm

theorem pLocal_eq_strict_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (hv : StrictVectorColoring G v) (F : Finset (Fin n))
    (x : Fin n) (hx : x∈F) :
    pLocal G v F x=gaussProb {g : Space d | ∀ y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫} := by
  classical
  have ht : ∀ᵐ g : Space d ∂stdGaussian (Space d),
      ∀ y : ↥(nbr G F x),⟪g,v y⟫≠⟪g,v x⟫ := by
    rw [ae_all_iff]
    intro y
    exact strict_edge_no_tie G v hv x y (Finset.mem_filter.mp y.2).2
  unfold pLocal gaussProb
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ht] with g hg
  apply propext
  change (x∈localMax G v F g) ↔ ∀y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫
  simp only [Set.mem_setOf_eq,localMax,Finset.mem_filter,hx,true_and]
  constructor
  · intro h y hy
    exact (h y hy).resolve_right (fun he => hg ⟨y,hy⟩ he.1)
  · intro h y hy
    exact Or.inl (h y hy)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryProbability -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def ordinaryNbrMax {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k : ℝ) (F : Finset (Fin n)) (x : Fin n) (g : Space d) : WithBot ℝ :=
  (nbr G F x).sup (fun y => (⟪g,ordinaryResidual k v x y⟫:WithBot ℝ))

theorem ordinary_edge_lt_iff {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) (hxy : G.Adj x y) (g : Space d) :
    ⟪g,v y⟫<⟪g,v x⟫ ↔ ⟪g,ordinaryResidual k v x y⟫<cA k*⟪g,v x⟫ := by
  have hc := cA_pos k hk
  have hneg := ordinary_edge_inner_neg G v k hk hv x y hxy
  have hd : 0 < 1-⟪v x,v y⟫ := by linarith
  have hi := congrArg (fun z : Space d => ⟪g,z⟫) (ordinary_edge_decomposition G v k hk hv x y hxy)
  simp only [inner_add_right,real_inner_smul_right] at hi
  have heq : ⟪g,v y⟫-⟪g,v x⟫=
      ((1-⟪v x,v y⟫)/cA k)*(⟪g,ordinaryResidual k v x y⟫-cA k*⟪g,v x⟫) := by
    rw [hi]
    field_simp
    ring
  have hp := div_pos hd hc
  constructor
  · intro h
    have hmul : ((1-⟪v x,v y⟫)/cA k)*(⟪g,ordinaryResidual k v x y⟫-cA k*⟪g,v x⟫)<
        ((1-⟪v x,v y⟫)/cA k)*0 := by rw [← heq]; simpa using sub_neg.mpr h
    have h0 := (mul_lt_mul_iff_right₀ hp).mp hmul
    linarith
  · intro h
    have h0 := (mul_lt_mul_iff_right₀ hp).mpr (sub_neg.mpr h)
    rw [mul_zero,← heq] at h0
    exact sub_neg.mp h0

theorem ordinary_edge_no_tie {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (x y : Fin n) (hxy : G.Adj x y) :
    ∀ᵐ g : Space d ∂stdGaussian (Space d),⟪g,v y⟫≠⟪g,v x⟫ := by
  have hne : v y-v x≠0 := by
    intro h
    have hyx := sub_eq_zero.mp h
    have hi := ordinary_edge_inner_neg G v k hk hv x y hxy
    rw [hyx,real_inner_self_eq_norm_sq,hv.1 x] at hi
    norm_num at hi
  simpa only [inner_sub_left,real_inner_comm,sub_ne_zero] using
    gaussian_inner_ne_zero_ae (v y-v x) hne

theorem ordinary_residuals_independent {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) :
    IndepFun (fun g : Space d => ⟪g,v x⟫)
      (fun g (y : ↥(nbr G F x)) => ⟪g,ordinaryResidual k v x y⟫) (stdGaussian (Space d)) := by
  simpa only [real_inner_comm] using
    gaussian_orthogonal_family_independent (v x)
      (fun y : ↥(nbr G F x) => ordinaryResidual k v x y)
      (fun y => ordinary_residual_orthogonal G v k hv x y)

theorem ordinary_pLocal_eq_strict_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (hx : x∈F) :
    pLocal G v F x=gaussProb {g : Space d | ∀y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫} := by
  classical
  have ht : ∀ᵐ g : Space d ∂stdGaussian (Space d),
      ∀y : ↥(nbr G F x),⟪g,v y⟫≠⟪g,v x⟫ := by
    rw [ae_all_iff]
    intro y
    exact ordinary_edge_no_tie G v k hk hv x y (Finset.mem_filter.mp y.2).2
  unfold pLocal gaussProb
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [ht] with g hg
  apply propext
  change (x∈localMax G v F g) ↔ ∀y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫
  simp only [localMax,Finset.mem_filter,hx,true_and]
  constructor
  · intro h y hy
    exact (h y hy).resolve_right (fun he => hg ⟨y,hy⟩ he.1)
  · intro h y hy
    exact Or.inl (h y hy)

theorem ordinaryNbrMax_eq_coe_finiteMax {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (F : Finset (Fin n)) (x : Fin n)
    [Nonempty ↥(nbr G F x)] (g : Space d) :
    ordinaryNbrMax G v k F x g=
      (finiteMax (fun y : ↥(nbr G F x) => ⟪g,ordinaryResidual k v x y⟫):WithBot ℝ) := by
  classical
  rw [finiteMax,Finset.coe_sup']
  have ha : (nbr G F x).attach=Finset.univ := by ext; simp
  rw [← ha]
  simp only [Function.comp_def]
  exact (Finset.sup_attach (nbr G F x)
    (fun y : Fin n => (⟪g,ordinaryResidual k v x y⟫:WithBot ℝ))).symm

theorem ordinary_local_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (hx : x∈F) (a : ℝ) :
    pLocal G v F x=∫g,tailOver (cA k) (ordinaryNbrMax G v k F x g) ∂stdGaussian (Space d) ∧
      gaussProb {g : Space d | ordinaryNbrMax G v k F x g≤(a:WithBot ℝ)} ≤ pLocal G v F x/PhiTail (a/cA k) := by
  classical
  by_cases hS : (nbr G F x).Nonempty
  · letI : Nonempty ↥(nbr G F x) := ⟨⟨hS.choose,hS.choose_spec⟩⟩
    let X : Space d→ℝ := fun g => ⟪g,v x⟫
    let Z : Space d→(↥(nbr G F x)→ℝ) := fun g y => ⟪g,ordinaryResidual k v x y⟫
    let Y : Space d→ℝ := fun g => finiteMax (Z g)
    have hX : Measurable X := by dsimp [X]; fun_prop
    have hZ : Measurable Z := by dsimp [Z]; fun_prop
    have hY : Measurable Y := finiteMax_measurable.comp hZ
    have hI : IndepFun X Y (stdGaussian (Space d)) := by
      simpa only [Function.comp_def,id_eq] using
        ((ordinary_residuals_independent G v k hv F x).comp measurable_id finiteMax_measurable)
    have hN : (stdGaussian (Space d)).map X=gaussianReal 0 1 := by
      simpa only [X,real_inner_comm] using gaussian_inner_map (v x) (hv.1 x)
    have hevent : pLocal G v F x=(stdGaussian (Space d)).real {g : Space d | Y g<cA k*X g} := by
      rw [ordinary_pLocal_eq_strict_probability G v k hk hv F x hx]
      unfold gaussProb
      congr 1
      ext g
      change (∀y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫) ↔ finiteMax (Z g)<cA k*X g
      rw [finiteMax_lt_iff]
      constructor
      · intro h y
        exact (ordinary_edge_lt_iff G v k hk hv x y (Finset.mem_filter.mp y.2).2 g).mp (h y y.2)
      · intro h y hy
        exact (ordinary_edge_lt_iff G v k hk hv x y (Finset.mem_filter.mp hy).2 g).mpr (h ⟨y,hy⟩)
    have hP : pLocal G v F x=∫g,PhiTail (Y g/cA k) ∂stdGaussian (Space d) := by
      rw [hevent]
      exact independent_gaussian_threshold (stdGaussian (Space d)) X Y hX hY hI hN _ (cA_pos k hk)
    have hmax : ∀g,ordinaryNbrMax G v k F x g=(Y g:WithBot ℝ) := ordinaryNbrMax_eq_coe_finiteMax G v k F x
    constructor
    · rw [hP]
      apply integral_congr_ae
      filter_upwards [] with g
      rw [hmax]
      rfl
    · have hb := gaussian_tail_integral_lower_bound (stdGaussian (Space d)) Y hY (cA k) a (cA_pos k hk)
      rw [← hP] at hb
      simpa only [gaussProb,hmax,WithBot.coe_le_coe] using hb
  · have he : nbr G F x=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp : pLocal G v F x=1 := by
      rw [ordinary_pLocal_eq_strict_probability G v k hk hv F x hx]
      simp [he,gaussProb]
    constructor
    · simp [hp,ordinaryNbrMax,he,tailOver]
    · simp only [ordinaryNbrMax,he,Finset.sup_empty,bot_le,Set.setOf_true,gaussProb,probReal_univ,hp]
      exact (le_div_iff₀ (phiTail_pos _)).mpr (by simpa using phiTail_le_one (a/cA k))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxConcentration -/

set_option autoImplicit false
set_option maxHeartbeats 6000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem bounded_empirical_deviation {ι Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι→Ω→ℝ) (hI : iIndepFun X μ) (hX : ∀i,Measurable (X i))
    (hB : ∀i ω,X i ω∈Set.Icc 0 1) (p ε : ℝ) (hmean : ∀i,∫ω,X i ω ∂μ=p)
    (hε : 0 ≤ ε) :
    μ.real {ω | ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p|} ≤
      2*Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
  let S : Ω→ℝ := fun ω => ∑i,(X i ω-p)
  have hR : 0 < (Fintype.card ι:ℝ) := by exact_mod_cast Fintype.card_pos
  have hsub : ∀i,HasSubgaussianMGF (fun ω => X i ω-p) (1/4:NNReal) μ := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ:=μ) (hX i).aemeasurable
      (Eventually.of_forall (hB i))
    rw [hmean i] at h
    norm_num at h ⊢
    exact h
  have hIc : iIndepFun (fun i ω => X i ω-p) μ := by
    simpa only [Function.comp_def] using
      (hI.comp (fun _ z => z-p) (fun _ => measurable_id.sub_const p))
  have hIn : iIndepFun (fun i ω => -(X i ω-p)) μ := by
    simpa only [Function.comp_def] using
      (hIc.comp (fun _ z => -z) (fun _ => measurable_neg))
  have he : -(ε*(Fintype.card ι:ℝ))^2 /
      (2*∑_i : ι,(1/4:NNReal)) = -2*(Fintype.card ι:ℝ)*ε^2 := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,NNReal.coe_mul,
      NNReal.coe_natCast,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat]
    field_simp
    ring
  have hplus : μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ≤
      Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIc (s:=Finset.univ)
      (fun i _ => hsub i) (mul_nonneg hε hR.le)
    simpa only [S,he] using h
  have hminus : μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} ≤
      Real.exp (-2*(Fintype.card ι:ℝ)*ε^2) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hIn (s:=Finset.univ)
      (fun i _ => (hsub i).neg) (mul_nonneg hε hR.le)
    simpa only [S,Finset.sum_neg_distrib,he] using h
  have hS : ∀ω,S ω=(∑i,X i ω)-(Fintype.card ι:ℝ)*p := by
    intro ω
    simp [S,Finset.sum_sub_distrib]
  have hE : {ω | ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p|} ⊆
      {ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ∪ {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} := by
    intro ω hω
    change ε < |(∑i,X i ω)/(Fintype.card ι:ℝ)-p| at hω
    rcases (lt_abs.mp hω) with h|h
    · left
      change ε*(Fintype.card ι:ℝ) ≤ S ω
      rw [hS]
      have hm := (lt_div_iff₀ hR).mp (show ε+p < (∑i,X i ω)/(Fintype.card ι:ℝ) by linarith)
      nlinarith
    · right
      change ε*(Fintype.card ι:ℝ) ≤ -S ω
      rw [hS]
      have hm := (div_lt_iff₀ hR).mp (show (∑i,X i ω)/(Fintype.card ι:ℝ) < p-ε by linarith)
      nlinarith
  calc
    _ ≤ μ.real ({ω | ε*(Fintype.card ι:ℝ) ≤ S ω} ∪
        {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω}) := measureReal_mono hE
    _ ≤ μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ S ω}+
        μ.real {ω | ε*(Fintype.card ι:ℝ) ≤ -S ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxSampling -/

set_option autoImplicit false
set_option maxHeartbeats 6000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurableSet_localMax_mem {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    MeasurableSet {g : Space d | x∈localMax G v F g} := by
  classical
  apply measurableSet_setOfPred.mpr
  simp only [localMax,Finset.mem_filter]
  apply Measurable.and measurable_const
  apply Measurable.forall
  intro y
  apply Measurable.imp measurable_const
  apply Measurable.or
  · exact measurableSet_setOfPred.mp (measurableSet_lt
      (by fun_prop : Measurable fun g : Space d => ⟪g,v y⟫)
      (by fun_prop : Measurable fun g : Space d => ⟪g,v x⟫))
  · exact (measurableSet_setOfPred.mp (measurableSet_eq_fun
      (by fun_prop : Measurable fun g : Space d => ⟪g,v y⟫)
      (by fun_prop : Measurable fun g : Space d => ⟪g,v x⟫))).and measurable_const

theorem measurable_localMax {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) :
    Measurable (localMax G v F) := by
  rw [measurable_finset_iff]
  intro x
  exact measurableSet_setOfPred.mp (measurableSet_localMax_mem G v F x)

def localIndicator {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) (g : Space d) : ℝ :=
  if x∈localMax G v F g then 1 else 0

theorem localIndicator_measurable {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    Measurable (localIndicator G v F x) := by
  classical
  exact Measurable.ite (measurableSet_localMax_mem G v F x) measurable_const measurable_const

theorem localIndicator_range {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) (g : Space d) :
    localIndicator G v F x g∈Set.Icc 0 1 := by
  classical
  dsimp [localIndicator]
  split_ifs <;> norm_num

theorem localIndicator_mean {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n) :
    ∫g,localIndicator G v F x g ∂stdGaussian (Space d)=pLocal G v F x := by
  classical
  simpa only [localIndicator,pLocal,gaussProb,Set.indicator_apply,
    Set.mem_setOf_eq,Pi.one_apply] using
    (integral_indicator_one (μ:=stdGaussian (Space d)) (measurableSet_localMax_mem G v F x))

theorem freq_eq_indicator_sum {n R : ℕ} (I : Fin R→Finset (Fin n)) (x : Fin n) :
    freq I x=(∑i : Fin R,if x∈I i then (1:ℝ) else 0)/R := by
  classical
  rw [freq,Finset.card_filter]
  push_cast
  rfl

theorem fixed_core_deviation {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (x : Fin n)
    (hR : 0 < R) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin R => stdGaussian (Space d)).real
      {ω | ε < |freq (fun i => localMax G v F (ω i)) x-pLocal G v F x|} ≤
      2*Real.exp (-2*R*ε^2) := by
  classical
  letI : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp hR
  let μ : Measure (Fin R→Space d) := Measure.pi fun _ => stdGaussian (Space d)
  let X : Fin R→(Fin R→Space d)→ℝ := fun i ω => localIndicator G v F x (ω i)
  have hI : iIndepFun X μ := iIndepFun_pi (fun _ => (localIndicator_measurable G v F x).aemeasurable)
  have hX : ∀i,Measurable (X i) := fun i =>
    (localIndicator_measurable G v F x).comp (measurable_pi_apply i)
  have hmean : ∀i,∫ω,X i ω ∂μ=pLocal G v F x := by
    intro i
    change (∫ω,localIndicator G v F x (ω i) ∂Measure.pi (fun _ : Fin R => stdGaussian (Space d)))=_
    have hm := measurePreserving_eval (fun _ : Fin R => stdGaussian (Space d)) i
    calc
      _ = ∫g,localIndicator G v F x g ∂
          (Measure.pi (fun _ : Fin R => stdGaussian (Space d))).map (Function.eval i) :=
        (integral_map_of_stronglyMeasurable (measurable_pi_apply i)
          (localIndicator_measurable G v F x).stronglyMeasurable).symm
      _ = ∫g,localIndicator G v F x g ∂stdGaussian (Space d) := by rw [hm.map_eq]
      _ = _ := localIndicator_mean G v F x
  have h := bounded_empirical_deviation μ X hI hX
    (fun i ω => localIndicator_range G v F x (ω i)) (pLocal G v F x) ε hmean hε
  simpa only [freq_eq_indicator_sum,X,localIndicator,Fintype.card_fin] using h

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxAlgorithm -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem localMax_subset {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (F : Finset (Fin n)) (g : Space d) : localMax G v F g ⊆ F := by
  classical
  exact Finset.filter_subset _ _

theorem localMax_independent {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (F : Finset (Fin n)) (g : Space d) : IsIndep G (localMax G v F g) := by
  classical
  intro x hx y hy hxy
  have hxF := (Finset.mem_filter.mp hx).1
  have hyF := (Finset.mem_filter.mp hy).1
  have h₁ := (Finset.mem_filter.mp hx).2 y (Finset.mem_filter.mpr ⟨hyF,hxy⟩)
  have h₂ := (Finset.mem_filter.mp hy).2 x (Finset.mem_filter.mpr ⟨hxF,hxy.symm⟩)
  rcases h₁ with h₁|⟨h₁,hord₁⟩ <;> rcases h₂ with h₂|⟨h₂,hord₂⟩
  · linarith
  · linarith
  · linarith
  · exact (not_lt_of_gt hord₁) hord₂

theorem sampledAt_subset {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (ω : Fin (numLevels n)×Fin R→Space d)
    (F : Finset (Fin n)) (j : ℕ) (i : Fin R) : sampledAt G v ω F j i ⊆ F := by
  unfold sampledAt
  split_ifs
  · exact localMax_subset G v F _
  · exact Finset.empty_subset F

theorem sampledAt_independent {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (ω : Fin (numLevels n)×Fin R→Space d)
    (F : Finset (Fin n)) (j : ℕ) (i : Fin R) : IsIndep G (sampledAt G v ω F j i) := by
  unfold sampledAt
  split_ifs
  · exact localMax_independent G v F _
  · intro x hx
    exact False.elim (Finset.notMem_empty x hx)

theorem alg2Sampled_independent {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (I : Finset (Fin n)) (hI : I∈alg2Sampled G v δ ω) : IsIndep G I := by
  unfold alg2Sampled at hI
  obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hI
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
  exact sampledAt_independent G v ω _ _ i

theorem largest_fold_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (l : List (Finset (Fin n))) (acc : Finset (Fin n))
    (hacc : IsIndep G acc) (hl : ∀I∈l,IsIndep G I) :
    IsIndep G (l.foldl (fun A I => if A.card<I.card then I else A) acc) := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons I l ih =>
    apply ih
    · dsimp only
      split_ifs
      · exact hl I List.mem_cons_self
      · exact hacc
    · intro J hJ
      exact hl J (List.mem_cons_of_mem I hJ)

theorem largest_independent {n : ℕ} (G : SimpleGraph (Fin n))
    (l : List (Finset (Fin n))) (hl : ∀I∈l,IsIndep G I) : IsIndep G (largest l) := by
  apply largest_fold_independent G l ∅ _ hl
  intro x hx
  exact False.elim (Finset.notMem_empty x hx)

theorem largest_fold_card_acc {n : ℕ} (l : List (Finset (Fin n))) (acc : Finset (Fin n)) :
    acc.card ≤ (l.foldl (fun A I => if A.card<I.card then I else A) acc).card := by
  induction l generalizing acc with
  | nil => exact le_rfl
  | cons I l ih =>
    simp only [List.foldl_cons]
    split_ifs with h
    · exact h.le.trans (ih I)
    · exact ih acc

theorem largest_fold_card_mem {n : ℕ} (l : List (Finset (Fin n))) (acc I : Finset (Fin n))
    (hI : I∈l) : I.card ≤ (l.foldl (fun A J => if A.card<J.card then J else A) acc).card := by
  induction l generalizing acc with
  | nil => simp at hI
  | cons J l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hI with rfl|hI
    · by_cases h : acc.card<I.card
      · rw [if_pos h]
        exact largest_fold_card_acc l I
      · rw [if_neg h]
        exact (Nat.le_of_not_gt h).trans (largest_fold_card_acc l acc)
    · exact ih _ hI

theorem largest_card_mem {n : ℕ} (l : List (Finset (Fin n))) (I : Finset (Fin n))
    (hI : I∈l) : I.card ≤ (largest l).card := largest_fold_card_mem l ∅ I hI

theorem alg2_eq_find {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d) :
    alg2 G v δ T ω=(alg2Sampled G v δ ω).find? (fun I => T≤I.card) := rfl

theorem sampleSet_mem_alg2Sampled {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ numLevels n) (i : Fin R) :
    sampleSet G v δ ω j i∈alg2Sampled G v δ ω := by
  unfold alg2Sampled
  apply List.mem_flatMap.mpr
  refine ⟨j-1,List.mem_range.mpr (by omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨i,by simp,?_⟩
  congr 1
  omega

theorem alg2_none_sample_small {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d)
    (hfail : alg2 G v δ T ω=none) (j : ℕ) (hj1 : 1 ≤ j) (hjℓ : j ≤ numLevels n)
    (i : Fin R) : (sampleSet G v δ ω j i).card<T := by
  rw [alg2_eq_find,List.find?_eq_none] at hfail
  have h := hfail _ (sampleSet_mem_alg2Sampled G v δ ω j hj1 hjℓ i)
  simpa only [Bool.not_eq_true,decide_eq_false_iff_not,not_le] using h

theorem trialObtained_card_of_sample {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d)
    (I : Finset (Fin n)) (hI : I∈alg2Sampled G v δ ω) (hT : T ≤ I.card) :
    T ≤ (trialObtained G v δ T ω).card := by
  unfold trialObtained
  rw [alg2_eq_find]
  split
  · rename_i J hJ
    simpa only [decide_eq_true_eq] using List.find?_some hJ
  · exact hT.trans (largest_card_mem _ I hI)

theorem trialObtained_independent {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d) :
    IsIndep G (trialObtained G v δ T ω) := by
  unfold trialObtained
  rw [alg2_eq_find]
  split
  · rename_i I hI
    exact alg2Sampled_independent G v δ ω I (List.mem_of_find?_eq_some hI)
  · exact largest_independent G _ (alg2Sampled_independent G v δ ω)

theorem thm2Output_independent {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl cT : ℝ)
    (ω : Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d) :
    IsIndep G (thm2Output G v k β Cl cT ω) := by
  apply largest_independent
  intro I hI
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hI
  exact trialObtained_independent G v _ _ _

theorem thm2Output_card_trial {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl cT : ℝ)
    (ω : Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d)
    (t : Fin (trialsA cT n)) :
    (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) (fun p => ω (t,p))).card ≤
      (thm2Output G v k β Cl cT ω).card := by
  exact largest_card_mem _ _ (List.mem_ofFn.mpr ⟨t,rfl⟩)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoreCount -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem freq_nonneg {n R : ℕ} (I : Fin R→Finset (Fin n)) (x : Fin n) : 0 ≤ freq I x := by
  unfold freq
  positivity

theorem sum_freq_eq_card {n R : ℕ} (F : Finset (Fin n)) (I : Fin R→Finset (Fin n))
    (hI : ∀i,I i ⊆ F) :
    (∑x∈F,freq I x)=(∑i : Fin R,((I i).card:ℝ))/R := by
  classical
  simp only [freq_eq_indicator_sum,← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_boole]
  have hfilter : F.filter (fun x => x∈I i)=I i := by
    ext x
    simp only [Finset.mem_filter]
    exact ⟨And.right,fun hx => ⟨hI i hx,hx⟩⟩
  rw [hfilter]

theorem deleted_card_lt {n R : ℕ} (F : Finset (Fin n)) (I : Fin R→Finset (Fin n))
    (hI : ∀i,I i ⊆ F) (δ : ℝ) (hδ : 0 < δ) (T : ℕ) (hR : 0 < R)
    (hT : ∀i,(I i).card<T) :
    ((F \ F.filter (fun x => freq I x<δ/2)).card:ℝ)<2*T/δ := by
  classical
  letI : Nonempty (Fin R) := Fin.pos_iff_nonempty.mp hR
  let D := F \ F.filter (fun x => freq I x<δ/2)
  have hD : ∀x∈D,δ/2 ≤ freq I x := by
    intro x hx
    simp only [D,Finset.mem_sdiff,Finset.mem_filter,not_and,not_lt] at hx
    exact hx.2 hx.1
  have hsum : (δ/2)*(D.card:ℝ) ≤ ∑x∈F,freq I x := by
    calc
      _ = ∑_x∈D,δ/2 := by simp; ring
      _ ≤ ∑x∈D,freq I x := Finset.sum_le_sum (fun x hx => hD x hx)
      _ ≤ ∑x∈F,freq I x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun x _ _ => freq_nonneg I x)
  have hsumLT : (∑i : Fin R,((I i).card:ℝ)) < (R:ℝ)*T := by
    calc
      _ < ∑_i : Fin R,(T:ℝ) := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        (fun i _ => by exact_mod_cast hT i)
      _ = _ := by simp
  have htotal : (∑x∈F,freq I x)<T := by
    rw [sum_freq_eq_card F I hI]
    apply (div_lt_iff₀ (show (0:ℝ)<R by exact_mod_cast hR)).mpr
    simpa only [mul_comm] using hsumLT
  apply (lt_div_iff₀ hδ).mpr
  have h := hsum.trans_lt htotal
  change (D.card:ℝ)*δ<2*T
  nlinarith

theorem cores_step_subset {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d) (j : ℕ) :
    cores G v δ ω (j+1) ⊆ cores G v δ ω j := by
  classical
  exact Finset.filter_subset _ _

theorem cores_step_loss_lt {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (hδ : 0 < δ) (T : ℕ)
    (ω : Fin (numLevels n)×Fin R→Space d) (hR : 0 < R) (j : ℕ)
    (hT : ∀i,(sampledAt G v ω (cores G v δ ω j) j i).card<T) :
    ((cores G v δ ω j \ cores G v δ ω (j+1)).card:ℝ)<2*T/δ :=
  deleted_card_lt (cores G v δ ω j) (sampledAt G v ω (cores G v δ ω j) j)
    (sampledAt_subset G v ω _ j) δ hδ T hR hT

theorem cores_card_lower {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (hδ : 0 < δ) (T : ℕ)
    (ω : Fin (numLevels n)×Fin R→Space d) (hR : 0 < R) (j : ℕ)
    (hT : ∀k,k<j → ∀i,(sampledAt G v ω (cores G v δ ω k) k i).card<T) :
    (n:ℝ)-j*(2*T/δ) ≤ ((cores G v δ ω j).card:ℝ) := by
  classical
  induction j with
  | zero => simp [cores]
  | succ j ih =>
    have hprev := ih (fun k hk => hT k (by omega))
    have hstep := (cores_step_loss_lt G v δ hδ T ω hR j (hT j (by omega))).le
    have hcard := Finset.card_sdiff_add_card_eq_card (cores_step_subset G v δ ω j)
    have hcardR :
        ((cores G v δ ω j \ cores G v δ ω (j+1)).card:ℝ)+
          ((cores G v δ ω (j+1)).card:ℝ)=((cores G v δ ω j).card:ℝ) := by
      exact_mod_cast hcard
    push_cast
    nlinarith

theorem failed_core_nonempty_of_budget {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (hδ : 0 < δ) (T : ℕ)
    (ω : Fin (numLevels n)×Fin R→Space d) (hR : 0 < R)
    (hfail : alg2 G v δ T ω=none)
    (hbudget : (numLevels n:ℝ)*(2*T/δ)<n) : (cores G v δ ω (numLevels n)).Nonempty := by
  have hsmall : ∀k,k<numLevels n → ∀i,(sampledAt G v ω (cores G v δ ω k) k i).card<T := by
    intro k hk i
    have h := alg2_none_sample_small G v δ T ω hfail (k+1) (by omega) (by omega) i
    exact h
  have hcard := cores_card_lower G v δ hδ T ω hR (numLevels n) hsmall
  apply Finset.card_pos.mp
  have : (0:ℝ)<(cores G v δ ω (numLevels n)).card := by linarith
  exact_mod_cast this

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowDegree -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_inner_subgaussian_one {d : ℕ} (w : Space d) (hw : ‖w‖ ≤ 1) :
    HasSubgaussianMGF (fun g : Space d => ⟪w,g⟫) 1 (stdGaussian (Space d)) := by
  have hL := gaussian_inner_map_variance w
  refine ⟨?_,?_⟩
  · intro t
    have hi : Integrable (fun z : ℝ => Real.exp (t*z))
        ((stdGaussian (Space d)).map (fun g : Space d => ⟪w,g⟫)) := by
      rw [hL]
      exact integrable_exp_mul_gaussianReal t
    exact (integrable_map_measure (f:=fun g : Space d => ⟪w,g⟫)
      (g:=fun z : ℝ => Real.exp (t*z)) (by fun_prop) (by fun_prop)).mp hi
  · intro t
    rw [mgf_gaussianReal hL]
    simp only [zero_mul,zero_add,NNReal.coe_one,Real.coe_toNNReal _ (sq_nonneg _),one_mul]
    apply Real.exp_le_exp.mpr
    have hn := norm_nonneg w
    nlinarith [mul_nonneg (show 0 ≤ 1-‖w‖^2 by nlinarith) (sq_nonneg t)]

theorem gaussian_inner_upper {d : ℕ} (w : Space d) (hw : ‖w‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    gaussProb {g : Space d | a<⟪g,w⟫} ≤ Real.exp (-(a^2/2)) := by
  have h := (gaussian_inner_subgaussian_one w hw).measure_ge_le ha
  have hsub : {g : Space d | a<⟪g,w⟫} ⊆ {g : Space d | a ≤ ⟪w,g⟫} := by
    intro g hg
    change a<⟪g,w⟫ at hg
    change a ≤ ⟪w,g⟫
    simpa only [real_inner_comm] using hg.le
  exact (measureReal_mono hsub).trans (by simpa only [NNReal.coe_one,mul_one,neg_div] using h)

theorem ordinary_max_upper {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (a : ℝ) (ha : 0 ≤ a) :
    gaussProb {g : Space d | (a:WithBot ℝ)<ordinaryNbrMax G v k F x g} ≤
      (nbr G F x).card*Real.exp (-(a^2/2)) := by
  classical
  have heq : {g : Space d | (a:WithBot ℝ)<ordinaryNbrMax G v k F x g}=
      ⋃y∈nbr G F x,{g : Space d | a<⟪g,ordinaryResidual k v x y⟫} := by
    ext g
    simp [ordinaryNbrMax,Finset.lt_sup_iff]
  unfold gaussProb
  rw [heq]
  calc
    _ ≤ ∑y∈nbr G F x,(stdGaussian (Space d)).real {g : Space d | a<⟪g,ordinaryResidual k v x y⟫} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑_y∈nbr G F x,Real.exp (-(a^2/2)) := Finset.sum_le_sum (fun y hy =>
      gaussian_inner_upper _ (ordinary_residual_norm_le G v k hk hv x y (Finset.mem_filter.mp hy).2) a ha)
    _ = _ := by simp

theorem measurableSet_ordinaryNbrMax_le {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (F : Finset (Fin n)) (x : Fin n) (a : ℝ) :
    MeasurableSet {g : Space d | ordinaryNbrMax G v k F x g≤(a:WithBot ℝ)} := by
  classical
  simp only [ordinaryNbrMax,Finset.sup_le_iff,WithBot.coe_le_coe,Set.setOf_forall]
  apply MeasurableSet.iInter
  intro y
  apply MeasurableSet.iInter
  intro hy
  exact measurableSet_le (by fun_prop) measurable_const

theorem ordinary_pLocal_lower {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β : ℝ) (hk : 2 < k) (hβ : 0 ≤ β)
    (hv : OrdinaryVectorColoring G v k) (hn : 0 < n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) (x : Fin n) :
    pStarA k β n ≤ pLocal G v Finset.univ x := by
  classical
  let a := Real.sqrt (2*Real.log (2*(n:ℝ)^β))
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpow : 1 ≤ (n:ℝ)^β := Real.one_le_rpow hn1 hβ
  have hpowpos : 0 < (n:ℝ)^β := Real.rpow_pos_of_pos hnR β
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a^2=2*Real.log (2*(n:ℝ)^β) :=
    Real.sq_sqrt (mul_nonneg (by norm_num) (Real.log_nonneg (by nlinarith)))
  have he : Real.exp (-(a^2/2))=(2*(n:ℝ)^β)⁻¹ := by
    rw [hasq]
    have heq : -(2*Real.log (2*(n:ℝ)^β)/2)=-Real.log (2*(n:ℝ)^β) := by ring
    rw [heq,Real.exp_neg,Real.exp_log (by positivity)]
  have hcard : ((nbr G Finset.univ x).card:ℝ) ≤ (maxDegOn G Finset.univ:ℝ) := by
    exact_mod_cast Finset.le_sup (f:=fun y => (nbr G Finset.univ y).card) (Finset.mem_univ x)
  have hd := hcard.trans hdeg
  have hhigh : gaussProb {g : Space d | (a:WithBot ℝ)<ordinaryNbrMax G v k Finset.univ x g} ≤ 1/2 := by
    have h := ordinary_max_upper G v k hk hv Finset.univ x a ha
    rw [he] at h
    have hm := mul_le_mul_of_nonneg_right hd (inv_nonneg.mpr (by positivity : 0 ≤ 2*(n:ℝ)^β))
    have hc : (n:ℝ)^β*(2*(n:ℝ)^β)⁻¹=1/2 := by field_simp
    rw [hc] at hm
    exact h.trans hm
  have hlow : (1/2:ℝ) ≤ gaussProb {g : Space d | ordinaryNbrMax G v k Finset.univ x g≤(a:WithBot ℝ)} := by
    have hevent : {g : Space d | (a:WithBot ℝ)<ordinaryNbrMax G v k Finset.univ x g}=
        {g : Space d | ordinaryNbrMax G v k Finset.univ x g≤(a:WithBot ℝ)}ᶜ := by ext; simp
    unfold gaussProb at hhigh ⊢
    rw [hevent,probReal_compl_eq_one_sub (measurableSet_ordinaryNbrMax_le G v k Finset.univ x a)] at hhigh
    linarith
  have hL := (ordinary_local_probability G v k hk hv Finset.univ x (Finset.mem_univ x) a).2
  have hp := (le_div_iff₀ (phiTail_pos (a/cA k))).mp hL
  have hm := mul_le_mul_of_nonneg_right hlow (phiTail_nonneg (a/cA k))
  have hm' : pStarA k β n ≤
      gaussProb {g : Space d | ordinaryNbrMax G v k Finset.univ x g≤(a:WithBot ℝ)}*PhiTail (a/cA k) := by
    simpa only [pStarA,a,div_eq_mul_inv,mul_comm,one_mul] using hm
  exact hm'.trans hp

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussianSymmetry -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_neg_map {d : ℕ} :
    (stdGaussian (Space d)).map (fun g => -g)=stdGaussian (Space d) := by
  simpa using stdGaussian_map (LinearIsometryEquiv.neg ℝ : Space d ≃ₗᵢ[ℝ] Space d)

theorem gaussian_cover_symmetry {d : ℕ} {Y : Type*} [Fintype Y] (u : Y→Space d) (a : ℝ) :
    gaussProb {g : Space d | ∃y,a ≤ ⟪g,u y⟫}=
      gaussProb {g : Space d | ∃y,⟪g,u y⟫ ≤ -a} := by
  have hM : MeasurableSet {g : Space d | ∃y,a ≤ ⟪g,u y⟫} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro y
    exact measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))
  unfold gaussProb
  calc
    (stdGaussian (Space d)).real {g : Space d | ∃y,a ≤ ⟪g,u y⟫}=
        ((stdGaussian (Space d)).map (fun g => -g)).real {g : Space d | ∃y,a ≤ ⟪g,u y⟫} := by rw [gaussian_neg_map]
    _ = (stdGaussian (Space d)).real {g : Space d | ∃y,a ≤ ⟪-g,u y⟫} :=
      map_measureReal_apply (by fun_prop) hM
    _ = _ := by
      congr 1
      ext g
      change (∃y,a ≤ ⟪-g,u y⟫) ↔ ∃y,⟪g,u y⟫ ≤ -a
      simp only [inner_neg_left,le_neg]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussianBlocks -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_orthogonal_blocks_independent {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι→Space d) (w : κ→Space d) (hw : ∀i j,⟪u i,w j⟫=0) :
    IndepFun (fun g : Space d => fun i => ⟪u i,g⟫) (fun g => fun j => ⟪w j,g⟫)
      (stdGaussian (Space d)) := by
  let L₁ : Space d→L[ℝ] (ι→ℝ) := ContinuousLinearMap.pi (fun i => innerSL ℝ (u i))
  let L₂ : Space d→L[ℝ] (κ→ℝ) := ContinuousLinearMap.pi (fun j => innerSL ℝ (w j))
  have hG : HasGaussianLaw (fun g : Space d => (fun i => ⟪u i,g⟫,fun j => ⟪w j,g⟫))
      (stdGaussian (Space d)) := IsGaussian.hasGaussianLaw_id.map_fun (L₁.prod L₂)
  exact hG.indepFun_of_covariance_eval (fun i j => by rw [gaussian_inner_covariance,hw i j])

theorem gaussian_orthogonal_scalars_independent {d : ℕ} (u v : Space d) (h : ⟪u,v⟫=0) :
    IndepFun (fun g : Space d => ⟪u,g⟫) (fun g => ⟪v,g⟫) (stdGaussian (Space d)) := by
  have hi := gaussian_orthogonal_blocks_independent (fun _ : Fin 1 => u)
    (fun _ : Fin 1 => v) (fun _ _ => h)
  simpa only [Function.comp_def] using
    hi.comp (measurable_pi_apply (0:Fin 1)) (measurable_pi_apply (0:Fin 1))

theorem gaussian_orthonormal_pair_map {d : ℕ} (u v : Space d)
    (hu : ‖u‖=1) (hv : ‖v‖=1) (h : ⟪u,v⟫=0) :
    (stdGaussian (Space d)).map (fun g : Space d => (⟪u,g⟫,⟪v,g⟫))=
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  rw [(gaussian_orthogonal_scalars_independent u v h).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    gaussian_inner_map u hu,gaussian_inner_map v hv]

theorem gaussian_pair_family_independent {d : ℕ} {κ : Type*} [Fintype κ]
    (u v : Space d) (w : κ→Space d) (hu : ∀i,⟪u,w i⟫=0) (hv : ∀i,⟪v,w i⟫=0) :
    IndepFun (fun g : Space d => (⟪u,g⟫,⟪v,g⟫)) (fun g i => ⟪w i,g⟫)
      (stdGaussian (Space d)) := by
  have h := gaussian_orthogonal_blocks_independent (![u,v]) w (fun i j => by
    fin_cases i
    · exact hu j
    · exact hv j)
  simpa only [Function.comp_def,id_eq,Matrix.cons_val_zero,Matrix.cons_val_one] using
    h.comp ((measurable_pi_apply (0:Fin 2)).prodMk (measurable_pi_apply (1:Fin 2))) measurable_id

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussianBox -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_coordinate_box_factor {d : ℕ} {κ : Type*} [Fintype κ]
    (u v : Space d) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : ⟪u,v⟫=0)
    (w : κ→Space d) (huw : ∀i,⟪u,w i⟫=0) (hvw : ∀i,⟪v,w i⟫=0)
    (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (B : Set (κ→ℝ)) (hB : MeasurableSet B) :
    (stdGaussian (Space d)).real {g : Space d |
      (⟪u,g⟫∈S ∧ ⟪v,g⟫∈T) ∧ (fun i => ⟪w i,g⟫)∈B} =
      (gaussianReal 0 1).real S*(gaussianReal 0 1).real T*
        (stdGaussian (Space d)).real {g : Space d | (fun i => ⟪w i,g⟫)∈B} := by
  let X : Space d→ℝ×ℝ := fun g => (⟪u,g⟫,⟪v,g⟫)
  let W : Space d→(κ→ℝ) := fun g i => ⟪w i,g⟫
  have hI : IndepFun X W (stdGaussian (Space d)) := gaussian_pair_family_independent u v w huw hvw
  have h := hI.measure_inter_preimage_eq_mul (S ×ˢ T) B (hS.prod hT) hB
  have hR : (stdGaussian (Space d)).real (X ⁻¹' (S ×ˢ T) ∩ W ⁻¹' B)=
      (stdGaussian (Space d)).real (X ⁻¹' (S ×ˢ T))*(stdGaussian (Space d)).real (W ⁻¹' B) := by
    simpa only [measureReal_def,ENNReal.toReal_mul] using congrArg ENNReal.toReal h
  have hM : (stdGaussian (Space d)).real (X ⁻¹' (S ×ˢ T))=
      (gaussianReal 0 1).real S*(gaussianReal 0 1).real T := by
    rw [← map_measureReal_apply (by dsimp [X]; fun_prop) (hS.prod hT),gaussian_orthonormal_pair_map u v hu hv huv]
    exact measureReal_prod_prod _ _
  rw [hM] at hR
  exact hR

theorem gaussian_coordinate_box_polyhedral_factor {d : ℕ} {κ : Type*} [Fintype κ]
    (u v : Space d) (hu : ‖u‖=1) (hv : ‖v‖=1) (huv : ⟪u,v⟫=0)
    (w : κ→Space d) (huw : ∀i,⟪u,w i⟫=0) (hvw : ∀i,⟪v,w i⟫=0)
    (a b c e : ℝ) (A : κ→ℝ) :
    (stdGaussian (Space d)).real {g : Space d |
      (⟪u,g⟫∈Set.Icc a b ∧ ⟪v,g⟫∈Set.Icc c e) ∧ ∀i,⟪w i,g⟫ ≤ A i} =
      (gaussianReal 0 1).real (Set.Icc a b)*(gaussianReal 0 1).real (Set.Icc c e)*
        (stdGaussian (Space d)).real {g : Space d | ∀i,⟪w i,g⟫ ≤ A i} := by
  let B : Set (κ→ℝ) := {z | ∀i,z i ≤ A i}
  have hB : MeasurableSet B := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro i
    exact measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply i) measurable_const)
  exact gaussian_coordinate_box_factor u v hu hv huv w huw hvw _ _ measurableSet_Icc measurableSet_Icc B hB

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrthogonalProjection -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def orthogonalRemainder {d : ℕ} (u w : Space d) : Space d := w-⟪u,w⟫ • u

def normalizedRemainder {d : ℕ} (u w : Space d) : Space d := ‖orthogonalRemainder u w‖⁻¹ • orthogonalRemainder u w

theorem orthogonalRemainder_inner {d : ℕ} (u w : Space d) (hu : ‖u‖=1) :
    ⟪u,orthogonalRemainder u w⟫=0 := by
  simp only [orthogonalRemainder,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hu]
  ring

theorem orthogonalRemainder_norm_sq {d : ℕ} (u w : Space d) (hu : ‖u‖=1) :
    ‖orthogonalRemainder u w‖^2=‖w‖^2-⟪u,w⟫^2 := by
  unfold orthogonalRemainder
  nth_rw 1 [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm w u]
  simp only [norm_smul,Real.norm_eq_abs,hu,mul_one,sq_abs]
  ring

theorem normalizedRemainder_inner {d : ℕ} (u w : Space d) (hu : ‖u‖=1) :
    ⟪u,normalizedRemainder u w⟫=0 := by
  simp only [normalizedRemainder,real_inner_smul_right,orthogonalRemainder_inner u w hu,mul_zero]

theorem normalizedRemainder_norm {d : ℕ} (u w : Space d) (hne : orthogonalRemainder u w≠0) :
    ‖normalizedRemainder u w‖=1 := by
  rw [normalizedRemainder,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hne))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hne)

theorem orthogonalRemainder_pair_norm {d : ℕ} (u v : Space d) (hu : ‖u‖=1) (hv : ‖v‖=1) :
    ‖orthogonalRemainder u v‖=‖orthogonalRemainder v u‖ := by
  have h₁ := orthogonalRemainder_norm_sq u v hu
  have h₂ := orthogonalRemainder_norm_sq v u hv
  rw [hv] at h₁
  rw [hu] at h₂
  have hi : ⟪v,u⟫=⟪u,v⟫ := real_inner_comm _ _
  rw [hi] at h₂
  nlinarith [norm_nonneg (orthogonalRemainder u v),norm_nonneg (orthogonalRemainder v u)]

theorem orthogonalRemainder_other_inner {d : ℕ} (u e w : Space d)
    (huw : ⟪u,w⟫=0) (hue : ⟪u,e⟫=0) : ⟪u,orthogonalRemainder e w⟫=0 := by
  simp only [orthogonalRemainder,inner_sub_right,real_inner_smul_right,huw,hue,mul_zero,sub_zero]

theorem orthogonalRemainder_decomposition {d : ℕ} (u w : Space d) :
    w=⟪u,w⟫ • u+orthogonalRemainder u w := by unfold orthogonalRemainder; module

theorem orthogonalRemainder_budget {d : ℕ} (e w : Space d) (he : ‖e‖=1) (hw : ‖w‖ ≤ 1) :
    ⟪e,w⟫^2+‖orthogonalRemainder e w‖^2 ≤ 1 := by
  rw [orthogonalRemainder_norm_sq e w he]
  nlinarith [norm_nonneg w]

theorem unit_inner_abs_le_one {d : ℕ} (e w : Space d) (he : ‖e‖=1) (hw : ‖w‖ ≤ 1) :
    |⟪e,w⟫| ≤ 1 := by
  have h := abs_real_inner_le_norm e w
  rw [he,one_mul] at h
  exact h.trans hw

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryBox -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_real_interval_pos (a b : ℝ) (hab : a<b) :
    0<(gaussianReal 0 1).real (Set.Icc a b) := by
  letI : (gaussianReal 0 1).IsOpenPosMeasure :=
    (gaussianReal_absolutelyContinuous' 0 (show (1:NNReal)≠0 by norm_num)).isOpenPosMeasure
  have h : 0<gaussianReal 0 1 (Set.Ioo a b) :=
    isOpen_Ioo.measure_pos (gaussianReal 0 1) (Set.nonempty_Ioo.mpr hab)
  apply ENNReal.toReal_pos
  · exact ne_of_gt (lt_of_lt_of_le h (measure_mono Set.Ioo_subset_Icc_self))
  · exact measure_ne_top _ _

theorem gaussian_real_Ioc_eq_Icc (a b : ℝ) :
    (gaussianReal 0 1).real (Set.Ioc a b)=(gaussianReal 0 1).real (Set.Icc a b) := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  exact congrArg ENNReal.toReal (measure_congr Ioc_ae_eq_Icc)

def ordinaryBoxProjection {n d : ℕ} (k : ℝ) (v : Fin n→Space d)
    (x : Fin n) (e : Space d) (y : Fin n) : ℝ := ⟪e,ordinaryResidual k v x y⟫

def ordinaryBoxResidual {n d : ℕ} (k : ℝ) (v : Fin n→Space d)
    (x : Fin n) (e : Space d) (y : Fin n) : Space d :=
  orthogonalRemainder e (ordinaryResidual k v x y)

def ordinaryBoxEvent {n d : ℕ} (G : SimpleGraph (Fin n)) (k : ℝ)
    (v : Fin n→Space d) (F : Finset (Fin n)) (x : Fin n) (e : Space d) (a b t : ℝ) : Set (Space d) :=
  {g | ∀y∈nbr G F x,⟪ordinaryBoxResidual k v x e y,g⟫ ≤
    (cA k*a-b*ordinaryBoxProjection k v x e y)*t-1/t}

theorem ordinary_box_subset_strict_local {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (e : Space d) (he : ‖e‖=1)
    (a b t : ℝ) (ht : 0<t) :
    {g : Space d | (⟪v x,g⟫∈Set.Ioc (a*t) (a*t+1/t) ∧
      ⟪e,g⟫∈Set.Icc (b*t) (b*t+1/t)) ∧ g∈ordinaryBoxEvent G k v F x e a b t} ⊆
      {g : Space d | ∀y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫} := by
  classical
  intro g hg y hy
  apply (ordinary_edge_lt_iff G v k hk hv x y (Finset.mem_filter.mp hy).2 g).mpr
  have hξ : ordinaryBoxProjection k v x e y ≤ 1 :=
    (le_abs_self _).trans (unit_inner_abs_le_one e _ he
      (ordinary_residual_norm_le G v k hk hv x y (Finset.mem_filter.mp hy).2))
  have hδ₀ : 0 ≤ ⟪e,g⟫-b*t := by linarith [hg.1.2.1]
  have hδ₁ : ⟪e,g⟫-b*t ≤ 1/t := by linarith [hg.1.2.2]
  have hξδ : ordinaryBoxProjection k v x e y*(⟪e,g⟫-b*t) ≤ 1/t :=
    (mul_le_mul_of_nonneg_right hξ hδ₀).trans (by simpa using hδ₁)
  have hW := hg.2 y hy
  have hdecomp := congrArg (fun z : Space d => ⟪g,z⟫)
    (orthogonalRemainder_decomposition e (ordinaryResidual k v x y))
  simp only [inner_add_right,real_inner_smul_right] at hdecomp
  have hinner : ⟪g,ordinaryResidual k v x y⟫ ≤ cA k*(a*t) := by
    change ⟪ordinaryBoxResidual k v x e y,g⟫ ≤ _ at hW
    rw [hdecomp]
    unfold ordinaryBoxProjection at hW hξδ
    unfold ordinaryBoxResidual at hW
    have hi₁ : ⟪g,e⟫=⟪e,g⟫ := real_inner_comm _ _
    have hi₂ : ⟪g,orthogonalRemainder e (ordinaryResidual k v x y)⟫=
      ⟪orthogonalRemainder e (ordinaryResidual k v x y),g⟫ := real_inner_comm _ _
    rw [hi₁,hi₂]
    nlinarith
  have hstrict : cA k*(a*t)<cA k*⟪g,v x⟫ := by
    apply mul_lt_mul_of_pos_left _ (cA_pos k hk)
    simpa only [real_inner_comm] using hg.1.1.1
  exact hinner.trans_lt hstrict

theorem ordinary_box_probability_bound {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (hx : x∈F) (e : Space d) (he : ‖e‖=1)
    (hxe : ⟪v x,e⟫=0) (a b t : ℝ) (ht : 0<t) :
    gaussProb (ordinaryBoxEvent G k v F x e a b t) ≤ pLocal G v F x/
      ((gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t))*
        (gaussianReal 0 1).real (Set.Icc (b*t) (b*t+1/t))) := by
  classical
  let w : ↥(nbr G F x)→Space d := fun y => ordinaryBoxResidual k v x e y
  let A : ↥(nbr G F x)→ℝ := fun y => (cA k*a-b*ordinaryBoxProjection k v x e y)*t-1/t
  have huw : ∀y,⟪v x,w y⟫=0 := fun y =>
    orthogonalRemainder_other_inner (v x) e _ (ordinary_residual_orthogonal G v k hv x y) hxe
  have hew : ∀y,⟪e,w y⟫=0 := fun y => orthogonalRemainder_inner e _ he
  let B : Set (↥(nbr G F x)→ℝ) := {z | ∀y,z y ≤ A y}
  have hB : MeasurableSet B := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro y
    exact measurableSet_setOfPred.mp (measurableSet_le (measurable_pi_apply y) measurable_const)
  have hfactor := gaussian_coordinate_box_factor (v x) e (hv.1 x) he hxe w huw hew
    (Set.Ioc (a*t) (a*t+1/t)) (Set.Icc (b*t) (b*t+1/t)) measurableSet_Ioc measurableSet_Icc B hB
  have hset : {g : Space d | (fun y => ⟪w y,g⟫)∈B}=ordinaryBoxEvent G k v F x e a b t := by
    ext g
    change (∀y:↥(nbr G F x),⟪ordinaryBoxResidual k v x e y,g⟫≤A y) ↔ _
    exact Subtype.forall
  rw [hset,gaussian_real_Ioc_eq_Icc] at hfactor
  have hle : (gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t))*
      (gaussianReal 0 1).real (Set.Icc (b*t) (b*t+1/t))*
      gaussProb (ordinaryBoxEvent G k v F x e a b t) ≤ pLocal G v F x := by
    rw [ordinary_pLocal_eq_strict_probability G v k hk hv F x hx]
    unfold gaussProb
    rw [← hfactor]
    apply measureReal_mono _ (measure_ne_top _ _)
    intro g hg
    apply ordinary_box_subset_strict_local G v k hk hv F x e he a b t ht
    exact ⟨hg.1,(Set.ext_iff.mp hset g).mp hg.2⟩
  have hp₁ : 0<(gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t)) :=
    gaussian_real_interval_pos _ _ (by linarith [one_div_pos.mpr ht])
  have hp₂ : 0<(gaussianReal 0 1).real (Set.Icc (b*t) (b*t+1/t)) :=
    gaussian_real_interval_pos _ _ (by linarith [one_div_pos.mpr ht])
  exact (le_div_iff₀ (mul_pos hp₁ hp₂)).mpr (by simpa only [mul_comm] using hle)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryPlane -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def ordinaryPlaneAxis {n d : ℕ} (v : Fin n→Space d) (r x : Fin n) : Space d :=
  normalizedRemainder (v x) (v r)

theorem ordinary_plane_axis_unit {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x : Fin n) (hx : 0<‖uvec v r x‖) : ‖ordinaryPlaneAxis v r x‖=1 := by
  apply normalizedRemainder_norm
  have hp := orthogonalRemainder_pair_norm (v x) (v r) (hv.1 x) (hv.1 r)
  have hr : orthogonalRemainder (v r) (v x)=uvec v r x := rfl
  rw [hr] at hp
  apply norm_ne_zero_iff.mp
  rw [hp]
  exact hx.ne'

theorem ordinary_plane_axis_orthogonal {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x : Fin n) : ⟪v x,ordinaryPlaneAxis v r x⟫=0 :=
  normalizedRemainder_inner (v x) (v r) (hv.1 x)

theorem ordinary_plane_residual_budget {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y) :
    (ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y)^2+
      ‖ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y‖^2 ≤ 1 :=
  orthogonalRemainder_budget _ _ (ordinary_plane_axis_unit G v k hv r x hx)
    (ordinary_residual_norm_le G v k hk hv x y hxy)

theorem ordinary_plane_residual_orthogonal {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) :
    ⟪v x,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫=0 ∧
      ⟪ordinaryPlaneAxis v r x,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫=0 :=
  ⟨orthogonalRemainder_other_inner _ _ _ (ordinary_residual_orthogonal G v k hv x y)
      (ordinary_plane_axis_orthogonal G v k hv r x),
    orthogonalRemainder_inner _ _ (ordinary_plane_axis_unit G v k hv r x hx)⟩

theorem ordinary_plane_box_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (r x : Fin n) (hxF : x∈F) (hx : 0<‖uvec v r x‖)
    (a b t : ℝ) (ht : 0<t) :
    gaussProb (ordinaryBoxEvent G k v F x (ordinaryPlaneAxis v r x) a b t) ≤ pLocal G v F x/
      ((gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t))*
        (gaussianReal 0 1).real (Set.Icc (b*t) (b*t+1/t))) :=
  ordinary_box_probability_bound G v k hk hv F x hxF _
    (ordinary_plane_axis_unit G v k hv r x hx) (ordinary_plane_axis_orthogonal G v k hv r x) a b t ht

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxPlaneGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem orthogonalRemainder_linear {d : ℕ} (r u w : Space d) (a b : ℝ) :
    orthogonalRemainder r (a • u+b • w)=
      a • orthogonalRemainder r u+b • orthogonalRemainder r w := by
  simp only [orthogonalRemainder,inner_add_right,real_inner_smul_right]
  module

theorem orthogonalRemainder_of_orthogonal {d : ℕ} (r w : Space d) (h : ⟪r,w⟫=0) :
    orthogonalRemainder r w=w := by simp only [orthogonalRemainder,h,zero_smul,sub_zero]

theorem orthogonalRemainder_self {d : ℕ} (r : Space d) (hr : ‖r‖=1) :
    orthogonalRemainder r r=0 := by
  simp only [orthogonalRemainder,real_inner_self_eq_norm_sq,hr,one_pow,one_smul,sub_self]

theorem ordinary_plane_axis_eq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k) (r x : Fin n) :
    ordinaryPlaneAxis v r x=‖uvec v r x‖⁻¹ • (v r-rho v r x • v x) := by
  unfold ordinaryPlaneAxis normalizedRemainder
  have hn := orthogonalRemainder_pair_norm (v x) (v r) (hv.1 x) (hv.1 r)
  change ‖orthogonalRemainder (v x) (v r)‖=‖uvec v r x‖ at hn
  rw [hn]
  congr 1
  unfold orthogonalRemainder rho
  have hi : ⟪v x,v r⟫=⟪v r,v x⟫ := real_inner_comm _ _
  rw [hi]

theorem ordinary_plane_axis_span {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x : Fin n) (hx : 0<‖uvec v r x‖) :
    v r=rho v r x • v x+‖uvec v r x‖ • ordinaryPlaneAxis v r x := by
  rw [ordinary_plane_axis_eq G v k hv r x,smul_smul,mul_inv_cancel₀ hx.ne',one_smul]
  module

theorem ordinary_plane_residual_root_orthogonal {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) :
    ⟪v r,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫=0 := by
  have h₁ := ordinary_plane_residual_orthogonal G v k hv r x y hx
  rw [ordinary_plane_axis_span G v k hv r x hx,inner_add_left,real_inner_smul_left,real_inner_smul_left,
    h₁.1,h₁.2,mul_zero,mul_zero,add_zero]

theorem ordinary_plane_axis_projected {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x : Fin n) (hx : 0<‖uvec v r x‖) :
    orthogonalRemainder (v r) (ordinaryPlaneAxis v r x)=
      (-(rho v r x)/‖uvec v r x‖) • uvec v r x := by
  rw [ordinary_plane_axis_eq G v k hv r x]
  have heq : ‖uvec v r x‖⁻¹ • (v r-rho v r x • v x)=
      ‖uvec v r x‖⁻¹ • v r+(-(rho v r x)/‖uvec v r x‖) • v x := by
    simp only [div_eq_mul_inv]
    module
  rw [heq,orthogonalRemainder_linear,orthogonalRemainder_self (v r) (hv.1 r),smul_zero,zero_add]
  rfl

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryTransmission -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem orthogonalRemainder_add {d : ℕ} (r u w : Space d) :
    orthogonalRemainder r (u+w)=orthogonalRemainder r u+orthogonalRemainder r w := by
  simpa only [one_smul] using orthogonalRemainder_linear r u w 1 1

theorem orthogonalRemainder_smul {d : ℕ} (r u : Space d) (a : ℝ) :
    orthogonalRemainder r (a • u)=a • orthogonalRemainder r u := by
  simp only [orthogonalRemainder,real_inner_smul_right]
  module

theorem ordinary_edge_projected_decomposition {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y) :
    uvec v r y=⟪v x,v y⟫ • uvec v r x+((1-⟪v x,v y⟫)/cA k) •
      (((ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y)*(-(rho v r x)/‖uvec v r x‖)) •
        uvec v r x+ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y) := by
  have h := congrArg (orthogonalRemainder (v r)) (ordinary_edge_decomposition G v k hk hv x y hxy)
  have hq : ordinaryResidual k v x y=
      ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y • ordinaryPlaneAxis v r x+
        ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y :=
    orthogonalRemainder_decomposition _ _
  rw [orthogonalRemainder_add,orthogonalRemainder_smul,orthogonalRemainder_smul] at h
  rw [hq,orthogonalRemainder_add,orthogonalRemainder_smul,
    ordinary_plane_axis_projected G v k hv r x hx,
    orthogonalRemainder_of_orthogonal _ _ (ordinary_plane_residual_root_orthogonal G v k hv r x y hx),smul_smul] at h
  exact h

theorem ordinary_edge_projected_score {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y)
    (g : Space d) (L t : ℝ)
    (hg : ⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫ = -L*t) :
    ⟪g,uvec v r y⟫=(-⟪v x,v y⟫)*(‖uvec v r x‖*L)*t+
      ((1-⟪v x,v y⟫)/cA k)*(⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
        L*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t) := by
  have hgi : ⟪g,uvec v r x⟫ = -(‖uvec v r x‖*L)*t := by
    have h := congrArg (fun a : ℝ => ‖uvec v r x‖*a) hg
    simp only [real_inner_smul_right,← mul_assoc,mul_inv_cancel₀ hx.ne',one_mul] at h
    nlinarith
  rw [ordinary_edge_projected_decomposition G v k hk hv r x y hx hxy]
  simp only [inner_add_right,real_inner_smul_right,hgi]
  field_simp
  <;> ring

theorem ordinary_transmission_lower {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y)
    (g : Space d) (L B t : ℝ) (ht : 0 ≤ t)
    (hg : ⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫ = -L*t)
    (hB : -(cA k*(‖uvec v r x‖*L)) ≤ B)
    (hQ : B*t ≤ ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
      L*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t) :
    ((1/(k-1))*(‖uvec v r x‖*L)+((1+1/(k-1))/cA k)*B)*t ≤ ⟪g,uvec v r y⟫ := by
  let η := -⟪v x,v y⟫
  let ell := 1/(k-1)
  let U := ‖uvec v r x‖*L
  have hc := cA_pos k hk
  have hηell : ell ≤ η := by dsimp [ell,η]; linarith [hv.2 x y hxy]
  have hell : 0<ell := div_pos zero_lt_one (by linarith)
  have hη : 0<η := hell.trans_le hηell
  have hmult : 0 ≤ (1+η)/cA k := (div_pos (by linarith) hc).le
  have hUB : 0 ≤ U+B/cA k := by
    have hb : -U ≤ B/cA k := (le_div_iff₀ hc).mpr (by dsimp [U]; nlinarith [hB])
    linarith
  have hbase : ell*U+(1+ell)/cA k*B ≤ η*U+(1+η)/cA k*B := by
    have hp := mul_nonneg (sub_nonneg.mpr hηell) hUB
    have heq : η*U+(1+η)/cA k*B-(ell*U+(1+ell)/cA k*B)=(η-ell)*(U+B/cA k) := by ring
    linarith
  rw [ordinary_edge_projected_score G v k hk hv r x y hx hxy g L t hg]
  change (ell*U+(1+ell)/cA k*B)*t ≤ η*U*t+((1+η)/cA k)*_
  exact (mul_le_mul_of_nonneg_right hbase ht).trans (by
    have h := mul_le_mul_of_nonneg_left hQ hmult
    nlinarith)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverSliceGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def planeNeighborScore {n d : ℕ} (v : Fin n→Space d) (k : ℝ) (r x y : Fin n) (z w : ℝ) : ℝ :=
  (-⟪v x,v y⟫)*‖uvec v r x‖*z+((1-⟪v x,v y⟫)/cA k)*
    (w+z*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y)

theorem plane_neighbor_score_eq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y) (g : Space d) :
    ⟪g,uvec v r y⟫=planeNeighborScore v k r x y (-⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫)
      ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫ := by
  have h := ordinary_edge_projected_score G v k hk hv r x y hx hxy g
    (-⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫) 1 (by ring)
  simpa only [planeNeighborScore,mul_one,mul_assoc] using h

theorem scalar_transmission_lower (c η ell U B Q t : ℝ) (hc : 0<c)
    (hell : 0 ≤ ell) (hη : ell ≤ η) (ht : 0 ≤ t)
    (hB : -(c*U) ≤ B) (hQ : B*t ≤ Q) :
    (ell*U+(1+ell)/c*B)*t ≤ η*U*t+((1+η)/c)*Q := by
  have hη0 : 0 ≤ η := hell.trans hη
  have hmult : 0 ≤ (1+η)/c := div_nonneg (by linarith) hc.le
  have hUB : 0 ≤ U+B/c := by
    have h : -U ≤ B/c := (le_div_iff₀ hc).mpr (by nlinarith only [hB])
    linarith only [h]
  have hbase : ell*U+(1+ell)/c*B ≤ η*U+(1+η)/c*B := by
    have hp := mul_nonneg (sub_nonneg.mpr hη) hUB
    have heq : η*U+(1+η)/c*B-(ell*U+(1+ell)/c*B)=(η-ell)*(U+B/c) := by ring
    linarith only [hp,heq]
  have h₁ := mul_le_mul_of_nonneg_right hbase ht
  have h₂ := mul_le_mul_of_nonneg_left hQ hmult
  nlinarith only [h₁,h₂]

theorem ordinary_root_residual_norm_sq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k) (r x : Fin n) :
    ‖uvec v r x‖^2=1-(rho v r x)^2 := by
  have h := orthogonalRemainder_norm_sq (v r) (v x) (hv.1 r)
  simpa only [orthogonalRemainder,uvec,rho,hv.1 x,one_pow] using h

theorem ordinary_root_rho_mem {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k) (r x : Fin n) :
    rho v r x∈Set.Icc (-1) 1 := by
  exact abs_le.mp (unit_inner_abs_le_one (v r) (v x) (hv.1 r) (hv.1 x).le)

theorem ordinary_root_residual_norm_le {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k) (r x : Fin n) :
    ‖uvec v r x‖ ≤ 1 := by
  have h := ordinary_root_residual_norm_sq G v k hv r x
  nlinarith only [h,norm_nonneg (uvec v r x),sq_nonneg (rho v r x)]

theorem ordinary_plane_residual_inner_root_axis {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hv : OrdinaryVectorColoring G v k)
    (r x y : Fin n) (hx : 0<‖uvec v r x‖) :
    ⟪uvec v r x,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫=0 := by
  have h₁ := (ordinary_plane_residual_orthogonal G v k hv r x y hx).1
  have h₂ := ordinary_plane_residual_root_orthogonal G v k hv r x y hx
  simp only [uvec,inner_sub_left,real_inner_smul_left,h₁,h₂,mul_zero,sub_zero]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverSliceScalar -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem scalar_drift_transmission (c ell η U U' ψ E w t Q : ℝ)
    (hc : 0<c) (hell : ell∈Set.Icc (0:ℝ) 1) (hη : ell ≤ η)
    (hU : 0 ≤ U') (hUU : U ≤ U') (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hDrift : (1-ell)*U'+(((1+ell)/c)*E+40)*w ≤ ((1+ell)/c)*ψ)
    (hQ : (ψ-E*w)*t ≤ Q) :
    (U+40*w)*t ≤ η*U'*t+((1+η)/c)*Q := by
  have hA : 0<(1+ell)/c := div_pos (by linarith [hell.1]) hc
  have hbase : 0 ≤ (1-ell)*U'+40*w := by
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hell.2) hU) (by positivity)
  have hBprod : 0 ≤ ((1+ell)/c)*(ψ-E*w) := by nlinarith only [hDrift,hbase]
  have hB0 : 0 ≤ ψ-E*w := nonneg_of_mul_nonneg_right hBprod hA
  have hB : -(c*U') ≤ ψ-E*w := le_trans (neg_nonpos.mpr (mul_nonneg hc.le hU)) hB0
  have hthreshold : U'+40*w ≤ ell*U'+((1+ell)/c)*(ψ-E*w) := by nlinarith only [hDrift]
  have hstep := scalar_transmission_lower c η ell U' (ψ-E*w) Q t hc hell.1 hη ht hB hQ
  apply le_trans _ hstep
  have h0 : U+40*w ≤ U'+40*w := by linarith only [hUU]
  exact mul_le_mul_of_nonneg_right (h0.trans hthreshold) ht

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxThresholdOptimization -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def thresholdPsi (c ν s : ℝ) : ℝ :=
  if s ≤ ν then c*Real.sqrt (1-s^2) else c*(1-ν*s)/Real.sqrt (1-ν^2)

theorem threshold_optimization (c ν D x y s S : ℝ)
    (hc : 0<c) (hν : 0<ν) (hν1 : ν<1) (hD : 0 ≤ D)
    (hrel : D*(1-ν^2)=c^2*(1+D*ν^2))
    (hy : 0 ≤ y) (hs : 0 ≤ s) (hsq : s^2=x^2+y^2) (hsS : s ≤ S) (hS : ν ≤ S) :
    ∃a b μ κ θ : ℝ,
      Real.sqrt (1-ν^2) ≤ a ∧ |b| ≤ ν ∧ 0 ≤ μ ∧ μ ≤ ν ∧ 0 ≤ κ ∧
      0 ≤ θ ∧ θ ≤ (S/ν-1)/(D+1) ∧ a^2+b^2+μ^2=1 ∧
      μ+θ*(μ+κ)=y ∧
      (1+θ)*c*a-Real.sqrt ((x-(1+θ)*b)^2+θ^2*(D+κ^2))=thresholdPsi c ν s := by
  have hνsq : 0<1-ν^2 := by nlinarith
  have ha : 0<Real.sqrt (1-ν^2) := Real.sqrt_pos.mpr hνsq
  have ha2 : (Real.sqrt (1-ν^2))^2=1-ν^2 := Real.sq_sqrt hνsq.le
  have hD1 : 0<D+1 := by linarith
  have hbar : 0 ≤ (S/ν-1)/(D+1) := by
    apply div_nonneg _ hD1.le
    have h : 1 ≤ S/ν := (le_div_iff₀ hν).mpr (by simpa using hS)
    linarith
  by_cases hsmall : s ≤ ν
  · have hss : 0 ≤ 1-s^2 := by nlinarith
    have hx : |x| ≤ s := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg y]
    have hyS : y ≤ s := by nlinarith [sq_nonneg x]
    refine ⟨Real.sqrt (1-s^2),x,y,0,0,?_,hx.trans hsmall,hy,hyS.trans hsmall,le_rfl,le_rfl,hbar,?_,?_,?_⟩
    · apply Real.sqrt_le_sqrt
      nlinarith
    · rw [Real.sq_sqrt hss]
      nlinarith
    · ring
    · simp only [thresholdPsi,if_pos hsmall,zero_add,one_mul,zero_mul,add_zero,mul_zero,sub_self,
        zero_pow (by norm_num : (2:ℕ)≠0),Real.sqrt_zero,sub_zero]
  · have hsν : ν<s := lt_of_not_ge hsmall
    have hs0 : 0<s := hν.trans hsν
    let a := Real.sqrt (1-ν^2)
    let b := ν*x/s
    let μ := ν*y/s
    let κ := D*μ
    let θ := (s/ν-1)/(D+1)
    have hbμ : b^2+μ^2=ν^2 := by
      dsimp [b,μ]
      field_simp [hs0.ne']
      nlinarith only [hsq]
    have hμ : 0 ≤ μ := div_nonneg (mul_nonneg hν.le hy) hs0.le
    have hb : |b| ≤ ν := by
      apply abs_le.mpr
      constructor <;> nlinarith [sq_nonneg μ]
    have hμν : μ ≤ ν := by nlinarith [sq_nonneg b]
    have hκ : 0 ≤ κ := mul_nonneg hD hμ
    have hθ : 0 ≤ θ := by
      apply div_nonneg _ hD1.le
      have h : 1 ≤ s/ν := (le_div_iff₀ hν).mpr (by simpa using hsν.le)
      linarith
    have hθS : θ ≤ (S/ν-1)/(D+1) := by
      apply div_le_div_of_nonneg_right _ hD1.le
      exact sub_le_sub_right ((div_le_div_iff_of_pos_right hν).mpr hsS) 1
    have hθeq : 1+(D+1)*θ=s/ν := by dsimp [θ]; field_simp; ring
    have htarget : μ+θ*(μ+κ)=y := by
      dsimp [μ,κ]
      have heq : ν*(1+(D+1)*θ)=s := by simpa only [mul_comm] using (eq_div_iff hν.ne').mp hθeq
      field_simp
      nlinarith only [congrArg (fun z : ℝ => y*z) heq]
    have hxEq : x-(1+θ)*b=D*θ*b := by
      have hνs : ν*(1+(D+1)*θ)=s := by simpa only [mul_comm] using (eq_div_iff hν.ne').mp hθeq
      dsimp [b]
      field_simp
      nlinarith only [congrArg (fun z : ℝ => x*z) hνs]
    have hrad : (x-(1+θ)*b)^2+θ^2*(D+κ^2)=θ^2*D*(1+D*ν^2) := by
      rw [hxEq]
      dsimp [κ]
      nlinarith only [congrArg (fun z : ℝ => θ^2*D^2*z) hbμ]
    have hroot : Real.sqrt ((x-(1+θ)*b)^2+θ^2*(D+κ^2))=θ*c*(1+D*ν^2)/a := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by dsimp [a]; positivity)).mpr
      rw [hrad]
      have haSq : a^2=1-ν^2 := ha2
      have hp : (θ*c*(1+D*ν^2)/a)^2=(θ*c*(1+D*ν^2))^2/a^2 := div_pow _ _ _
      rw [hp,haSq]
      apply (eq_div_iff hνsq.ne').mpr
      nlinarith only [congrArg (fun z : ℝ => θ^2*(1+D*ν^2)*z) hrel]
    refine ⟨a,b,μ,κ,θ,le_rfl,hb,hμ,hμν,hκ,hθ,hθS,?_,htarget,?_⟩
    · dsimp [a]
      rw [ha2]
      nlinarith [hbμ]
    · rw [hroot]
      dsimp [thresholdPsi]
      rw [if_neg hsmall]
      change (1+θ)*c*a-θ*c*(1+D*ν^2)/a=c*(1-ν*s)/a
      have hνs : ν*(1+(D+1)*θ)=s := by
        simpa only [mul_comm] using (eq_div_iff hν.ne').mp hθeq
      have haSq : a^2=1-ν^2 := ha2
      have hin : (1+θ)*a^2-θ*(1+D*ν^2)=1-ν*s := by
        nlinarith only [congrArg (fun z : ℝ => (1+θ)*z) haSq,congrArg (fun z : ℝ => ν*z) hνs]
      calc
        (1+θ)*c*a-θ*c*(1+D*ν^2)/a=c*((1+θ)*a^2-θ*(1+D*ν^2))/a := by
          field_simp
          <;> ring
        _ = c*(1-ν*s)/a := by rw [hin]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryOptimization -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def ordinaryNu (k D : ℝ) : ℝ :=
  Real.sqrt (((k-2)*D-k)/(2*(k-1)*D))

theorem ordinaryNu_properties (k D : ℝ) (hk : 2<k) (hD : (cA k)^2<D) :
    0<ordinaryNu k D ∧ ordinaryNu k D<1 ∧
      D*(1-(ordinaryNu k D)^2)=(cA k)^2*(1+D*(ordinaryNu k D)^2) := by
  have hkm : 0<k-2 := by linarith
  have hk1 : 0<k-1 := by linarith
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hDn : 0<(k-2)*D-k := by
    rw [cA_sq k hk] at hD
    have h := (div_lt_iff₀ hkm).mp hD
    nlinarith
  have hden : 0<2*(k-1)*D := by positivity
  have hp : 0<((k-2)*D-k)/(2*(k-1)*D) := div_pos hDn hden
  have hν : 0<ordinaryNu k D := Real.sqrt_pos.mpr hp
  have hνsq : (ordinaryNu k D)^2=((k-2)*D-k)/(2*(k-1)*D) := Real.sq_sqrt hp.le
  refine ⟨hν,?_,?_⟩
  · have hratio : ((k-2)*D-k)/(2*(k-1)*D)<1 := (div_lt_one hden).mpr (by nlinarith)
    nlinarith
  · rw [hνsq,cA_sq k hk]
    field_simp
    <;> ring

theorem ordinary_threshold_optimization (k D H L ρ : ℝ)
    (hk : 2<k) (hD : (cA k)^2<D) (hH : 1<H)
    (hL : 0<L) (hLH : L<Real.sqrt H) (hρ : ρ∈Set.Icc (-1) 1) :
    ∃a b μ κ θ : ℝ,
      Real.sqrt (1-(ordinaryNu k D)^2) ≤ a ∧ |b| ≤ ordinaryNu k D ∧
      0 ≤ μ ∧ μ ≤ ordinaryNu k D ∧ 0 ≤ κ ∧ 0 ≤ θ ∧
      θ ≤ (Real.sqrt H/ordinaryNu k D-1)/(D+1) ∧ a^2+b^2+μ^2=1 ∧
      μ+θ*(μ+κ)=Real.sqrt (H-L^2) ∧
      (1+θ)*cA k*a-Real.sqrt ((L*ρ-(1+θ)*b)^2+θ^2*(D+κ^2))=
        thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2))) := by
  have hν := ordinaryNu_properties k D hk hD
  have hH0 : 0<H := by linarith
  have hS : (Real.sqrt H)^2=H := Real.sq_sqrt hH0.le
  have hLsq : L^2<H := by nlinarith [Real.sqrt_nonneg H]
  have hy : 0<H-L^2 := by linarith
  have hySq : (Real.sqrt (H-L^2))^2=H-L^2 := Real.sq_sqrt hy.le
  have hρsq : ρ^2 ≤ 1 := by nlinarith [hρ.1,hρ.2]
  have hsarg : 0 ≤ H-L^2*(1-ρ^2) := by nlinarith [sq_nonneg (L*ρ)]
  have hsSq : (Real.sqrt (H-L^2*(1-ρ^2)))^2=H-L^2*(1-ρ^2) := Real.sq_sqrt hsarg
  apply threshold_optimization (cA k) (ordinaryNu k D) D (L*ρ) (Real.sqrt (H-L^2))
    (Real.sqrt (H-L^2*(1-ρ^2))) (Real.sqrt H) (cA_pos k hk) hν.1 hν.2.1
    (lt_of_le_of_lt (sq_nonneg _) hD).le hν.2.2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · rw [hsSq,hySq]
    ring
  · apply Real.sqrt_le_sqrt
    nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hρsq)]
  · have hOne : 1<Real.sqrt H := by nlinarith [Real.sqrt_nonneg H]
    exact hν.2.1.le.trans hOne.le

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxDriftGeometry -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem sqrt_increment_le (p q r : ℝ) (hp : 0<p) (hpq : p ≤ q) (hr : 0 ≤ r) :
    Real.sqrt (q+r)-Real.sqrt (p+r) ≤ Real.sqrt q-Real.sqrt p := by
  have hq : 0 ≤ q := hp.le.trans hpq
  have hp' : 0 ≤ p := hp.le
  have hpr : 0 ≤ p+r := by linarith
  have hqr : 0 ≤ q+r := by linarith
  have h₁ := Real.sq_sqrt hq
  have h₂ := Real.sq_sqrt hp'
  have h₃ := Real.sq_sqrt hpr
  have h₄ := Real.sq_sqrt hqr
  have hab : 0<Real.sqrt q+Real.sqrt p := by
    have := Real.sqrt_pos.mpr hp
    nlinarith [Real.sqrt_nonneg q]
  apply (mul_le_mul_iff_left₀ hab).mp
  calc
    (Real.sqrt (q+r)-Real.sqrt (p+r))*(Real.sqrt q+Real.sqrt p) ≤
        (Real.sqrt (q+r)-Real.sqrt (p+r))*(Real.sqrt (q+r)+Real.sqrt (p+r)) := by
      apply mul_le_mul_of_nonneg_left
        (add_le_add (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_le_sqrt (by linarith)))
        (sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith)))
    _ = (Real.sqrt q-Real.sqrt p)*(Real.sqrt q+Real.sqrt p) := by nlinarith only [h₁,h₂,h₃,h₄]

theorem weighted_circle_upper (A B U s H : ℝ) (hcircle : U^2+s^2=H) :
    A*U+B*s ≤ Real.sqrt (H*(A^2+B^2)) := by
  have hnon : 0 ≤ H := by nlinarith only [hcircle,sq_nonneg U,sq_nonneg s]
  have hsq := Real.sq_sqrt (mul_nonneg hnon (by positivity : 0 ≤ A^2+B^2))
  have hId : (A*U+B*s)^2+(A*s-B*U)^2=(A^2+B^2)*(U^2+s^2) := by ring
  rw [hcircle] at hId
  nlinarith only [hId,hsq,Real.sqrt_nonneg (H*(A^2+B^2)),sq_nonneg (A*s-B*U)]

def thresholdGap (ν H ell : ℝ) : ℝ :=
  (1+ell)/Real.sqrt (1-ν^2)-Real.sqrt
    (H*((1-ell)^2+((1+ell)*ν/Real.sqrt (1-ν^2))^2))

theorem linear_drift_lower (ν H ell U s : ℝ) (hν : 0<ν) (hν1 : ν<1)
    (hcircle : U^2+s^2=H) :
    thresholdGap ν H ell ≤ (1+ell)*(1-ν*s)/Real.sqrt (1-ν^2)-(1-ell)*U := by
  have h := weighted_circle_upper (1-ell) ((1+ell)*ν/Real.sqrt (1-ν^2)) U s H hcircle
  unfold thresholdGap
  have heq : (1+ell)*(1-ν*s)/Real.sqrt (1-ν^2)-(1-ell)*U=
      (1+ell)/Real.sqrt (1-ν^2)-((1-ell)*U+((1+ell)*ν/Real.sqrt (1-ν^2))*s) := by ring
  rw [heq]
  linarith only [h]

theorem thresholdPsi_drift_lower (c ν H ell U : ℝ)
    (hc : 0<c) (hν : 0<ν) (hν1 : ν<1) (hH : 1<H)
    (hell : ell∈Set.Icc (0:ℝ) 1) (hU : 0 ≤ U) (hUH : U ≤ Real.sqrt H) :
    thresholdGap ν H ell ≤
      ((1+ell)/c)*thresholdPsi c ν (Real.sqrt (H-U^2))-(1-ell)*U := by
  have hH0 : 0 ≤ H := by linarith
  have hU2 : U^2 ≤ H := by nlinarith [Real.sq_sqrt hH0,Real.sqrt_nonneg H]
  let s := Real.sqrt (H-U^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=H-U^2 := Real.sq_sqrt (by linarith)
  have hcircle : U^2+s^2=H := by linarith
  have hν2 : 0<1-ν^2 := by nlinarith
  have ha0 : 0<Real.sqrt (1-ν^2) := Real.sqrt_pos.mpr hν2
  have ha2 := Real.sq_sqrt hν2.le
  change thresholdGap ν H ell ≤ ((1+ell)/c)*thresholdPsi c ν s-(1-ell)*U
  unfold thresholdPsi
  by_cases hsν : s ≤ ν
  · rw [if_pos hsν]
    have hs1 : 0 ≤ 1-s^2 := by nlinarith
    have hHsν : 0 ≤ H-ν^2 := by linarith
    have hUeq : Real.sqrt (H-s^2)=U := by
      apply (Real.sqrt_eq_iff_eq_sq (by linarith) hU).mpr
      nlinarith only [hcircle]
    have hinc := sqrt_increment_le (1-ν^2) (1-s^2) (H-1) hν2 (by nlinarith) (by linarith)
    have heq₁ : 1-s^2+(H-1)=H-s^2 := by ring
    have heq₂ : 1-ν^2+(H-1)=H-ν^2 := by ring
    rw [heq₁,heq₂,hUeq] at hinc
    have hdiff : 0 ≤ Real.sqrt (1-s^2)-Real.sqrt (1-ν^2) :=
      sub_nonneg.mpr (Real.sqrt_le_sqrt (by nlinarith))
    have hf : (1+ell)*Real.sqrt (1-ν^2)-(1-ell)*Real.sqrt (H-ν^2) ≤
        (1+ell)*Real.sqrt (1-s^2)-(1-ell)*U := by
      have h₁ := mul_le_mul_of_nonneg_left hinc (show 0 ≤ 1-ell by linarith [hell.2])
      have h₂ := mul_nonneg (show 0 ≤ 2*ell by linarith [hell.1]) hdiff
      nlinarith only [h₁,h₂]
    have hboundary := linear_drift_lower ν H ell (Real.sqrt (H-ν^2)) ν hν hν1 (by
      rw [Real.sq_sqrt hHsν]
      ring)
    have hb : (1+ell)*(1-ν*ν)/Real.sqrt (1-ν^2)=(1+ell)*Real.sqrt (1-ν^2) := by
      apply (div_eq_iff ha0.ne').mpr
      nlinarith only [congrArg (fun z : ℝ => (1+ell)*z) ha2]
    rw [hb] at hboundary
    have hcancel : ((1+ell)/c)*(c*Real.sqrt (1-s^2))=(1+ell)*Real.sqrt (1-s^2) := by field_simp
    rw [hcancel]
    exact hboundary.trans hf
  · rw [if_neg hsν]
    have hcancel : ((1+ell)/c)*(c*(1-ν*s)/Real.sqrt (1-ν^2))=
      (1+ell)*(1-ν*s)/Real.sqrt (1-ν^2) := by field_simp
    rw [hcancel]
    exact linear_drift_lower ν H ell U s hν hν1 hcircle

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryNuBound -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinaryNu_sq_lt_half (k D : ℝ) (hk : 2<k) (hD : (cA k)^2<D) :
    (ordinaryNu k D)^2<1/2 := by
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hk1 : 0<k-1 := by linarith
  have hden : 0<2*(k-1)*D := by positivity
  have hp : 0<((k-2)*D-k)/(2*(k-1)*D) := by
    apply div_pos _ hden
    have h := hD
    rw [cA_sq k hk] at h
    have h' := (div_lt_iff₀ (show 0<k-2 by linarith)).mp h
    nlinarith
  rw [ordinaryNu,Real.sq_sqrt hp.le]
  apply (div_lt_iff₀ hden).mpr
  nlinarith

theorem ordinary_optimization_a_lower (k D a : ℝ) (hk : 2<k) (hD : (cA k)^2<D)
    (ha : Real.sqrt (1-(ordinaryNu k D)^2) ≤ a) : 7/10 ≤ a := by
  have hνsq := ordinaryNu_sq_lt_half k D hk hD
  have hnon : 0 ≤ 1-(ordinaryNu k D)^2 := by linarith
  have hs : (Real.sqrt (1-(ordinaryNu k D)^2))^2=1-(ordinaryNu k D)^2 := Real.sq_sqrt hnon
  have hn := Real.sqrt_nonneg (1-(ordinaryNu k D)^2)
  have h : 7/10 ≤ Real.sqrt (1-(ordinaryNu k D)^2) := by nlinarith
  exact h.trans ha

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryGap -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def ordinaryGap (k D H : ℝ) : ℝ :=
  Real.sqrt (2*k*D/((k-1)*(D+1)))-Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1)))

theorem ordinary_gap_identity (k D H : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 0 ≤ H) :
    thresholdGap (ordinaryNu k D) H (1/(k-1))=ordinaryGap k D H := by
  have hk1 : 0<k-1 := by linarith
  have hk2 : 0<k-2 := by linarith
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hD1 : 0<D+1 := by linarith
  have hν := ordinaryNu_properties k D hk hD
  have hν2 : 0<1-(ordinaryNu k D)^2 := by nlinarith [hν.1,hν.2.1]
  have hnp : 0 ≤ ((k-2)*D-k)/(2*(k-1)*D) := by
    have hd := hD
    rw [cA_sq k hk] at hd
    have h := (div_lt_iff₀ hk2).mp hd
    apply div_nonneg _ (by positivity)
    nlinarith
  have hνsq : (ordinaryNu k D)^2=((k-2)*D-k)/(2*(k-1)*D) := Real.sq_sqrt hnp
  let a := Real.sqrt (1-(ordinaryNu k D)^2)
  have ha : 0<a := Real.sqrt_pos.mpr hν2
  have haSq : a^2=k*(D+1)/(2*(k-1)*D) := by
    dsimp [a]
    rw [Real.sq_sqrt hν2.le,hνsq]
    field_simp
    <;> ring
  have hfirstSq : ((1+1/(k-1))/a)^2=2*k*D/((k-1)*(D+1)) := by
    have hp : ((1+1/(k-1))/a)^2=(1+1/(k-1))^2/a^2 := div_pow _ _ _
    rw [hp,haSq]
    field_simp
    <;> ring
  have hfirst : Real.sqrt (2*k*D/((k-1)*(D+1)))=(1+1/(k-1))/a := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    exact hfirstSq.symm
  have hsecond : (1-1/(k-1))^2+((1+1/(k-1))*(ordinaryNu k D)/a)^2=
      2*((k-2)*D-2)/((k-1)*(D+1)) := by
    have hp : ((1+1/(k-1))*(ordinaryNu k D)/a)^2=
        (1+1/(k-1))^2*(ordinaryNu k D)^2/a^2 := by rw [div_pow,mul_pow]
    rw [hp,hνsq,haSq]
    field_simp
    <;> ring
  unfold thresholdGap ordinaryGap
  change (1+1/(k-1))/a-Real.sqrt (H*((1-1/(k-1))^2+((1+1/(k-1))*(ordinaryNu k D)/a)^2))=_
  rw [hsecond,hfirst]
  congr 1
  congr 1
  ring

theorem ordinary_gap_rationalized (k D H : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 0 ≤ H) :
    ordinaryGap k D H=(2*(k*D-H*((k-2)*D-2))/((k-1)*(D+1)))/
      (Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1)))) := by
  have hk1 : 0<k-1 := by linarith
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hD1 : 0<D+1 := by linarith
  have hrad1 : 0<2*k*D/((k-1)*(D+1)) := by positivity
  have hinner : 0<(k-2)*D-2 := by
    have hd := hD
    rw [cA_sq k hk] at hd
    have h := (div_lt_iff₀ (show 0<k-2 by linarith)).mp hd
    nlinarith
  have hrad2 : 0 ≤ 2*H*((k-2)*D-2)/((k-1)*(D+1)) := by positivity
  have hsum : 0<Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1))) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr hrad1) (Real.sqrt_nonneg _)
  apply (eq_div_iff hsum.ne').mpr
  unfold ordinaryGap
  have h₁ := Real.sq_sqrt hrad1.le
  have h₂ := Real.sq_sqrt hrad2
  calc
    _ = 2*k*D/((k-1)*(D+1))-2*H*((k-2)*D-2)/((k-1)*(D+1)) := by nlinarith only [h₁,h₂]
    _ = _ := by ring

theorem ordinary_drift_gap (k D H U : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 1<H)
    (hU : 0 ≤ U) (hUH : U ≤ Real.sqrt H) :
    ordinaryGap k D H ≤
      ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-U^2))-(1-1/(k-1))*U := by
  rw [← ordinary_gap_identity k D H hk hD (by linarith)]
  have hν := ordinaryNu_properties k D hk hD
  apply thresholdPsi_drift_lower (cA k) (ordinaryNu k D) H (1/(k-1)) U
    (cA_pos k hk) hν.1 hν.2.1 hH _ hU hUH
  constructor
  · exact (div_pos zero_lt_one (show 0<k-1 by linarith)).le
  · apply (div_le_one (by linarith : 0<k-1)).mpr
    linarith

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverSliceThreshold -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_cover_slice_threshold {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k D H U w t z : ℝ) (hk : 2<k) (hH : 1<H)
    (hv : OrdinaryVectorColoring G v k) (r x y : Fin n) (hx : 0<‖uvec v r x‖) (hxy : G.Adj x y)
    (ht : 0<t) (hz : 0<z) (hzH : z<Real.sqrt H*t) (hw : 0 ≤ w)
    (hU : U*t ≤ ‖uvec v r x‖*z)
    (hDrift : ∀s : ℝ,0 ≤ s → s ≤ Real.sqrt H →
      (1-1/(k-1))*s+(((1+1/(k-1))/cA k)*((20*cA k+1)*
        (1+(Real.sqrt H/ordinaryNu k D-1)/(D+1)))+40)*w ≤
        ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-s^2)))
    (W : ℝ)
    (hW : (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-(z/t)^2*(1-(rho v r x)^2)))-
      (20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))*w)*t ≤
        W+(z/t)*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t) :
    (U+40*w)*t ≤ planeNeighborScore v k r x y z W := by
  let L := z/t
  let U' := ‖uvec v r x‖*L
  have hL : 0<L := div_pos hz ht
  have hLH : L<Real.sqrt H := (div_lt_iff₀ ht).mpr hzH
  have hUt : U'*t=‖uvec v r x‖*z := by dsimp [U',L]; field_simp
  have hUU : U ≤ U' := by nlinarith only [hU,hUt,ht]
  have hU' : 0 ≤ U' := mul_nonneg hx.le hL.le
  have hU'H : U' ≤ Real.sqrt H := by
    have hn := ordinary_root_residual_norm_le G v k hv r x
    have h : U' ≤ L := by dsimp [U']; nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hL.le]
    exact h.trans hLH.le
  have hsq : U'^2=L^2*(1-(rho v r x)^2) := by
    dsimp [U']
    rw [mul_pow,ordinary_root_residual_norm_sq G v k hv r x]
    ring
  have hψ : thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-U'^2))=
      thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-(rho v r x)^2))) := by rw [hsq]
  have hD := hDrift U' hU' hU'H
  rw [hψ] at hD
  have hell : 1/(k-1)∈Set.Icc (0:ℝ) 1 := by
    constructor
    · exact (div_pos zero_lt_one (show 0<k-1 by linarith)).le
    · exact (div_le_one (show 0<k-1 by linarith)).mpr (by linarith)
  have hη : 1/(k-1) ≤ -⟪v x,v y⟫ := by linarith [hv.2 x y hxy]
  have h := scalar_drift_transmission (cA k) (1/(k-1)) (-⟪v x,v y⟫) U U'
    (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-(rho v r x)^2))))
    ((20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))) w t
    (W+L*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t)
    (cA_pos k hk) hell hη hU' hUU hw ht.le hD hW
  apply h.trans_eq
  unfold planeNeighborScore
  dsimp [U',L]
  field_simp
  <;> ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxMills -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_eq_density_integral (a : ℝ) :
    PhiTail a=∫ x in Set.Ioi a,gaussianPDFReal 0 1 x := by
  rw [phiTail_eq_Ioi,measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal)≠0),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)

def millsConstant : ℝ := (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-2)

theorem millsConstant_pos : 0 < millsConstant := by
  unfold millsConstant
  positivity

theorem gaussian_density_lower_interval (u : ℝ) (hu : 1≤u) (x : ℝ)
    (hx : x∈Set.Ioc u (u+u⁻¹)) :
    millsConstant*Real.exp (-(u^2/2))≤gaussianPDFReal 0 1 x := by
  have hp : 0<u := lt_of_lt_of_le zero_lt_one hu
  have hinv : 0<u⁻¹ := inv_pos.mpr hp
  have hinvle : u⁻¹≤1 := (inv_le_one₀ hp).mpr hu
  have hiu : u*u⁻¹=1 := mul_inv_cancel₀ hp.ne'
  have hiu2 : u⁻¹^2≤1 := by nlinarith
  have hx0 : 0≤x := le_of_lt (lt_trans hp hx.1)
  have hxsq : x^2≤(u+u⁻¹)^2 := by nlinarith [hx.2]
  have he : -(u^2/2)-2 ≤ -(x^2/2) := by nlinarith [hiu,hxsq]
  dsimp [millsConstant,gaussianPDFReal]
  simp only [NNReal.coe_one,mul_one,sub_zero]
  rw [mul_assoc,← Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply Real.exp_le_exp.mpr
  linarith

theorem phiTail_mills_lower (u : ℝ) (hu : 1≤u) :
    u⁻¹*millsConstant*Real.exp (-(u^2/2))≤PhiTail u := by
  have hp : 0<u := lt_of_lt_of_le zero_lt_one hu
  have hub : u≤u+u⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr hp.le)
  have hfi : Integrable (gaussianPDFReal 0 1) := integrable_gaussianPDFReal 0 1
  rw [phiTail_eq_density_integral]
  calc
    u⁻¹*millsConstant*Real.exp (-(u^2/2))=
        ∫ x in Set.Ioc u (u+u⁻¹),millsConstant*Real.exp (-(u^2/2)) := by
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hub]
      simp only [add_sub_cancel_left,smul_eq_mul]
      ring
    _ ≤ ∫ x in Set.Ioc u (u+u⁻¹),gaussianPDFReal 0 1 x := by
      apply setIntegral_mono_on (integrableOn_const (hs:=by
        rw [Real.volume_Ioc]
        finiteness)) hfi.integrableOn measurableSet_Ioc
      intro x hx
      exact gaussian_density_lower_interval u hu x hx
    _ ≤ ∫ x in Set.Ioi u,gaussianPDFReal 0 1 x := by
      apply setIntegral_mono_set hfi.integrableOn
        (Eventually.of_forall (fun x => gaussianPDFReal_nonneg 0 1 x))
      exact Eventually.of_forall (fun x hx => hx.1)

theorem gaussian_tail_ratio_bound (t : ℝ) (ht : 2 ≤ t) :
    Real.exp (-(t^2/2))/PhiTail (t/Real.sqrt 2) ≤
      millsConstant⁻¹*t*Real.exp (-(t^2/4)) := by
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hslo : 1 ≤ Real.sqrt (2:ℝ) := by nlinarith
  have hshi : Real.sqrt (2:ℝ) ≤ 2 := by nlinarith
  have htp : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hu : 1 ≤ t/Real.sqrt 2 := (le_div_iff₀ hs).mpr (by nlinarith)
  have hup : 0 < t/Real.sqrt 2 := div_pos htp hs
  have hut : t/Real.sqrt 2 ≤ t := (div_le_iff₀ hs).mpr (by nlinarith)
  have hexp : (t/Real.sqrt 2)^2/2=t^2/4 := by rw [div_pow,hs2]; ring
  have hL := phiTail_mills_lower (t/Real.sqrt 2) hu
  rw [hexp] at hL
  have hb : millsConstant*Real.exp (-(t^2/4)) ≤ PhiTail (t/Real.sqrt 2)*t := by
    calc
      millsConstant*Real.exp (-(t^2/4))=
          ((t/Real.sqrt 2)⁻¹*millsConstant*Real.exp (-(t^2/4)))*(t/Real.sqrt 2) := by
        field_simp
      _ ≤ PhiTail (t/Real.sqrt 2)*(t/Real.sqrt 2) := mul_le_mul_of_nonneg_right hL hup.le
      _ ≤ PhiTail (t/Real.sqrt 2)*t := mul_le_mul_of_nonneg_left hut (phiTail_nonneg _)
  apply (div_le_iff₀ (phiTail_pos _)).mpr
  calc
    Real.exp (-(t^2/2))=Real.exp (-(t^2/4))*Real.exp (-(t^2/4)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = (millsConstant⁻¹*Real.exp (-(t^2/4)))*
        (millsConstant*Real.exp (-(t^2/4))) := by
      field_simp [millsConstant_pos.ne']
    _ ≤ (millsConstant⁻¹*Real.exp (-(t^2/4)))*(PhiTail (t/Real.sqrt 2)*t) :=
      mul_le_mul_of_nonneg_left hb
        (mul_nonneg (inv_nonneg.mpr millsConstant_pos.le) (Real.exp_pos _).le)
    _ = millsConstant⁻¹*t*Real.exp (-(t^2/4))*PhiTail (t/Real.sqrt 2) := by ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxTailShift -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_shift_integral (a r : ℝ) :
    PhiTail (a+r)=∫x in Set.Ioi a,gaussianPDFReal 0 1 (x+r) := by
  have hfun : (fun x : ℝ => (Set.Ioi (a+r)).indicator (gaussianPDFReal 0 1) (x+r))=
      (Set.Ioi a).indicator (fun x : ℝ => gaussianPDFReal 0 1 (x+r)) := by
    funext x
    simp only [Set.indicator_apply,Set.mem_Ioi,add_lt_add_iff_right]
  rw [phiTail_eq_density_integral,← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self _ r,hfun,integral_indicator measurableSet_Ioi]

theorem gaussian_density_shift_bound (a r x : ℝ) (hr : 0 ≤ r) (hx : a ≤ x) :
    Real.exp (((a+r)^2-a^2)/2)*gaussianPDFReal 0 1 (x+r) ≤ gaussianPDFReal 0 1 x := by
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero]
  calc
    Real.exp (((a+r)^2-a^2)/2)*((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-((x+r)^2)/2))=
        (Real.sqrt (2*Real.pi))⁻¹*Real.exp ((((a+r)^2-a^2)/2)-((x+r)^2)/2) := by
      rw [Real.exp_sub]
      rw [show -((x+r)^2)/2=-(((x+r)^2)/2) by ring,Real.exp_neg]
      ring
    _ ≤ (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(x^2)/2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hx)]

theorem phiTail_shift_bound (a r : ℝ) (hr : 0 ≤ r) :
    Real.exp (((a+r)^2-a^2)/2)*PhiTail (a+r) ≤ PhiTail a := by
  rw [phiTail_shift_integral,phiTail_eq_density_integral,← integral_const_mul]
  apply setIntegral_mono_on
    (((integrable_gaussianPDFReal 0 1).comp_add_right r).const_mul _).integrableOn
    (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Ioi
  intro x hx
  exact gaussian_density_shift_bound a r x hr hx.le

theorem phiTail_pythagorean_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.exp (b^2/2)*PhiTail (Real.sqrt (a^2+b^2)) ≤ PhiTail a := by
  have hs : (Real.sqrt (a^2+b^2))^2=a^2+b^2 := Real.sq_sqrt (by positivity)
  have hsa : a ≤ Real.sqrt (a^2+b^2) := by nlinarith [Real.sqrt_nonneg (a^2+b^2),sq_nonneg b]
  have h := phiTail_shift_bound a (Real.sqrt (a^2+b^2)-a) (sub_nonneg.mpr hsa)
  rw [add_sub_cancel] at h
  have he : ((Real.sqrt (a^2+b^2))^2-a^2)/2=b^2/2 := by rw [hs]; ring
  rw [he] at h
  exact h

theorem phiTail_union_threshold (D κ t : ℝ) (hD : 0 ≤ D) (hκ : 0 ≤ κ) (ht : 0 ≤ t) :
    Real.exp (D*t^2/2)*PhiTail (Real.sqrt (D+κ^2)*t) ≤ PhiTail (κ*t) := by
  have hroot : Real.sqrt ((κ*t)^2+(Real.sqrt D*t)^2)=Real.sqrt (D+κ^2)*t := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (mul_nonneg (Real.sqrt_nonneg _) ht)).mpr
    simp only [mul_pow,Real.sq_sqrt hD,Real.sq_sqrt (by positivity : 0 ≤ D+κ^2)]
    ring
  have h := phiTail_pythagorean_bound (κ*t) (Real.sqrt D*t)
    (mul_nonneg hκ ht) (mul_nonneg (Real.sqrt_nonneg _) ht)
  rw [hroot,mul_pow,Real.sq_sqrt hD] at h
  exact h

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverIntegral -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_exp_upper (u : ℝ) (hu : 0 ≤ u) : PhiTail u ≤ Real.exp (-(u^2/2)) := by
  have h := phiTail_shift_bound 0 u hu
  simp only [zero_add,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero] at h
  have h' : Real.exp (u^2/2)*PhiTail u ≤ 1 := h.trans (phiTail_le_one 0)
  have hr : PhiTail u ≤ 1/Real.exp (u^2/2) :=
    (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using h')
  simpa only [one_div,Real.exp_neg] using hr

theorem gaussian_cover_integral_bound (f : ℝ→ℝ) (hf : Measurable f)
    (hf0 : ∀x,0 ≤ f x) (hf1 : ∀x,f x ≤ 1) (A : ℝ) (hA : 0 ≤ A)
    (hneg : ∀x,x<0 → f x=0)
    (hgood : ∀x,0 ≤ x → x<A → f x ≤ PhiTail (Real.sqrt (A^2-x^2))) :
    (∫x,f x ∂gaussianReal 0 1) ≤
      (1+A/(Real.sqrt (2*Real.pi)))*Real.exp (-(A^2/2)) := by
  let C := (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-(A^2/2))
  let S := Set.Ico (0:ℝ) A
  let T := Set.Ici A
  let B : ℝ→ℝ := S.indicator (fun _ => C)+T.indicator (gaussianPDFReal 0 1)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hfi : Integrable (fun x => gaussianPDFReal 0 1 x*f x) := by
    apply (integrable_gaussianPDFReal 0 1).mono' (by fun_prop)
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (hf0 _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf1 x) (gaussianPDFReal_nonneg _ _ _)
  have hSi : Integrable (S.indicator (fun _ => C)) := by
    apply IntegrableOn.integrable_indicator
    · exact integrableOn_const (hs:=by dsimp [S]; rw [Real.volume_Ico]; finiteness)
    · exact measurableSet_Ico
  have hTi : Integrable (T.indicator (gaussianPDFReal 0 1)) :=
    (integrable_gaussianPDFReal 0 1).integrableOn.integrable_indicator measurableSet_Ici
  have hBi : Integrable B := hSi.add hTi
  have hpoint : ∀x,gaussianPDFReal 0 1 x*f x ≤ B x := by
    intro x
    by_cases hx0 : x<0
    · have hxS : x∉S := by intro h; exact not_le_of_gt hx0 h.1
      have hxT : x∉T := by intro h; exact not_le_of_gt hx0 (hA.trans h)
      simp only [B,Pi.add_apply,Set.indicator_of_notMem hxS,Set.indicator_of_notMem hxT,hneg x hx0,mul_zero,add_zero,le_rfl]
    · have hx0 : 0 ≤ x := le_of_not_gt hx0
      by_cases hxA : x<A
      · have hxS : x∈S := ⟨hx0,hxA⟩
        have hxT : x∉T := not_le_of_gt hxA
        simp only [B,Pi.add_apply,Set.indicator_of_mem hxS,Set.indicator_of_notMem hxT,add_zero]
        have hsub : 0 ≤ A^2-x^2 := by nlinarith
        have hs := Real.sq_sqrt hsub
        have hExp := (hgood x hx0 hxA).trans (phiTail_exp_upper _ (Real.sqrt_nonneg _))
        apply (mul_le_mul_of_nonneg_left hExp (gaussianPDFReal_nonneg _ _ _)).trans_eq
        unfold gaussianPDFReal
        simp only [NNReal.coe_one,mul_one,sub_zero,hs]
        dsimp [C]
        rw [mul_assoc,← Real.exp_add]
        congr 1
        congr 1
        ring
      · have hxA : A ≤ x := le_of_not_gt hxA
        have hxS : x∉S := by intro h; exact not_lt_of_ge hxA h.2
        have hxT : x∈T := hxA
        simp only [B,Pi.add_apply,Set.indicator_of_notMem hxS,Set.indicator_of_mem hxT,zero_add]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf1 x) (gaussianPDFReal_nonneg _ _ _)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal)≠0)]
  simp only [smul_eq_mul]
  calc
    (∫x,gaussianPDFReal 0 1 x*f x) ≤ ∫x,B x := integral_mono hfi hBi hpoint
    _ = A*C+PhiTail A := by
      change (∫x,S.indicator (fun _ => C) x+T.indicator (gaussianPDFReal 0 1) x)=A*C+PhiTail A
      rw [integral_add hSi hTi]
      rw [integral_indicator measurableSet_Ico,integral_indicator measurableSet_Ici]
      rw [setIntegral_const,Real.volume_real_Ico_of_le hA,sub_zero,smul_eq_mul]
      rw [integral_Ici_eq_integral_Ioi,← phiTail_eq_density_integral]
    _ ≤ (1+A/(Real.sqrt (2*Real.pi)))*Real.exp (-(A^2/2)) := by
      have h := phiTail_exp_upper A hA
      dsimp [C]
      simp only [div_eq_mul_inv] at h ⊢
      nlinarith only [h]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverFubini -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_product_bad_event_bound {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (E : Set (ℝ×Ω)) (hE : MeasurableSet E)
    (A : ℝ) (hA : 0 ≤ A) (hpos : ∀p∈E,0 ≤ p.1)
    (hgood : ∀z,0 ≤ z → z<A → ν.real {ω : Ω | (z,ω)∈E} ≤ PhiTail (Real.sqrt (A^2-z^2))) :
    ((gaussianReal 0 1).prod ν).real E ≤ (1+A/Real.sqrt (2*Real.pi))*Real.exp (-(A^2/2)) := by
  let f : ℝ→ℝ := fun z => ν.real (Prod.mk z ⁻¹' E)
  have hf : Measurable f := ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left hE)
  have hf0 : ∀z,0 ≤ f z := fun _ => measureReal_nonneg
  have hf1 : ∀z,f z ≤ 1 := fun _ => measureReal_le_one
  have hneg : ∀z,z<0 → f z=0 := by
    intro z hz
    have he : Prod.mk z ⁻¹' E=∅ := by
      ext ω
      constructor
      · intro h
        exact (not_le_of_gt hz (hpos (z,ω) h)).elim
      · intro h
        exact h.elim
    dsimp [f]
    rw [he,measureReal_empty]
  have hInt : ((gaussianReal 0 1).prod ν).real E=∫z,f z ∂gaussianReal 0 1 := by
    let F : ℝ×Ω→ℝ := E.indicator 1
    have hFi : Integrable F ((gaussianReal 0 1).prod ν) := (integrable_const (1:ℝ)).indicator hE
    calc
      ((gaussianReal 0 1).prod ν).real E=∫p,F p ∂(gaussianReal 0 1).prod ν :=
        (integral_indicator_one hE).symm
      _ = ∫z,∫ω,F (z,ω) ∂ν ∂gaussianReal 0 1 := integral_prod F hFi
      _ = ∫z,f z ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [] with z
        have hfun : (fun ω => F (z,ω))=(Prod.mk z ⁻¹' E).indicator 1 := by
          funext ω
          rfl
        rw [hfun]
        exact integral_indicator_one (measurable_prodMk_left hE)
  rw [hInt]
  exact gaussian_cover_integral_bound f hf hf0 hf1 A hA hneg hgood

theorem independent_gaussian_bad_event_bound {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω→ℝ) (W : Ω→Y)
    (hX : Measurable X) (hW : Measurable W) (hI : IndepFun X W μ)
    (hN : μ.map X=gaussianReal 0 1) (E : Set (ℝ×Y)) (hE : MeasurableSet E)
    (A : ℝ) (hA : 0 ≤ A) (hpos : ∀p∈E,0 ≤ p.1)
    (hgood : ∀z,0 ≤ z → z<A → (μ.map W).real {w : Y | (z,w)∈E} ≤ PhiTail (Real.sqrt (A^2-z^2))) :
    μ.real {ω : Ω | (X ω,W ω)∈E} ≤ (1+A/Real.sqrt (2*Real.pi))*Real.exp (-(A^2/2)) := by
  letI : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  have hMap : μ.map (fun ω => (X ω,W ω))=(gaussianReal 0 1).prod (μ.map W) := by
    rw [hI.map_prod_eq_prod_map_map hX.aemeasurable hW.aemeasurable,hN]
  have hM : μ.real {ω : Ω | (X ω,W ω)∈E}=((gaussianReal 0 1).prod (μ.map W)).real E := by
    rw [← hMap,map_measureReal_apply (hX.prodMk hW) hE]
    rfl
  rw [hM]
  exact gaussian_product_bad_event_bound (μ.map W) E hE A hA hpos hgood

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussianInterval -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_real_Icc_density_integral (a b : ℝ) :
    (gaussianReal 0 1).real (Set.Icc a b)=∫ x in Set.Icc a b,gaussianPDFReal 0 1 x := by
  rw [measureReal_def,gaussianReal_apply_eq_integral 0 (by norm_num : (1:NNReal)≠0),ENNReal.toReal_ofReal]
  exact integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)

theorem gaussian_interval_density_lower (a t : ℝ) (ht : 0<t) :
    (1/t)*gaussianPDFReal 0 1 (|a| *t+1/t) ≤
      (gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t)) := by
  have ht' : 0<1/t := one_div_pos.mpr ht
  have hden : 0 ≤ |a| *t+1/t := by positivity
  have hpoint : ∀x∈Set.Icc (a*t) (a*t+1/t),
      gaussianPDFReal 0 1 (|a| *t+1/t) ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    have ha₁ := mul_le_mul_of_nonneg_right (neg_abs_le a) ht.le
    have ha₂ := mul_le_mul_of_nonneg_right (le_abs_self a) ht.le
    have hax : |x| ≤ |a| *t+1/t := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hs : x^2 ≤ (|a| *t+1/t)^2 := by nlinarith [sq_abs x,abs_nonneg x]
    unfold gaussianPDFReal
    simp only [NNReal.coe_one,mul_one,sub_zero]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    apply Real.exp_le_exp.mpr
    linarith
  rw [gaussian_real_Icc_density_integral]
  calc
    (1/t)*gaussianPDFReal 0 1 (|a| *t+1/t)=
        ∫ x in Set.Icc (a*t) (a*t+1/t),gaussianPDFReal 0 1 (|a| *t+1/t) := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith)]
      simp only [add_sub_cancel_left,smul_eq_mul]
    _ ≤ ∫ x in Set.Icc (a*t) (a*t+1/t),gaussianPDFReal 0 1 x := by
      apply setIntegral_mono_on (integrableOn_const (hs:=by
        rw [Real.volume_Icc]
        finiteness)) (integrable_gaussianPDFReal 0 1).integrableOn measurableSet_Icc
      exact hpoint

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryBoxBound -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def gaussianBoxBound (a b t : ℝ) : ℝ :=
  2*Real.pi*t^2*Real.exp (-(1-a^2-b^2)*t^2/2+a+|b|+t⁻¹^2)

theorem gaussian_box_bound_density_identity (a b t : ℝ) (ha : 0 ≤ a) (ht : 0<t) :
    gaussianBoxBound a b t*
      ((1/t)*gaussianPDFReal 0 1 (|a| * t+1/t))*
      ((1/t)*gaussianPDFReal 0 1 (|b| * t+1/t))=Real.exp (-(t^2/2)) := by
  have ht0 := ht.ne'
  have hs : 0<Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : (Real.sqrt (2*Real.pi))^2=2*Real.pi := Real.sq_sqrt (by positivity)
  have hC : (2*Real.pi*t^2)*((1/t)*(Real.sqrt (2*Real.pi))⁻¹)*
      ((1/t)*(Real.sqrt (2*Real.pi))⁻¹)=1 := by
    field_simp
    nlinarith [sq_nonneg t]
  have hE : (-(1-a^2-b^2)*t^2/2+a+|b|+t⁻¹^2)-
      ((a*t+1/t)^2/2)-((|b| * t+1/t)^2/2)=-(t^2/2) := by
    rw [show b^2=|b|^2 by exact (sq_abs b).symm]
    field_simp
    <;> ring
  unfold gaussianBoxBound gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero,abs_of_nonneg ha,neg_div]
  calc
    2*Real.pi*t^2*Real.exp (-(1-a^2-b^2)*t^2/2+a+|b|+t⁻¹^2)*
        ((1/t)*((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-((a*t+1/t)^2/2))))*
        ((1/t)*((Real.sqrt (2*Real.pi))⁻¹*Real.exp (-((|b| * t+1/t)^2/2))))=
      ((2*Real.pi*t^2)*((1/t)*(Real.sqrt (2*Real.pi))⁻¹)*((1/t)*(Real.sqrt (2*Real.pi))⁻¹))*
        Real.exp ((-(1-a^2-b^2)*t^2/2+a+|b|+t⁻¹^2)-((a*t+1/t)^2/2)-((|b| * t+1/t)^2/2)) := by
      rw [Real.exp_sub,Real.exp_sub]
      rw [Real.exp_neg,Real.exp_neg]
      ring
    _ = Real.exp (-(t^2/2)) := by rw [hC,hE,one_mul]

theorem ordinary_box_exponential_bound {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (x : Fin n) (hx : x∈F) (e : Space d) (he : ‖e‖=1)
    (hxe : ⟪v x,e⟫=0) (a b t : ℝ) (ha : 0 ≤ a) (ht : 0<t)
    (hp : pLocal G v F x ≤ Real.exp (-(t^2/2))) :
    gaussProb (ordinaryBoxEvent G k v F x e a b t) ≤ gaussianBoxBound a b t := by
  let L₁ := (1/t)*gaussianPDFReal 0 1 (|a| * t+1/t)
  let L₂ := (1/t)*gaussianPDFReal 0 1 (|b| * t+1/t)
  let P₁ := (gaussianReal 0 1).real (Set.Icc (a*t) (a*t+1/t))
  let P₂ := (gaussianReal 0 1).real (Set.Icc (b*t) (b*t+1/t))
  have hL₁ : 0<L₁ := mul_pos (one_div_pos.mpr ht) (gaussianPDFReal_pos 0 1 _ (by norm_num))
  have hL₂ : 0<L₂ := mul_pos (one_div_pos.mpr ht) (gaussianPDFReal_pos 0 1 _ (by norm_num))
  have hLP₁ : L₁ ≤ P₁ := gaussian_interval_density_lower a t ht
  have hLP₂ : L₂ ≤ P₂ := gaussian_interval_density_lower b t ht
  have hP₁ : 0<P₁ := lt_of_lt_of_le hL₁ hLP₁
  have hP₂ : 0<P₂ := lt_of_lt_of_le hL₂ hLP₂
  have hK := ordinary_box_probability_bound G v k hk hv F x hx e he hxe a b t ht
  have hKB : gaussProb (ordinaryBoxEvent G k v F x e a b t) ≤ Real.exp (-(t^2/2))/(L₁*L₂) := by
    apply hK.trans
    exact div_le_div₀ (le_trans (measureReal_nonneg) hp) hp (mul_pos hL₁ hL₂)
      (mul_le_mul hLP₁ hLP₂ hL₂.le hP₁.le)
  apply hKB.trans_eq
  apply (div_eq_iff (mul_pos hL₁ hL₂).ne').mpr
  have hI := gaussian_box_bound_density_identity a b t ha ht
  simpa only [L₁,L₂,mul_assoc] using hI.symm

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxUniformTail -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def uniformMillsConstant : ℝ := min millsConstant (PhiTail 1)

theorem uniformMillsConstant_pos : 0<uniformMillsConstant :=
  lt_min millsConstant_pos (phiTail_pos 1)

theorem phiTail_uniform_lower (μ t : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (ht : 1 ≤ t) :
    ((1/t)*uniformMillsConstant)*Real.exp (-((μ*t)^2/2)) ≤ PhiTail (μ*t) := by
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have hu : μ*t ≤ t := by nlinarith
  have hc0 := uniformMillsConstant_pos.le
  have hcM : uniformMillsConstant ≤ millsConstant := min_le_left _ _
  have hcP : uniformMillsConstant ≤ PhiTail 1 := min_le_right _ _
  by_cases hbig : 1 ≤ μ*t
  · have hu0 : 0<μ*t := lt_of_lt_of_le zero_lt_one hbig
    have hi : 1/t ≤ (μ*t)⁻¹ := by
      simpa only [one_div] using (inv_le_inv₀ ht0 hu0).mpr hu
    apply le_trans _ (phiTail_mills_lower (μ*t) hbig)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact mul_le_mul hi hcM hc0 (inv_nonneg.mpr hu0.le)
  · have hE : Real.exp (-((μ*t)^2/2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (μ*t)])
    calc
      ((1/t)*uniformMillsConstant)*Real.exp (-((μ*t)^2/2)) ≤ (1/t)*uniformMillsConstant := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ (1/t)*uniformMillsConstant)
      _ ≤ uniformMillsConstant := by
        have hi : 1/t ≤ 1 := (div_le_one ht0).mpr ht
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hi hc0
      _ ≤ PhiTail 1 := hcP
      _ ≤ PhiTail (μ*t) := phiTail_antitone (le_of_lt (lt_of_not_ge hbig))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxBoxTail -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_box_polynomial_bound (a₀ b μ w t : ℝ)
    (ha₀ : 7/10 ≤ a₀) (ha₁ : a₀ ≤ 1) (hb : |b| ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1/100) (ht : 1 ≤ t)
    (hwt : w*t^2=Real.log t) (hnorm : a₀^2+b^2+μ^2=1) :
    gaussianBoxBound (a₀-20*w) b t ≤
      (2*Real.pi*Real.exp 3/t^10)*Real.exp (-((μ*t)^2/2)) := by
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  have ha : a₀-20*w ≤ 1 := by linarith
  have hinv : t⁻¹^2 ≤ 1 := by
    have hi : 0<t⁻¹ := inv_pos.mpr ht0
    have hi1 : t⁻¹ ≤ 1 := (inv_le_one₀ ht0).mpr ht
    nlinarith
  have hdiff : 24*w ≤ 1-(a₀-20*w)^2-b^2-μ^2 := by
    have hp := mul_nonneg hw (show 0 ≤ 40*a₀-400*w-24 by linarith)
    nlinarith only [hp,hnorm]
  have hE : -(1-(a₀-20*w)^2-b^2)*t^2/2+(a₀-20*w)+|b|+t⁻¹^2 ≤
      -((μ*t)^2/2)-12*Real.log t+3 := by
    have hm := mul_le_mul_of_nonneg_right hdiff (sq_nonneg t)
    nlinarith only [hm,hwt,ha,hb,hinv]
  have hpower : Real.exp (-(12*Real.log t))=(t^12)⁻¹ := by
    rw [Real.exp_neg]
    rw [show 12*Real.log t=(12:ℕ)*Real.log t by norm_num,Real.exp_nat_mul,Real.exp_log ht0]
  unfold gaussianBoxBound
  calc
    2*Real.pi*t^2*Real.exp (-(1-(a₀-20*w)^2-b^2)*t^2/2+(a₀-20*w)+|b|+t⁻¹^2) ≤
        2*Real.pi*t^2*Real.exp (-((μ*t)^2/2)-12*Real.log t+3) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (by positivity)
    _ = (2*Real.pi*Real.exp 3/t^10)*Real.exp (-((μ*t)^2/2)) := by
      rw [Real.exp_add,sub_eq_add_neg,Real.exp_add,hpower]
      field_simp
      <;> ring

theorem gaussian_box_tail_bound (a₀ b μ w t : ℝ)
    (ha₀ : 7/10 ≤ a₀) (ha₁ : a₀ ≤ 1) (hb : |b| ≤ 1)
    (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) (hw : 0 ≤ w) (hw1 : w ≤ 1/100) (ht : 1 ≤ t)
    (hwt : w*t^2=Real.log t) (hnorm : a₀^2+b^2+μ^2=1)
    (hlarge : 2*Real.pi*Real.exp 3 ≤ uniformMillsConstant*t^9) :
    gaussianBoxBound (a₀-20*w) b t ≤ PhiTail (μ*t) := by
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht
  apply (gaussian_box_polynomial_bound a₀ b μ w t ha₀ ha₁ hb hw hw1 ht hwt hnorm).trans
  apply le_trans _ (phiTail_uniform_lower μ t hμ hμ1 ht)
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_div_iff₀ (pow_pos ht0 10) ht0).mpr
  convert mul_le_mul_of_nonneg_right hlarge ht0.le using 1 <;> ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxBoxTailAsymptotic -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def roundingSlack (t : ℝ) : ℝ := Real.log t/t^2

theorem roundingSlack_tendsto : Tendsto roundingSlack atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.log t/t^2) atTop (𝓝 0)
  simpa only [Real.rpow_two] using
    (isLittleO_log_rpow_atTop (by norm_num : 0<(2:ℝ))).tendsto_div_nhds_zero

theorem gaussian_box_tail_eventually :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀t : ℝ,t₀ ≤ t → ∀a₀ b μ : ℝ,
      7/10 ≤ a₀ → a₀ ≤ 1 → |b| ≤ 1 → 0 ≤ μ → μ ≤ 1 → a₀^2+b^2+μ^2=1 →
      gaussianBoxBound (a₀-20*roundingSlack t) b t ≤ PhiTail (μ*t) := by
  have hw : ∀ᶠ t : ℝ in atTop,roundingSlack t ≤ 1/100 := by
    exact (roundingSlack_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/100)).mono fun t ht => ht.le
  have hp : Tendsto (fun t : ℝ => t^9) atTop atTop := tendsto_pow_atTop (by decide)
  have hlarge : ∀ᶠ t : ℝ in atTop,2*Real.pi*Real.exp 3 ≤ uniformMillsConstant*t^9 := by
    filter_upwards [hp.eventually_ge_atTop ((2*Real.pi*Real.exp 3)/uniformMillsConstant)] with t ht
    simpa only [mul_comm] using (div_le_iff₀ uniformMillsConstant_pos).mp ht
  have hAll : ∀ᶠ t : ℝ in atTop,1 ≤ t ∧ roundingSlack t ≤ 1/100 ∧
      2*Real.pi*Real.exp 3 ≤ uniformMillsConstant*t^9 := by
    filter_upwards [eventually_ge_atTop (1:ℝ),hw,hlarge] with t ht hw hl
    exact ⟨ht,hw,hl⟩
  obtain ⟨t₁,ht₁⟩ := (eventually_atTop.mp hAll)
  refine ⟨max t₁ 1,le_max_right _ _,?_⟩
  intro t ht a₀ b μ ha₀ ha₁ hb hμ hμ1 hnorm
  obtain ⟨ht1,hw,hl⟩ := ht₁ t (le_trans (le_max_left _ _) ht)
  apply gaussian_box_tail_bound a₀ b μ (roundingSlack t) t ha₀ ha₁ hb hμ hμ1 _ hw ht1 _ hnorm hl
  · exact div_nonneg (Real.log_nonneg ht1) (sq_nonneg t)
  · dsimp [roundingSlack]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one ht1)))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGaussianPolytopeLarge -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_inner_scaled_tail_bound {d : ℕ} (w : Space d) (σ a : ℝ)
    (hw : ‖w‖ ≤ σ) (ha : 0 ≤ a) :
    gaussProb {g : Space d | a*σ<⟪g,w⟫} ≤ PhiTail a := by
  have hσ : 0 ≤ σ := (norm_nonneg _).trans hw
  by_cases hw0 : w=0
  · have he : {g : Space d | a*σ<⟪g,w⟫}=∅ := by
      ext g
      simp only [hw0,inner_zero_right,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_lt]
      exact mul_nonneg ha hσ
    rw [he]
    simpa only [gaussProb,measureReal_empty] using phiTail_nonneg a
  · have hn : 0<‖w‖ := norm_pos_iff.mpr hw0
    let e := ‖w‖⁻¹ • w
    have he : ‖e‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hM : (stdGaussian (Space d)).map (fun g : Space d => ⟪g,e⟫)=gaussianReal 0 1 := by
      simpa only [real_inner_comm] using gaussian_inner_map e he
    have hP : gaussProb {g : Space d | a<⟪g,e⟫}=PhiTail a := by
      rw [phiTail_eq_Ioi,gaussProb]
      rw [← hM,map_measureReal_apply (by fun_prop) measurableSet_Ioi]
      rfl
    rw [← hP]
    unfold gaussProb
    apply measureReal_mono _ (measure_ne_top _ _)
    intro g hg
    change a<⟪g,e⟫
    change a*σ<⟪g,w⟫ at hg
    change a<⟪g,‖w‖⁻¹ • w⟫
    rw [real_inner_smul_right]
    have h := (mul_le_mul_of_nonneg_left hw ha).trans_lt hg
    simpa only [mul_comm] using (lt_mul_inv_iff₀ hn).mpr h

theorem gaussian_finite_polytope_large {d : ℕ} {Y : Type*} [Fintype Y]
    (w : Y→Space d) (ξ : Y→ℝ) (hξ : ∀y,(ξ y)^2 ≤ 1)
    (hw : ∀y,‖w y‖ ≤ Real.sqrt (1-(ξ y)^2))
    (D κ t : ℝ) (hD : 0 ≤ D) (hκ : 0 ≤ κ) (ht : 0 ≤ t)
    (hcard : (Fintype.card Y:ℝ) ≤ Real.exp (D*t^2/2)) :
    1-PhiTail (κ*t) ≤ gaussProb {g : Space d |
      ∀y,⟪g,w y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t} := by
  classical
  have hM : MeasurableSet {g : Space d |
      ∀y,⟪g,w y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro y
    exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) measurable_const)
  have hP : gaussProb {g : Space d | ∃y,
      Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t<⟪g,w y⟫} ≤ PhiTail (κ*t) := by
    have hset : {g : Space d | ∃y,Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t<⟪g,w y⟫}=
      ⋃y,{g : Space d | Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t<⟪g,w y⟫} := by ext; simp
    unfold gaussProb
    rw [hset]
    calc
      _ ≤ ∑y,(stdGaussian (Space d)).real {g : Space d |
          Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t<⟪g,w y⟫} := measureReal_iUnion_fintype_le _
      _ ≤ ∑_y : Y,PhiTail (Real.sqrt (D+κ^2)*t) := by
        apply Finset.sum_le_sum
        intro y hy
        have hb := gaussian_inner_scaled_tail_bound (w y) (Real.sqrt (1-(ξ y)^2))
          (Real.sqrt (D+κ^2)*t) (hw y) (mul_nonneg (Real.sqrt_nonneg _) ht)
        simpa only [mul_assoc,mul_comm,mul_left_comm,gaussProb] using hb
      _ = (Fintype.card Y:ℝ)*PhiTail (Real.sqrt (D+κ^2)*t) := by simp
      _ ≤ Real.exp (D*t^2/2)*PhiTail (Real.sqrt (D+κ^2)*t) :=
        mul_le_mul_of_nonneg_right hcard (phiTail_nonneg _)
      _ ≤ PhiTail (κ*t) := phiTail_union_threshold D κ t hD hκ ht
  have hset : {g : Space d | ∃y,Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t<⟪g,w y⟫}=
    {g : Space d | ∀y,⟪g,w y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t}ᶜ := by
    ext; simp
  unfold gaussProb at hP ⊢
  rw [hset,probReal_compl_eq_one_sub hM] at hP
  linarith

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxEhrhardTransmission -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem polyhedral_extrapolation_exceedance {d : ℕ} {Y : Type*} [Fintype Y]
    (z : Y→Space d) (A B : Y→ℝ) (μ κ θ : ℝ) (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ)
    (h₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤ A y} ≤ PhiTail μ)
    (h₁ : 1-PhiTail κ ≤ gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤ B y}) :
    1-PhiTail (μ+θ*(μ+κ)) ≤
      gaussProb {g : Space d | ∃y,(1+θ)*A y-θ*B y<⟪g,z y⟫} := by
  have h := lemma_29 z A B μ κ θ hμ hκ hθ h₀ h₁
  have hM : MeasurableSet {g : Space d | ∀y,⟪g,z y⟫ ≤ (1+θ)*A y-θ*B y} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro y
    exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) measurable_const)
  have hset : {g : Space d | ∃y,(1+θ)*A y-θ*B y<⟪g,z y⟫}=
      {g : Space d | ∀y,⟪g,z y⟫ ≤ (1+θ)*A y-θ*B y}ᶜ := by
    ext g
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,not_forall,not_le]
  rw [hset,gaussProb,probReal_compl_eq_one_sub hM]
  exact sub_le_sub_left h 1

theorem circle_linear_lower (A B ξ : ℝ) (hξ : ξ^2 ≤ 1) :
    -Real.sqrt (A^2+B^2) ≤ A*ξ-B*Real.sqrt (1-ξ^2) := by
  have hq : (Real.sqrt (1-ξ^2))^2=1-ξ^2 := Real.sq_sqrt (by linarith)
  have hs : (Real.sqrt (A^2+B^2))^2=A^2+B^2 := Real.sq_sqrt (by positivity)
  have hn := Real.sqrt_nonneg (A^2+B^2)
  have hId : (A*ξ-B*Real.sqrt (1-ξ^2))^2+(A*Real.sqrt (1-ξ^2)+B*ξ)^2=
      (A^2+B^2)*(ξ^2+(Real.sqrt (1-ξ^2))^2) := by ring
  rw [hq] at hId
  nlinarith [sq_nonneg (A*Real.sqrt (1-ξ^2)+B*ξ)]

theorem ehrhard_transmission_bound {d : ℕ} {Y : Type*} [Fintype Y]
    (z : Y→Space d) (ξ : Y→ℝ) (hξ : ∀y,(ξ y)^2 ≤ 1)
    (c a b L ρ D μ κ θ t : ℝ) (hD : 0 ≤ D+κ^2)
    (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (h₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤ (c*a-b*ξ y)*t-1/t} ≤ PhiTail (μ*t))
    (h₁ : 1-PhiTail (κ*t) ≤ gaussProb {g : Space d |
      ∀y,⟪g,z y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t}) :
    1-PhiTail ((μ+θ*(μ+κ))*t) ≤ gaussProb {g : Space d | ∃y,
      ((1+θ)*c*a-Real.sqrt ((L*ρ-(1+θ)*b)^2+θ^2*(D+κ^2)))*t-(1+θ)/t <
        ⟪g,z y⟫+L*ρ*ξ y*t} := by
  have h := polyhedral_extrapolation_exceedance z
    (fun y => (c*a-b*ξ y)*t-1/t)
    (fun y => Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t)
    (μ*t) (κ*t) θ (mul_nonneg hμ ht) (mul_nonneg hκ ht) hθ h₀ h₁
  have harg : μ*t+θ*(μ*t+κ*t)=(μ+θ*(μ+κ))*t := by ring
  rw [harg] at h
  apply h.trans
  unfold gaussProb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨y,hy⟩ := hg
  refine ⟨y,?_⟩
  have hC := circle_linear_lower (L*ρ-(1+θ)*b) (θ*Real.sqrt (D+κ^2)) (ξ y) (hξ y)
  have hsq : (θ*Real.sqrt (D+κ^2))^2=θ^2*(D+κ^2) := by
    rw [mul_pow,Real.sq_sqrt hD]
  rw [hsq] at hC
  have hCt := mul_le_mul_of_nonneg_right hC ht
  have hid : (1+θ)*((c*a-b*ξ y)*t-1/t)-θ*(Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t)+L*ρ*ξ y*t=
      ((1+θ)*c*a+((L*ρ-(1+θ)*b)*ξ y-(θ*Real.sqrt (D+κ^2))*Real.sqrt (1-(ξ y)^2)))*t-(1+θ)/t := by ring
  nlinarith

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryEhrhard -/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem extrapolated_threshold_lower (c ψ θ Θ w t : ℝ)
    (hc : 0 ≤ c) (hθ : 0 ≤ θ) (hθΘ : θ ≤ Θ) (hw : 0 ≤ w) (ht : 0<t) (hwt : 1 ≤ w*t^2) :
    (ψ-(20*c+1)*(1+Θ)*w)*t ≤ (ψ-20*(1+θ)*c*w)*t-(1+θ)/t := by
  have hΘ : 0 ≤ Θ := hθ.trans hθΘ
  have h₁ : 20*(1+θ)*c*w*t ≤ 20*(1+Θ)*c*w*t := by
    nlinarith only [mul_nonneg (show 0 ≤ Θ-θ by linarith) (show 0 ≤ 20*c*w*t by positivity)]
  have h₂ : (1+θ)/t ≤ (1+Θ)*w*t := by
    apply (div_le_iff₀ ht).mpr
    have h := mul_le_mul_of_nonneg_left hwt (show 0 ≤ 1+Θ by linarith)
    nlinarith only [h,hθΘ]
  nlinarith only [h₁,h₂]

theorem ordinary_ehrhard_transmission_eventually (k D H : ℝ)
    (hk : 2<k) (hD : (cA k)^2<D) (hH : 1<H) :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀t : ℝ,t₀ ≤ t → ∀L ρ : ℝ,0<L → L<Real.sqrt H → ρ∈Set.Icc (-1) 1 →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,OrdinaryVectorColoring G v k →
      ∀F : Finset (Fin n),∀r x : Fin n,x∈F → 0<‖uvec v r x‖ →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) →
      ((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2) →
      1-PhiTail (Real.sqrt (H-L^2)*t) ≤ gaussProb {g : Space d | ∃y∈nbr G F x,
        (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))-
          (20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))*roundingSlack t)*t ≤
          ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
            L*ρ*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t} := by
  classical
  obtain ⟨t₁,ht₁,hTail⟩ := gaussian_box_tail_eventually
  have hslack : ∀ᶠ t : ℝ in atTop,roundingSlack t ≤ 1/100 :=
    (roundingSlack_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/100)).mono fun _ ht => ht.le
  obtain ⟨t₂,ht₂⟩ := eventually_atTop.mp hslack
  refine ⟨max (max t₁ t₂) (Real.exp 1),?_,?_⟩
  · exact ht₁.trans ((le_max_left t₁ t₂).trans (le_max_left _ _))
  intro t ht L ρ hL hLH hρ n d G v hv F r x hxF hx hp hcard
  have htt₁ : t₁ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have htt₂ : t₂ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht1 : 1 ≤ t := ht₁.trans htt₁
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht1
  have htlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ((le_max_right _ _).trans ht)
  have hw : 0 ≤ roundingSlack t := div_nonneg (Real.log_nonneg ht1) (sq_nonneg t)
  have hw1 : roundingSlack t ≤ 1/100 := ht₂ t htt₂
  have hwt : roundingSlack t*t^2=Real.log t := div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')
  obtain ⟨a₀,b,μ,κ,θ,ha₀,hb,hμ,hμν,hκ,hθ,hθbar,hnorm,hμθ,hopt⟩ :=
    ordinary_threshold_optimization k D H L ρ hk hD hH hL hLH hρ
  have hν := ordinaryNu_properties k D hk hD
  have haLower : 7/10 ≤ a₀ := ordinary_optimization_a_lower k D a₀ hk hD ha₀
  have haUpper : a₀ ≤ 1 := by nlinarith [sq_nonneg b,sq_nonneg μ]
  have ha : 0 ≤ a₀-20*roundingSlack t := by linarith
  have hb1 : |b| ≤ 1 := hb.trans hν.2.1.le
  have hμ1 : μ ≤ 1 := hμν.trans hν.2.1.le
  let e := ordinaryPlaneAxis v r x
  let z : ↥(nbr G F x)→Space d := fun y => ordinaryBoxResidual k v x e y
  let ξ : ↥(nbr G F x)→ℝ := fun y => ordinaryBoxProjection k v x e y
  have hbudget : ∀y : ↥(nbr G F x),(ξ y)^2+‖z y‖^2 ≤ 1 := fun y =>
    ordinary_plane_residual_budget G v k hk hv r x y hx (Finset.mem_filter.mp y.2).2
  have hξ : ∀y,(ξ y)^2 ≤ 1 := fun y => le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hbudget y)
  have hz : ∀y,‖z y‖ ≤ Real.sqrt (1-(ξ y)^2) := by
    intro y
    have hs := Real.sq_sqrt (show 0 ≤ 1-(ξ y)^2 by linarith [hξ y])
    nlinarith [hbudget y,norm_nonneg (z y),Real.sqrt_nonneg (1-(ξ y)^2)]
  have hK₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤
      (cA k*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t} ≤ PhiTail (μ*t) := by
    have hB := ordinary_box_exponential_bound G v k hk hv F x hxF e
      (ordinary_plane_axis_unit G v k hv r x hx) (ordinary_plane_axis_orthogonal G v k hv r x)
      (a₀-20*roundingSlack t) b t ha ht0 hp
    have hT := hTail t htt₁ a₀ b μ haLower haUpper hb1 hμ hμ1 hnorm
    have hset : {g : Space d | ∀y,⟪g,z y⟫ ≤
        (cA k*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t}=
        ordinaryBoxEvent G k v F x e (a₀-20*roundingSlack t) b t := by
      ext g
      simp only [ordinaryBoxEvent,z,ξ,Set.mem_setOf_eq,Subtype.forall,real_inner_comm]
    rw [hset]
    exact hB.trans hT
  have hD0 : 0 ≤ D := (lt_of_le_of_lt (sq_nonneg _) hD).le
  have hK₁ : 1-PhiTail (κ*t) ≤ gaussProb {g : Space d | ∀y,
      ⟪g,z y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t} :=
    gaussian_finite_polytope_large z ξ hξ hz D κ t hD0 hκ ht0.le (by simpa using hcard)
  have hE := ehrhard_transmission_bound z ξ hξ (cA k) (a₀-20*roundingSlack t) b L ρ D μ κ θ t
    (by positivity) hμ hκ hθ ht0.le hK₀ hK₁
  rw [hμθ] at hE
  apply hE.trans
  unfold gaussProb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨y,hy⟩ := hg
  refine ⟨y,y.2,?_⟩
  have hthreshold := extrapolated_threshold_lower (cA k)
    (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))) θ
    ((Real.sqrt H/ordinaryNu k D-1)/(D+1)) (roundingSlack t) t (cA_pos k hk).le hθ hθbar hw ht0
    (by rw [hwt]; exact htlog)
  have heq : ((1+θ)*cA k*(a₀-20*roundingSlack t)-Real.sqrt ((L*ρ-(1+θ)*b)^2+θ^2*(D+κ^2)))*t-(1+θ)/t=
      (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))-20*(1+θ)*cA k*roundingSlack t)*t-(1+θ)/t := by
    rw [← hopt]
    ring
  rw [heq] at hy
  exact hthreshold.trans hy.le

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxEhrhardUniform -/

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_ehrhard_transmission_uniform :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀k D H : ℝ,2<k → (cA k)^2<D → 1<H →
      ∀t : ℝ,t₀ ≤ t → ∀L ρ : ℝ,0<L → L<Real.sqrt H → ρ∈Set.Icc (-1) 1 →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,OrdinaryVectorColoring G v k →
      ∀F : Finset (Fin n),∀r x : Fin n,x∈F → 0<‖uvec v r x‖ →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) →
      ((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2) →
      1-PhiTail (Real.sqrt (H-L^2)*t) ≤ gaussProb {g : Space d | ∃y∈nbr G F x,
        (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))-
          (20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))*roundingSlack t)*t ≤
          ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
            L*ρ*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t} := by
  classical
  obtain ⟨t₁,ht₁,hTail⟩ := gaussian_box_tail_eventually
  have hslack : ∀ᶠ t : ℝ in atTop,roundingSlack t ≤ 1/100 :=
    (roundingSlack_tendsto.eventually_lt_const (by norm_num : (0:ℝ)<1/100)).mono fun _ ht => ht.le
  obtain ⟨t₂,ht₂⟩ := eventually_atTop.mp hslack
  refine ⟨max (max t₁ t₂) (Real.exp 1),?_,?_⟩
  · exact ht₁.trans ((le_max_left t₁ t₂).trans (le_max_left _ _))
  intro k D H hk hD hH t ht L ρ hL hLH hρ n d G v hv F r x hxF hx hp hcard
  have htt₁ : t₁ ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have htt₂ : t₂ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht1 : 1 ≤ t := ht₁.trans htt₁
  have ht0 : 0<t := lt_of_lt_of_le zero_lt_one ht1
  have htlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ((le_max_right _ _).trans ht)
  have hw : 0 ≤ roundingSlack t := div_nonneg (Real.log_nonneg ht1) (sq_nonneg t)
  have hw1 : roundingSlack t ≤ 1/100 := ht₂ t htt₂
  have hwt : roundingSlack t*t^2=Real.log t := div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')
  obtain ⟨a₀,b,μ,κ,θ,ha₀,hb,hμ,hμν,hκ,hθ,hθbar,hnorm,hμθ,hopt⟩ :=
    ordinary_threshold_optimization k D H L ρ hk hD hH hL hLH hρ
  have hν := ordinaryNu_properties k D hk hD
  have haLower : 7/10 ≤ a₀ := ordinary_optimization_a_lower k D a₀ hk hD ha₀
  have haUpper : a₀ ≤ 1 := by nlinarith [sq_nonneg b,sq_nonneg μ]
  have ha : 0 ≤ a₀-20*roundingSlack t := by linarith
  have hb1 : |b| ≤ 1 := hb.trans hν.2.1.le
  have hμ1 : μ ≤ 1 := hμν.trans hν.2.1.le
  let e := ordinaryPlaneAxis v r x
  let z : ↥(nbr G F x)→Space d := fun y => ordinaryBoxResidual k v x e y
  let ξ : ↥(nbr G F x)→ℝ := fun y => ordinaryBoxProjection k v x e y
  have hbudget : ∀y : ↥(nbr G F x),(ξ y)^2+‖z y‖^2 ≤ 1 := fun y =>
    ordinary_plane_residual_budget G v k hk hv r x y hx (Finset.mem_filter.mp y.2).2
  have hξ : ∀y,(ξ y)^2 ≤ 1 := fun y => le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hbudget y)
  have hz : ∀y,‖z y‖ ≤ Real.sqrt (1-(ξ y)^2) := by
    intro y
    have hs := Real.sq_sqrt (show 0 ≤ 1-(ξ y)^2 by linarith [hξ y])
    nlinarith [hbudget y,norm_nonneg (z y),Real.sqrt_nonneg (1-(ξ y)^2)]
  have hK₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤
      (cA k*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t} ≤ PhiTail (μ*t) := by
    have hB := ordinary_box_exponential_bound G v k hk hv F x hxF e
      (ordinary_plane_axis_unit G v k hv r x hx) (ordinary_plane_axis_orthogonal G v k hv r x)
      (a₀-20*roundingSlack t) b t ha ht0 hp
    have hT := hTail t htt₁ a₀ b μ haLower haUpper hb1 hμ hμ1 hnorm
    have hset : {g : Space d | ∀y,⟪g,z y⟫ ≤
        (cA k*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t}=
        ordinaryBoxEvent G k v F x e (a₀-20*roundingSlack t) b t := by
      ext g
      simp only [ordinaryBoxEvent,z,ξ,Set.mem_setOf_eq,Subtype.forall,real_inner_comm]
    rw [hset]
    exact hB.trans hT
  have hD0 : 0 ≤ D := (lt_of_le_of_lt (sq_nonneg _) hD).le
  have hK₁ : 1-PhiTail (κ*t) ≤ gaussProb {g : Space d | ∀y,
      ⟪g,z y⟫ ≤ Real.sqrt (D+κ^2)*Real.sqrt (1-(ξ y)^2)*t} :=
    gaussian_finite_polytope_large z ξ hξ hz D κ t hD0 hκ ht0.le (by simpa using hcard)
  have hE := ehrhard_transmission_bound z ξ hξ (cA k) (a₀-20*roundingSlack t) b L ρ D μ κ θ t
    (by positivity) hμ hκ hθ ht0.le hK₀ hK₁
  rw [hμθ] at hE
  apply hE.trans
  unfold gaussProb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨y,hy⟩ := hg
  refine ⟨y,y.2,?_⟩
  have hthreshold := extrapolated_threshold_lower (cA k)
    (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))) θ
    ((Real.sqrt H/ordinaryNu k D-1)/(D+1)) (roundingSlack t) t (cA_pos k hk).le hθ hθbar hw ht0
    (by rw [hwt]; exact htlog)
  have heq : ((1+θ)*cA k*(a₀-20*roundingSlack t)-Real.sqrt ((L*ρ-(1+θ)*b)^2+θ^2*(D+κ^2)))*t-(1+θ)/t=
      (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))-20*(1+θ)*cA k*roundingSlack t)*t-(1+θ)/t := by
    rw [← hopt]
    ring
  rw [heq] at hy
  exact hthreshold.trans hy.le


end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverBadEvent -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def coverBoxSample {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k : ℝ) (F : Finset (Fin n)) (r x : Fin n) (g : Space d) : (↥(nbr G F x)→ℝ) :=
  fun y => ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫

def coverBadEvent {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k : ℝ) (F : Finset (Fin n)) (r x : Fin n) (U w t : ℝ) : Set (ℝ×(↥(nbr G F x)→ℝ)) :=
  {p | U*t ≤ ‖uvec v r x‖*p.1 ∧ ∀y : ↥(nbr G F x),planeNeighborScore v k r x y p.1 (p.2 y)<(U+40*w)*t}

theorem coverBoxSample_measurable {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k : ℝ) (F : Finset (Fin n)) (r x : Fin n) : Measurable (coverBoxSample G v k F r x) := by
  unfold coverBoxSample
  fun_prop

theorem coverBadEvent_measurable {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k : ℝ) (F : Finset (Fin n)) (r x : Fin n) (U w t : ℝ) :
    MeasurableSet (coverBadEvent G v k F r x U w t) := by
  change MeasurableSet ({p | U*t ≤ ‖uvec v r x‖*p.1} ∩
    {p : ℝ×(↥(nbr G F x)→ℝ) | ∀y : ↥(nbr G F x),planeNeighborScore v k r x y p.1 (p.2 y)<(U+40*w)*t})
  apply MeasurableSet.inter (measurableSet_le measurable_const (by fun_prop))
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro y
  apply measurableSet_setOfPred.mp
  apply measurableSet_lt _ measurable_const
  unfold planeNeighborScore
  fun_prop

theorem cover_bad_fiber_bound {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k D H U w t t₀ : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 1<H)
    (hv : OrdinaryVectorColoring G v k) (F : Finset (Fin n)) (r x : Fin n)
    (hxF : x∈F) (hx : 0<‖uvec v r x‖) (hU : 0<U) (ht : 0<t) (hw : 0 ≤ w)
    (hwt : w=roundingSlack t)
    (hp : pLocal G v F x ≤ Real.exp (-(t^2/2)))
    (hcard : ((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2))
    (hDrift : ∀s : ℝ,0 ≤ s → s ≤ Real.sqrt H →
      (1-1/(k-1))*s+(((1+1/(k-1))/cA k)*((20*cA k+1)*
        (1+(Real.sqrt H/ordinaryNu k D-1)/(D+1)))+40)*w ≤
        ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-s^2)))
    (hTail : ∀k D H : ℝ,2<k → (cA k)^2<D → 1<H → ∀t : ℝ,t₀ ≤ t → ∀L ρ : ℝ,
      0<L → L<Real.sqrt H → ρ∈Set.Icc (-1) 1 →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,OrdinaryVectorColoring G v k →
      ∀F : Finset (Fin n),∀r x : Fin n,x∈F → 0<‖uvec v r x‖ →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) → ((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2) →
      1-PhiTail (Real.sqrt (H-L^2)*t) ≤ gaussProb {g : Space d | ∃y∈nbr G F x,
        (thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-L^2*(1-ρ^2)))-
          (20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))*roundingSlack t)*t ≤
          ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
            L*ρ*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t})
    (htt : t₀ ≤ t) (z : ℝ) (hz0 : 0 ≤ z) (hzA : z<Real.sqrt H*t) :
    ((stdGaussian (Space d)).map (coverBoxSample G v k F r x)).real
      {W | (z,W)∈coverBadEvent G v k F r x U w t} ≤ PhiTail (Real.sqrt ((Real.sqrt H*t)^2-z^2)) := by
  classical
  let E := coverBadEvent G v k F r x U w t
  let W := coverBoxSample G v k F r x
  have hWm : Measurable W := coverBoxSample_measurable G v k F r x
  have hEm : MeasurableSet E := coverBadEvent_measurable G v k F r x U w t
  have hMap : ((stdGaussian (Space d)).map W).real {a | (z,a)∈E}=
      gaussProb {g : Space d | (z,W g)∈E} := by
    change ((stdGaussian (Space d)).map W).real (Prod.mk z ⁻¹' E)=_
    rw [map_measureReal_apply hWm (measurable_prodMk_left hEm)]
    rfl
  rw [hMap]
  by_cases hTrigger : U*t ≤ ‖uvec v r x‖*z
  · have hz : 0<z := by nlinarith only [hTrigger,mul_pos hU ht,hx]
    have hL : 0<z/t := div_pos hz ht
    have hLH : z/t<Real.sqrt H := (div_lt_iff₀ ht).mpr hzA
    let B : ℝ := thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-(z/t)^2*(1-(rho v r x)^2)))-
      (20*cA k+1)*(1+(Real.sqrt H/ordinaryNu k D-1)/(D+1))*w
    let S : Set (Space d) := {g | ∃y∈nbr G F x,
      B*t ≤ ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫+
        (z/t)*rho v r x*ordinaryBoxProjection k v x (ordinaryPlaneAxis v r x) y*t}
    have hS : MeasurableSet S := by
      apply measurableSet_setOfPred.mpr
      apply Measurable.exists
      intro y
      apply Measurable.and measurable_const
      exact measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))
    have hT : 1-PhiTail (Real.sqrt (H-(z/t)^2)*t) ≤ gaussProb S := by
      have h := hTail k D H hk hD hH t htt (z/t) (rho v r x) hL hLH
        (ordinary_root_rho_mem G v k hv r x) n d G v hv F r x hxF hx hp hcard
      simpa only [← hwt,B,S] using h
    have hComp : gaussProb Sᶜ ≤ PhiTail (Real.sqrt (H-(z/t)^2)*t) := by
      unfold gaussProb at hT ⊢
      rw [probReal_compl_eq_one_sub hS]
      linarith only [hT]
    have hSub : {g : Space d | (z,W g)∈E} ⊆ Sᶜ := by
      intro g hg hs
      obtain ⟨y,hy,hQ⟩ := hs
      have hscore := ordinary_cover_slice_threshold G v k D H U w t z hk hH hv r x y hx
        (Finset.mem_filter.mp hy).2 ht hz hzA hw hTrigger hDrift
        ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫ hQ
      have hbad := hg.2 ⟨y,hy⟩
      exact not_lt_of_ge hscore hbad
    apply (measureReal_mono hSub (measure_ne_top _ _)).trans
    apply hComp.trans_eq
    congr 1
    have hH0 : 0 ≤ H := by linarith
    have hsub : 0 ≤ H-(z/t)^2 := by nlinarith only [hL,hLH,Real.sq_sqrt hH0,Real.sqrt_nonneg H]
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hz0,hzA,Real.sqrt_nonneg H,mul_nonneg (Real.sqrt_nonneg H) ht.le])
      (mul_nonneg (Real.sqrt_nonneg _) ht.le)).mpr
    simp only [mul_pow,Real.sq_sqrt hH0,Real.sq_sqrt hsub]
    field_simp
    <;> ring
  · have he : {g : Space d | (z,W g)∈E}=∅ := by
      ext g
      constructor
      · intro hg
        exact (hTrigger hg.1).elim
      · intro hg
        exact hg.elim
    rw [he]
    simpa only [gaussProb,measureReal_empty] using phiTail_nonneg (Real.sqrt ((Real.sqrt H*t)^2-z^2))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverOneVertex -/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_cover_one_vertex_bound :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀k D H U w t : ℝ,2<k → (cA k)^2<D → 1<H → 0<U →
      0<t → 0 ≤ w → w=roundingSlack t → t₀ ≤ t →
      (∀s : ℝ,0 ≤ s → s ≤ Real.sqrt H →
        (1-1/(k-1))*s+(((1+1/(k-1))/cA k)*((20*cA k+1)*
          (1+(Real.sqrt H/ordinaryNu k D-1)/(D+1)))+40)*w ≤
          ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-s^2))) →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,OrdinaryVectorColoring G v k →
      ∀F : Finset (Fin n),∀r x : Fin n,x∈F → 0<‖uvec v r x‖ →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) → ((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2) →
      gaussProb {g : Space d | ⟪g,uvec v r x⟫ ≤ -(U*t) ∧
        ∀y∈nbr G F x,⟪g,uvec v r y⟫<(U+40*w)*t} ≤
        (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(H*t^2/2)) := by
  classical
  obtain ⟨t₀,ht₀,hTail⟩ := ordinary_ehrhard_transmission_uniform
  refine ⟨t₀,ht₀,?_⟩
  intro k D H U w t hk hD hH hU ht hw hwt htt hDrift n d G v hv F r x hxF hx hp hcard
  let axis : Space d := -(‖uvec v r x‖⁻¹ • uvec v r x)
  let X : Space d→ℝ := fun g => -⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫
  let W := coverBoxSample G v k F r x
  let z : ↥(nbr G F x)→Space d := fun y => ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y
  let E := coverBadEvent G v k F r x U w t
  have haxis : ‖axis‖=1 := by
    dsimp [axis]
    rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hx),inv_mul_cancel₀ hx.ne']
  have haxz : ∀y,⟪axis,z y⟫=0 := by
    intro y
    simp only [axis,z,inner_neg_left,real_inner_smul_left,
      ordinary_plane_residual_inner_root_axis G v k hv r x y hx,mul_zero,neg_zero]
  have hXm : Measurable X := by dsimp [X]; fun_prop
  have hWm : Measurable W := coverBoxSample_measurable G v k F r x
  have hN : (stdGaussian (Space d)).map X=gaussianReal 0 1 := by
    simpa only [axis,X,inner_neg_left,real_inner_smul_left,real_inner_smul_right,real_inner_comm] using
      gaussian_inner_map axis haxis
  have hI : IndepFun X W (stdGaussian (Space d)) := by
    change IndepFun X (fun g (y : ↥(nbr G F x)) =>
      ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫) (stdGaussian (Space d))
    simpa only [axis,X,W,coverBoxSample,z,inner_neg_left,real_inner_smul_left,real_inner_smul_right,real_inner_comm] using
      gaussian_orthogonal_family_independent axis z haxz
  have hpos : ∀p∈E,0 ≤ p.1 := by
    intro p hp
    have h : 0<‖uvec v r x‖*p.1 := (mul_pos hU ht).trans_le hp.1
    exact (pos_of_mul_pos_right h hx.le).le
  have hgood : ∀Z,0 ≤ Z → Z<Real.sqrt H*t →
      ((stdGaussian (Space d)).map W).real {a | (Z,a)∈E} ≤ PhiTail (Real.sqrt ((Real.sqrt H*t)^2-Z^2)) := by
    intro Z hZ hZA
    exact cover_bad_fiber_bound G v k D H U w t t₀ hk hD hH hv F r x hxF hx hU ht hw hwt hp hcard
      hDrift hTail htt Z hZ hZA
  have hB := independent_gaussian_bad_event_bound (stdGaussian (Space d)) X W hXm hWm hI hN E
    (coverBadEvent_measurable G v k F r x U w t) (Real.sqrt H*t)
    (mul_nonneg (Real.sqrt_nonneg _) ht.le) hpos hgood
  have hscore : ∀g : Space d,⟪g,uvec v r x⟫=-‖uvec v r x‖*X g := by
    intro g
    dsimp [X]
    rw [real_inner_smul_right]
    field_simp
  have hSub : {g : Space d | ⟪g,uvec v r x⟫ ≤ -(U*t) ∧
      ∀y∈nbr G F x,⟪g,uvec v r y⟫<(U+40*w)*t} ⊆ {g : Space d | (X g,W g)∈E} := by
    intro g hg
    refine ⟨?_,?_⟩
    · nlinarith only [hg.1,hscore g]
    · intro y
      change planeNeighborScore v k r x y (-⟪g,‖uvec v r x‖⁻¹ • uvec v r x⟫)
        ⟪g,ordinaryBoxResidual k v x (ordinaryPlaneAxis v r x) y⟫<(U+40*w)*t
      rw [← plane_neighbor_score_eq G v k hk hv r x y hx (Finset.mem_filter.mp y.2).2 g]
      exact hg.2 y y.2
  have hExp : (Real.sqrt H*t)^2=H*t^2 := by rw [mul_pow,Real.sq_sqrt (by linarith : 0 ≤ H)]
  have hResult := (measureReal_mono hSub (measure_ne_top _ _)).trans hB
  rw [hExp] at hResult
  exact hResult

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverUnion -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def neighborUnion {n : ℕ} (G : SimpleGraph (Fin n)) (F W : Finset (Fin n)) : Finset (Fin n) :=
  W.biUnion (nbr G F)

theorem finite_cover_lifting {n d : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n→Space d)
    (F W : Finset (Fin n)) (s t q ε : ℝ)
    (hCover : IsCover (W.image u) s q)
    (hBad : ∀x∈W,gaussProb {g : Space d | ⟪g,u x⟫ ≤ -s ∧ ∀y∈nbr G F x,⟪g,u y⟫<t} ≤ ε) :
    IsCover ((neighborUnion G F W).image u) t (q-(W.card:ℝ)*ε) := by
  classical
  let A : Set (Space d) := {g | ∃x∈W,⟪g,u x⟫ ≤ -s}
  let B : Set (Space d) := {g | ∃y∈neighborUnion G F W,t ≤ ⟪g,u y⟫}
  let E : Set (Space d) := {g | ∃x∈W,⟪g,u x⟫ ≤ -s ∧ ∀y∈nbr G F x,⟪g,u y⟫<t}
  have hA : q ≤ gaussProb A := by
    have hC : q ≤ gaussProb {g : Space d | ∃x∈W,s ≤ ⟪g,u x⟫} := by
      simpa only [IsCover,Finset.mem_image,exists_exists_and_eq_and] using hCover
    have hSym := gaussian_cover_symmetry (fun x : ↥W => u x) s
    have hSym' : gaussProb {g : Space d | ∃x∈W,s ≤ ⟪g,u x⟫}=gaussProb A := by
      simpa only [A,Subtype.exists,exists_prop] using hSym
    rw [← hSym']
    exact hC
  have hE : gaussProb E ≤ (W.card:ℝ)*ε := by
    have heq : E=⋃x∈W,{g : Space d | ⟪g,u x⟫ ≤ -s ∧ ∀y∈nbr G F x,⟪g,u y⟫<t} := by
      ext g
      simp only [E,Set.mem_iUnion,Set.mem_setOf_eq]
      aesop
    unfold gaussProb
    rw [heq]
    calc
      _ ≤ ∑x∈W,(stdGaussian (Space d)).real {g : Space d | ⟪g,u x⟫ ≤ -s ∧
          ∀y∈nbr G F x,⟪g,u y⟫<t} := measureReal_biUnion_finset_le _ _
      _ ≤ ∑_x∈W,ε := Finset.sum_le_sum (fun x hx => hBad x hx)
      _ = _ := by simp
  have hSub : A ⊆ B∪E := by
    intro g hg
    by_cases hgB : g∈B
    · exact Or.inl hgB
    · obtain ⟨x,hx,hxg⟩ := hg
      apply Or.inr
      refine ⟨x,hx,hxg,?_⟩
      intro y hy
      apply lt_of_not_ge
      intro hyt
      exact hgB ⟨y,Finset.mem_biUnion.mpr ⟨x,hx,hy⟩,hyt⟩
  have hAB : gaussProb A ≤ gaussProb B+gaussProb E :=
    (measureReal_mono hSub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have hB : q-(W.card:ℝ)*ε ≤ gaussProb B := by linarith only [hA,hE,hAB]
  simpa only [IsCover,Finset.mem_image,exists_exists_and_eq_and,B] using hB

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxGapBound -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_gap_positive_lower (k D H B S : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 0 ≤ H)
    (hEx : 0 ≤ k*D-H*((k-2)*D-2))
    (hB : (k-1)*(D+1) ≤ B)
    (hS : Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1))) ≤ S) :
    2*(k*D-H*((k-2)*D-2))/(B*S) ≤ ordinaryGap k D H := by
  have hk1 : 0<k-1 := by linarith
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hD1 : 0<D+1 := by linarith
  have hden : 0<(k-1)*(D+1) := mul_pos hk1 hD1
  have hsum : 0<Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1))) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_nonneg _)
  have hB0 : 0<B := hden.trans_le hB
  have hS0 : 0<S := hsum.trans_le hS
  rw [ordinary_gap_rationalized k D H hk hD hH,div_div]
  apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hEx) (mul_pos hden hsum)
  exact mul_le_mul hB hS hsum.le hB0.le

theorem ordinary_drift_of_excess (k D H B S R w : ℝ) (hk : 2<k) (hD : (cA k)^2<D) (hH : 1<H)
    (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hB : (k-1)*(D+1) ≤ B)
    (hS : Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1))) ≤ S)
    (hEx : R*w*(B*S) ≤ 2*(k*D-H*((k-2)*D-2))) :
    ∀U : ℝ,0 ≤ U → U ≤ Real.sqrt H →
      (1-1/(k-1))*U+R*w ≤
        ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-U^2)) := by
  have hk1 : 0<k-1 := by linarith
  have hD0 : 0<D := lt_of_le_of_lt (sq_nonneg _) hD
  have hden : 0<(k-1)*(D+1) := by positivity
  have hB0 : 0<B := hden.trans_le hB
  have hsum : 0<Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1))) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_nonneg _)
  have hS0 : 0<S := hsum.trans_le hS
  have hBS : 0<B*S := mul_pos hB0 hS0
  have hEx0 : 0 ≤ k*D-H*((k-2)*D-2) := by
    have h := mul_nonneg (mul_nonneg hR hw) hBS.le
    linarith only [h,hEx]
  have hgap := ordinary_gap_positive_lower k D H B S hk hD (by linarith) hEx0 hB hS
  have hRg : R*w ≤ ordinaryGap k D H :=
    ((le_div_iff₀ hBS).mpr hEx).trans hgap
  intro U hU hUH
  have h := ordinary_drift_gap k D H U hk hD hH hU hUH
  linarith only [hRg,h]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxExcessIdentity -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem high_degree_excess_identity (k β Cl N ell t w : ℝ)
    (hden : 2+k*β≠0) (ht : t≠0) (hw : w≠0)
    (hscale : t^2=2*((k-2)*β/(2+k*β))*N+2*Cl*ell) :
    (k*(2*β*N/t^2)-(2*N/t^2+40*w)*((k-2)*(2*β*N/t^2)-2))/w=
      4*Cl*(2+k*β)*(N/t^2)*(ell/(w*t^2))-40*((k-2)*(2*β*N/t^2)-2) := by
  have hscaled : (2+k*β)*t^2-2*(k-2)*β*N=2*Cl*(2+k*β)*ell := by
    have h := congrArg (fun z : ℝ => (2+k*β)*z) hscale
    field_simp at h
    nlinarith only [h]
  have hbase : k*(2*β*N/t^2)-(2*N/t^2)*((k-2)*(2*β*N/t^2)-2)=
      2*N*((2+k*β)*t^2-2*(k-2)*β*N)/t^4 := by
    field_simp
    <;> ring
  calc
    (k*(2*β*N/t^2)-(2*N/t^2+40*w)*((k-2)*(2*β*N/t^2)-2))/w=
      (k*(2*β*N/t^2)-(2*N/t^2)*((k-2)*(2*β*N/t^2)-2))/w-
        40*((k-2)*(2*β*N/t^2)-2) := by
          field_simp
          <;> ring
    _ = _ := by
      rw [hbase,hscaled]
      field_simp
      <;> ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxExcessBound -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem high_degree_excess_lower (k β Cl N ell t w a B : ℝ)
    (hK : 0<2+k*β) (hCl : 0 ≤ Cl) (ha : 0<a) (ht : 0<t) (hw : 0<w)
    (hscale : t^2=2*((k-2)*β/(2+k*β))*N+2*Cl*ell)
    (hN : 1/(4*a) ≤ N/t^2) (hL : 1 ≤ ell/(w*t^2))
    (hB : (k-2)*(2*β*N/t^2)-2 ≤ B) :
    Cl*(2+k*β)/a-40*B ≤
      (k*(2*β*N/t^2)-(2*N/t^2+40*w)*((k-2)*(2*β*N/t^2)-2))/w := by
  rw [high_degree_excess_identity k β Cl N ell t w hK.ne' ht.ne' hw.ne' hscale]
  have hcoef : 0 ≤ 4*Cl*(2+k*β) := by positivity
  have hN0 : 0 ≤ N/t^2 := (by positivity : (0:ℝ) ≤ 1/(4*a)).trans hN
  have hprod : Cl*(2+k*β)/a ≤ 4*Cl*(2+k*β)*(N/t^2)*(ell/(w*t^2)) := by
    calc
      Cl*(2+k*β)/a=(4*Cl*(2+k*β))*(1/(4*a)) := by ring
      _ ≤ (4*Cl*(2+k*β))*(N/t^2) := mul_le_mul_of_nonneg_left hN hcoef
      _ ≤ (4*Cl*(2+k*β))*(N/t^2)*(ell/(w*t^2)) := by
        have h := mul_le_mul_of_nonneg_left hL (mul_nonneg hcoef hN0)
        simpa only [mul_one] using h
  nlinarith only [hprod,hB]

theorem ordinary_drift_from_scale (k β Cl N ell t w a B Bden S R : ℝ)
    (hk : 2<k) (hK : 0<2+k*β) (hCl : 0 ≤ Cl) (ha : 0<a) (ht : 0<t) (hw : 0<w)
    (hscale : t^2=2*((k-2)*β/(2+k*β))*N+2*Cl*ell)
    (hN : 1/(4*a) ≤ N/t^2) (hL : 1 ≤ ell/(w*t^2))
    (hB : (k-2)*(2*β*N/t^2)-2 ≤ B)
    (hD : (cA k)^2<2*β*N/t^2) (hH : 1<2*N/t^2+40*w) (hR : 0 ≤ R)
    (hBden : (k-1)*(2*β*N/t^2+1) ≤ Bden)
    (hS : Real.sqrt (2*k*(2*β*N/t^2)/((k-1)*(2*β*N/t^2+1)))+
      Real.sqrt (2*(2*N/t^2+40*w)*((k-2)*(2*β*N/t^2)-2)/((k-1)*(2*β*N/t^2+1))) ≤ S)
    (hClLarge : R*(Bden*S)/2+40*B ≤ Cl*(2+k*β)/a) :
    ∀U : ℝ,0 ≤ U → U ≤ Real.sqrt (2*N/t^2+40*w) →
      (1-1/(k-1))*U+R*w ≤
        ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k (2*β*N/t^2))
          (Real.sqrt ((2*N/t^2+40*w)-U^2)) := by
  have hEx := high_degree_excess_lower k β Cl N ell t w a B hK hCl ha ht hw hscale hN hL hB
  have hRatio : R*(Bden*S)/2 ≤
      (k*(2*β*N/t^2)-(2*N/t^2+40*w)*((k-2)*(2*β*N/t^2)-2))/w := by
    linarith only [hEx,hClLarge]
  have hMul := (le_div_iff₀ hw).mp hRatio
  apply ordinary_drift_of_excess k (2*β*N/t^2) (2*N/t^2+40*w) Bden S R w hk hD hH hw.le hR hBden hS
  nlinarith only [hMul]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLogLevels -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem log_nat_tendsto_atTop : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem numLevels_real_tendsto_atTop : Tendsto (fun n : ℕ => (numLevels n:ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_ceil (Real.log (n:ℝ))) log_nat_tendsto_atTop

theorem numLevels_over_log_tendsto :
    Tendsto (fun n : ℕ => (numLevels n:ℝ)/Real.log (n:ℝ)) atTop (𝓝 1) := by
  have hInv : Tendsto (fun n : ℕ => 1/Real.log (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_nat_tendsto_atTop
  have hE : Tendsto (fun n : ℕ => (numLevels n:ℝ)/Real.log (n:ℝ)-1) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hInv
    · filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
      have h : 1 ≤ (numLevels n:ℝ)/Real.log (n:ℝ) :=
        (le_div_iff₀ hn).mpr (by simpa only [numLevels,one_mul] using Nat.le_ceil (Real.log (n:ℝ)))
      linarith
    · filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
      have hceil : (numLevels n:ℝ) ≤ Real.log (n:ℝ)+1 := (Nat.ceil_lt_add_one hn.le).le
      have h : (numLevels n:ℝ)/Real.log (n:ℝ) ≤ 1/Real.log (n:ℝ)+1 := by
        apply (div_le_iff₀ hn).mpr
        have hi : (1/Real.log (n:ℝ))*Real.log (n:ℝ)=1 := div_mul_cancel₀ 1 hn.ne'
        nlinarith only [hceil,hi]
      linarith
  simpa only [sub_add_cancel,zero_add] using hE.add_const 1

theorem log_numLevels_over_log_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (numLevels n:ℝ)/Real.log (n:ℝ)) atTop (𝓝 0) := by
  have hL : Tendsto (fun n : ℕ => Real.log (numLevels n:ℝ)/(numLevels n:ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp numLevels_real_tendsto_atTop
  have hprod := hL.mul numLevels_over_log_tendsto
  have hcongr : (fun n : ℕ => (Real.log (numLevels n:ℝ)/(numLevels n:ℝ))*
      ((numLevels n:ℝ)/Real.log (n:ℝ))) =ᶠ[atTop]
      (fun n : ℕ => Real.log (numLevels n:ℝ)/Real.log (n:ℝ)) := by
    filter_upwards [numLevels_real_tendsto_atTop.eventually_gt_atTop 0] with n hn
    field_simp
  simpa only [zero_mul] using hprod.congr' hcongr

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxScaleLimits -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def highDegreeRate (k β : ℝ) : ℝ := (k-2)*β/(2+k*β)
def highDegreeSquare (k β Cl : ℝ) (n : ℕ) : ℝ :=
  2*highDegreeRate k β*Real.log (n:ℝ)+2*Cl*Real.log (numLevels n:ℝ)
def highDegreeT (k β Cl : ℝ) (n : ℕ) : ℝ := Real.sqrt (highDegreeSquare k β Cl n)
def highDegreeD (k β Cl : ℝ) (n : ℕ) : ℝ := 2*β*Real.log (n:ℝ)/highDegreeSquare k β Cl n
def highDegreeH0 (k β Cl : ℝ) (n : ℕ) : ℝ := 2*Real.log (n:ℝ)/highDegreeSquare k β Cl n
def highDegreeH (k β Cl : ℝ) (n : ℕ) : ℝ :=
  highDegreeH0 k β Cl n+40*roundingSlack (highDegreeT k β Cl n)

theorem highDegreeSquare_over_log_tendsto (k β Cl : ℝ) :
    Tendsto (fun n : ℕ => highDegreeSquare k β Cl n/Real.log (n:ℝ)) atTop (𝓝 (2*highDegreeRate k β)) := by
  have h := (tendsto_const_nhds (x:=2*highDegreeRate k β)).add
    (log_numLevels_over_log_tendsto_zero.const_mul (2*Cl))
  have hcongr : (fun n : ℕ => 2*highDegreeRate k β+(2*Cl)*
      (Real.log (numLevels n:ℝ)/Real.log (n:ℝ))) =ᶠ[atTop]
      (fun n : ℕ => highDegreeSquare k β Cl n/Real.log (n:ℝ)) := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
    unfold highDegreeSquare
    field_simp
    <;> ring
  simpa only [mul_zero,add_zero] using h.congr' hcongr

theorem highDegreeSquare_tendsto_atTop (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (highDegreeSquare k β Cl) atTop atTop := by
  have hratio := (highDegreeSquare_over_log_tendsto k β Cl).eventually_const_lt
    (show highDegreeRate k β<2*highDegreeRate k β by linarith)
  have hLower : ∀ᶠ n : ℕ in atTop,highDegreeRate k β*Real.log (n:ℝ) ≤ highDegreeSquare k β Cl n := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,hratio] with n hn hr
    exact ((lt_div_iff₀ hn).mp hr).le
  exact tendsto_atTop_mono' atTop hLower (log_nat_tendsto_atTop.const_mul_atTop ha)

theorem highDegreeT_tendsto_atTop (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (highDegreeT k β Cl) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (highDegreeSquare_tendsto_atTop k β Cl ha)

theorem highDegreeD_tendsto (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (highDegreeD k β Cl) atTop (𝓝 (β/highDegreeRate k β)) := by
  have h := (tendsto_const_nhds (x:=2*β)).div (highDegreeSquare_over_log_tendsto k β Cl)
    (show 2*highDegreeRate k β≠0 by positivity)
  have hcongr : (fun n : ℕ => (2*β)/(highDegreeSquare k β Cl n/Real.log (n:ℝ))) =ᶠ[atTop]
      highDegreeD k β Cl := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
    unfold highDegreeD
    field_simp
  have heq : 2*β/(2*highDegreeRate k β)=β/highDegreeRate k β := by ring
  rw [heq] at h
  exact h.congr' hcongr

theorem highDegreeH0_tendsto (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (highDegreeH0 k β Cl) atTop (𝓝 (1/highDegreeRate k β)) := by
  have h := (tendsto_const_nhds (x:=(2:ℝ))).div (highDegreeSquare_over_log_tendsto k β Cl)
    (show 2*highDegreeRate k β≠0 by positivity)
  have hcongr : (fun n : ℕ => 2/(highDegreeSquare k β Cl n/Real.log (n:ℝ))) =ᶠ[atTop]
      highDegreeH0 k β Cl := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
    unfold highDegreeH0
    field_simp
  have heq : 2/(2*highDegreeRate k β)=1/highDegreeRate k β := by ring
  rw [heq] at h
  exact h.congr' hcongr

theorem highDegreeH_tendsto (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (highDegreeH k β Cl) atTop (𝓝 (1/highDegreeRate k β)) := by
  change Tendsto (fun n => highDegreeH0 k β Cl n+40*roundingSlack (highDegreeT k β Cl n)) atTop _
  have hslack := roundingSlack_tendsto.comp (highDegreeT_tendsto_atTop k β Cl ha)
  simpa only [Function.comp_apply,mul_zero,add_zero] using (highDegreeH0_tendsto k β Cl ha).add (hslack.const_mul 40)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxPublicScale -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegreeSquare_eq_neg_log_deltaA (k β Cl : ℝ) (n : ℕ)
    (hreg : (k-2)/k<β) (hn : 2 ≤ n) :
    highDegreeSquare k β Cl n=-2*Real.log (deltaA k β Cl n) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hell : 0<(numLevels n:ℝ) := (Real.log_pos hn1).trans_le (Nat.le_ceil _)
  have hnp : (n:ℝ)^(-((k-2)*β/(2+k*β)))≠0 := (Real.rpow_pos_of_pos hn0 _).ne'
  have hep : (numLevels n:ℝ)^(-Cl)≠0 := (Real.rpow_pos_of_pos hell _).ne'
  rw [deltaA,if_neg (not_le_of_gt hreg),Real.log_mul hnp hep,
    Real.log_rpow hn0,Real.log_rpow hell]
  unfold highDegreeSquare highDegreeRate
  ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxScaleRegime -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegreeRate_properties (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    0<highDegreeRate k β ∧ highDegreeRate k β<1 ∧
      (cA k)^2<β/highDegreeRate k β ∧ 1<1/highDegreeRate k β := by
  have hk0 : 0<k := by linarith
  have hk2 : 0<k-2 := by linarith
  have hden : 0<2+k*β := by positivity
  have ha : 0<highDegreeRate k β := div_pos (mul_pos hk2 hβ) hden
  have ha1 : highDegreeRate k β<1 := (div_lt_one hden).mpr (by nlinarith)
  have hD : β/highDegreeRate k β=(2+k*β)/(k-2) := by
    unfold highDegreeRate
    field_simp
  refine ⟨ha,ha1,?_,?_⟩
  · rw [hD,cA_sq k hk]
    apply (div_lt_div_iff_of_pos_right hk2).mpr
    have h := (div_lt_iff₀ hk0).mp hreg
    nlinarith
  · exact (one_lt_div ha).mpr ha1

theorem highDegree_eventually_regime (k β Cl : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    ∀ᶠ n : ℕ in atTop,(cA k)^2<highDegreeD k β Cl n ∧ 1<highDegreeH k β Cl n ∧
      Real.exp 1<highDegreeT k β Cl n ∧ 0<highDegreeSquare k β Cl n := by
  have hp := highDegreeRate_properties k β hk hβ hreg
  filter_upwards [(highDegreeD_tendsto k β Cl hp.1).eventually_const_lt hp.2.2.1,
    (highDegreeH_tendsto k β Cl hp.1).eventually_const_lt hp.2.2.2,
    (highDegreeT_tendsto_atTop k β Cl hp.1).eventually_gt_atTop (Real.exp 1),
    (highDegreeSquare_tendsto_atTop k β Cl hp.1).eventually_gt_atTop 0] with n hD hH hT hs
  exact ⟨hD,hH,hT,hs⟩

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxScaleBounds -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem log_over_highDegreeSquare_tendsto (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => Real.log (n:ℝ)/highDegreeSquare k β Cl n) atTop (𝓝 (1/(2*highDegreeRate k β))) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).div (highDegreeSquare_over_log_tendsto k β Cl)
    (show 2*highDegreeRate k β≠0 by positivity)
  apply h.congr'
  filter_upwards [] with n
  change 1/(highDegreeSquare k β Cl n/Real.log (n:ℝ))=Real.log (n:ℝ)/highDegreeSquare k β Cl n
  simp only [one_div,inv_div]

theorem highDegreeT_le_numLevels_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    ∀ᶠ n : ℕ in atTop,highDegreeT k β Cl n ≤ (numLevels n:ℝ) := by
  have hr := (highDegreeSquare_over_log_tendsto k β Cl).eventually_lt_const
    (show 2*highDegreeRate k β<4*highDegreeRate k β by linarith)
  filter_upwards [hr,log_nat_tendsto_atTop.eventually_ge_atTop (4*highDegreeRate k β),
    (highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0] with n hr hn hs
  have hn0 : 0<Real.log (n:ℝ) := lt_of_lt_of_le (by positivity) hn
  have hupper := (div_lt_iff₀ hn0).mp hr
  have hlev : Real.log (n:ℝ) ≤ (numLevels n:ℝ) := Nat.le_ceil _
  have hT2 : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hs.le
  have hN2 : 4*highDegreeRate k β*Real.log (n:ℝ) ≤ (Real.log (n:ℝ))^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hn0.le]
  have hlev0 : 0 ≤ (numLevels n:ℝ) := Nat.cast_nonneg _
  nlinarith only [hupper,hN2,hT2,hlev,hn0,Real.sqrt_nonneg (highDegreeSquare k β Cl n),hlev0]

theorem highDegree_excess_ratio_bounds_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    ∀ᶠ n : ℕ in atTop,0<roundingSlack (highDegreeT k β Cl n) ∧
      1/(4*highDegreeRate k β) ≤ Real.log (n:ℝ)/(highDegreeT k β Cl n)^2 ∧
      1 ≤ Real.log (numLevels n:ℝ)/(roundingSlack (highDegreeT k β Cl n)*(highDegreeT k β Cl n)^2) := by
  have hN := (log_over_highDegreeSquare_tendsto k β Cl ha).eventually_const_lt
    (show 1/(4*highDegreeRate k β)<1/(2*highDegreeRate k β) by
      apply div_lt_div_of_pos_left zero_lt_one (by positivity)
      linarith)
  filter_upwards [hN,highDegreeT_le_numLevels_eventually k β Cl ha,
    (highDegreeT_tendsto_atTop k β Cl ha).eventually_gt_atTop 1,
    (highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0] with n hN hlev ht hs
  have ht0 : 0<highDegreeT k β Cl n := zero_lt_one.trans ht
  have hT2 : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hs.le
  have hlog : 0<Real.log (highDegreeT k β Cl n) := Real.log_pos ht
  have hw : 0<roundingSlack (highDegreeT k β Cl n) := div_pos hlog (pow_pos ht0 2)
  refine ⟨hw,?_,?_⟩
  · rw [hT2]
    exact hN.le
  · have hwt : roundingSlack (highDegreeT k β Cl n)*(highDegreeT k β Cl n)^2=
        Real.log (highDegreeT k β Cl n) := div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')
    rw [hwt]
    apply (le_div_iff₀ hlog).mpr
    simpa only [one_mul] using Real.log_le_log ht0 hlev

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxParameterBounds -/

set_option autoImplicit false
set_option maxHeartbeats 1400000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def highDegreeTheta (k β Cl : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt (highDegreeH k β Cl n)/ordinaryNu k (highDegreeD k β Cl n)-1)/(highDegreeD k β Cl n+1)

def highDegreeDriftCost (k β Cl : ℝ) (n : ℕ) : ℝ :=
  ((1+1/(k-1))/cA k)*(20*cA k+1)*(1+highDegreeTheta k β Cl n)+40

def gapRootSum (k D H : ℝ) : ℝ :=
  Real.sqrt (2*k*D/((k-1)*(D+1)))+Real.sqrt (2*H*((k-2)*D-2)/((k-1)*(D+1)))

theorem highDegree_parameter_bounds (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    ∃B Bden S R : ℝ,0<B ∧ 0<Bden ∧ 0<S ∧ 0<R ∧ ∀Cl : ℝ,
      ∀ᶠ n : ℕ in atTop,(k-2)*highDegreeD k β Cl n-2 ≤ B ∧
        (k-1)*(highDegreeD k β Cl n+1) ≤ Bden ∧
        gapRootSum k (highDegreeD k β Cl n) (highDegreeH k β Cl n) ≤ S ∧
        highDegreeDriftCost k β Cl n ≤ R := by
  have hp := highDegreeRate_properties k β hk hβ hreg
  let D₀ := β/highDegreeRate k β
  let H₀ := 1/highDegreeRate k β
  let ν₀ := ordinaryNu k D₀
  let Θ₀ := (Real.sqrt H₀/ν₀-1)/(D₀+1)
  let R₀ := ((1+1/(k-1))/cA k)*(20*cA k+1)*(1+Θ₀)+40
  let B₀ := (k-2)*D₀-2
  let Bden₀ := (k-1)*(D₀+1)
  let S₀ := gapRootSum k D₀ H₀
  have hD₀ : 0<D₀ := div_pos hβ hp.1
  have hk1 : 0<k-1 := by linarith
  have hD1 : 0<D₀+1 := by linarith
  have hden0 : 0<Bden₀ := mul_pos hk1 hD1
  have hB₀ : 0<B₀ := by
    have h := hp.2.2.1
    rw [cA_sq k hk] at h
    have h' := (div_lt_iff₀ (show 0<k-2 by linarith)).mp h
    dsimp [B₀,D₀]
    nlinarith only [h',hk]
  have hν₀ : 0<ν₀ := (ordinaryNu_properties k D₀ hk hp.2.2.1).1
  have hS₀ : 0 ≤ S₀ := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨B₀+1,Bden₀+1,S₀+1,|R₀|+1,by linarith,by linarith,by linarith,by positivity,?_⟩
  intro Cl
  have hD := highDegreeD_tendsto k β Cl hp.1
  have hH := highDegreeH_tendsto k β Cl hp.1
  have hden : Tendsto (fun n => (k-1)*(highDegreeD k β Cl n+1)) atTop (𝓝 Bden₀) :=
    (hD.add_const 1).const_mul (k-1)
  have hν : Tendsto (fun n => ordinaryNu k (highDegreeD k β Cl n)) atTop (𝓝 ν₀) := by
    unfold ordinaryNu
    exact (((hD.const_mul (k-2)).sub_const k).div (hD.const_mul (2*(k-1))) (by positivity)).sqrt
  have hΘ : Tendsto (highDegreeTheta k β Cl) atTop (𝓝 Θ₀) := by
    change Tendsto (fun n => (Real.sqrt (highDegreeH k β Cl n)/ordinaryNu k (highDegreeD k β Cl n)-1)/
      (highDegreeD k β Cl n+1)) atTop _
    exact ((hH.sqrt.div hν hν₀.ne').sub_const 1).div (hD.add_const 1) hD1.ne'
  have hR : Tendsto (highDegreeDriftCost k β Cl) atTop (𝓝 R₀) := by
    change Tendsto (fun n => ((1+1/(k-1))/cA k)*(20*cA k+1)*(1+highDegreeTheta k β Cl n)+40) atTop _
    exact (((hΘ.const_add 1).const_mul (((1+1/(k-1))/cA k)*(20*cA k+1))).add_const 40)
  have hS : Tendsto (fun n => gapRootSum k (highDegreeD k β Cl n) (highDegreeH k β Cl n)) atTop (𝓝 S₀) := by
    unfold gapRootSum
    simpa only [S₀,gapRootSum,Bden₀,D₀,H₀,mul_assoc,Pi.div_apply] using (((hD.const_mul (2*k)).div hden hden0.ne').sqrt).add
      ((((hH.mul ((hD.const_mul (k-2)).sub_const 2)).const_mul 2).div hden hden0.ne').sqrt)
  have hB := ((hD.const_mul (k-2)).sub_const 2).eventually_lt_const (show B₀<B₀+1 by linarith)
  have hBd := hden.eventually_lt_const (show Bden₀<Bden₀+1 by linarith)
  have hSb := hS.eventually_lt_const (show S₀<S₀+1 by linarith)
  have hRb := hR.eventually_lt_const (show R₀ < |R₀| + 1 by linarith [le_abs_self R₀])
  filter_upwards [hB,hBd,hSb,hRb] with n hb hbd hs hr
  exact ⟨hb.le,hbd.le,hs.le,hr.le⟩

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxDrift -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_drift_eventually (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    ∃Cl : ℝ,0<Cl ∧ ∀ᶠ n : ℕ in atTop,∀U : ℝ,0 ≤ U → U ≤ Real.sqrt (highDegreeH k β Cl n) →
      (1-1/(k-1))*U+highDegreeDriftCost k β Cl n*roundingSlack (highDegreeT k β Cl n) ≤
        ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k (highDegreeD k β Cl n))
          (Real.sqrt (highDegreeH k β Cl n-U^2)) := by
  obtain ⟨B,Bden,S,R,hB0,hBden0,hS0,hR0,hBounds⟩ := highDegree_parameter_bounds k β hk hβ hreg
  have hp := highDegreeRate_properties k β hk hβ hreg
  have hK : 0<2+k*β := by
    have hk0 : 0<k := by linarith
    positivity
  let a := highDegreeRate k β
  let Cl := a*(R*(Bden*S)/2+40*B)/(2+k*β)+1
  have ha : 0<a := hp.1
  have hCl : 0<Cl := by dsimp [Cl]; positivity
  have hClLarge : R*(Bden*S)/2+40*B ≤ Cl*(2+k*β)/a := by
    have heq : Cl*(2+k*β)/a=R*(Bden*S)/2+40*B+(2+k*β)/a := by
      dsimp [Cl]
      field_simp
      <;> ring
    rw [heq]
    linarith [div_pos hK ha]
  refine ⟨Cl,hCl,?_⟩
  filter_upwards [hBounds Cl,highDegree_excess_ratio_bounds_eventually k β Cl hp.1,
    highDegree_eventually_regime k β Cl hk hβ hreg] with n hb hr hReg
  let t := highDegreeT k β Cl n
  let w := roundingSlack t
  have ht0 : 0<t := lt_trans (Real.exp_pos 1) hReg.2.2.1
  have hw : 0<w := hr.1
  have hT2 : t^2=highDegreeSquare k β Cl n := Real.sq_sqrt hReg.2.2.2.le
  have hD : highDegreeD k β Cl n=2*β*Real.log (n:ℝ)/t^2 := by rw [hT2]; rfl
  have hH : highDegreeH k β Cl n=2*Real.log (n:ℝ)/t^2+40*w := by
    unfold highDegreeH highDegreeH0
    rw [hT2]
  have hscale : t^2=2*((k-2)*β/(2+k*β))*Real.log (n:ℝ)+2*Cl*Real.log (numLevels n:ℝ) := hT2
  have hraw := ordinary_drift_from_scale k β Cl (Real.log (n:ℝ)) (Real.log (numLevels n:ℝ)) t w a B Bden S R
    hk hK hCl.le ha ht0 hw hscale hr.2.1 hr.2.2
    (by rw [← hD]; exact hb.1) (by rw [← hD]; exact hReg.1)
    (by rw [← hH]; exact hReg.2.1) hR0.le (by rw [← hD]; exact hb.2.1)
    (by change gapRootSum k (2*β*Real.log (n:ℝ)/t^2) (2*Real.log (n:ℝ)/t^2+40*w) ≤ S
        rw [← hD,← hH]
        exact hb.2.2.1) hClLarge
  rw [← hD,← hH] at hraw
  intro U hU hUH
  have h := hraw U hU hUH
  have hcost := mul_le_mul_of_nonneg_right hb.2.2.2 hw.le
  have hc : (1-1/(k-1))*U+highDegreeDriftCost k β Cl n*w ≤ (1-1/(k-1))*U+R*w := add_le_add_right hcost _
  exact hc.trans h

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverLiftingBound -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def DriftCondition (k D H w t : ℝ) : Prop :=
  ∀s : ℝ,0 ≤ s → s ≤ Real.sqrt H →
    (1-1/(k-1))*s+(((1+1/(k-1))/cA k)*((20*cA k+1)*
      (1+(Real.sqrt H/ordinaryNu k D-1)/(D+1)))+40)*w ≤
      ((1+1/(k-1))/cA k)*thresholdPsi (cA k) (ordinaryNu k D) (Real.sqrt (H-s^2))

theorem ordinary_cover_lifting_bound :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀k D H U q w t : ℝ,2<k → (cA k)^2<D → 1<H → 0<U →
      0<t → 0 ≤ w → w=roundingSlack t → t₀ ≤ t → DriftCondition k D H w t →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,OrdinaryVectorColoring G v k →
      ∀F W : Finset (Fin n),W⊆F → ∀r : Fin n,
      IsCover (W.image (uvec v r)) (U*t) q →
      (∀x∈W,pLocal G v F x ≤ Real.exp (-(t^2/2))) →
      (∀x∈W,((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2)) →
      IsCover ((neighborUnion G F W).image (uvec v r)) ((U+40*w)*t)
        (q-(W.card:ℝ)*((1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(H*t^2/2)))) := by
  classical
  obtain ⟨t₀,ht₀,hVertex⟩ := ordinary_cover_one_vertex_bound
  refine ⟨t₀,ht₀,?_⟩
  intro k D H U q w t hk hD hH hU ht hw hwt htt hDrift n d G v hv F W hWF r hCover hp hcard
  apply finite_cover_lifting G (uvec v r) F W (U*t) ((U+40*w)*t) q _ hCover
  intro x hx
  by_cases hxpos : 0<‖uvec v r x‖
  · exact hVertex k D H U w t hk hD hH hU ht hw hwt htt hDrift n d G v hv F r x (hWF hx) hxpos
      (hp x hx) (hcard x hx)
  · have hn0 : ‖uvec v r x‖=0 := le_antisymm (le_of_not_gt hxpos) (norm_nonneg _)
    have hux : uvec v r x=0 := norm_eq_zero.mp hn0
    have he : {g : Space d | ⟪g,uvec v r x⟫ ≤ -(U*t) ∧
        ∀y∈nbr G F x,⟪g,uvec v r y⟫<(U+40*w)*t}=∅ := by
      ext g
      constructor
      · intro hg
        have h := hg.1
        rw [hux,inner_zero_right] at h
        nlinarith only [h,mul_pos hU ht]
      · intro hg
        exact hg.elim
    rw [he]
    simp only [gaussProb,measureReal_empty]
    positivity

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverLoss -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_cover_loss_eventually (B : ℝ) :
    ∀ᶠ t : ℝ in atTop,∀H : ℝ,0 ≤ H → H ≤ B →
      (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-20*Real.log t) ≤ (t^18)⁻¹ := by
  let C := Real.sqrt B/Real.sqrt (2*Real.pi)
  have hC : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  filter_upwards [eventually_ge_atTop (max (2:ℝ) (2*C))] with t ht H hH hHB
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have htC : 2*C ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0<t := by linarith
  have hcoef : 1+Real.sqrt H*t/Real.sqrt (2*Real.pi) ≤ t^2 := by
    rw [← div_mul_eq_mul_div]
    have hs := Real.sqrt_le_sqrt hHB
    have hsC : Real.sqrt H/Real.sqrt (2*Real.pi) ≤ C := div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_right hsC ht0.le
    have hct := mul_nonneg (show 0 ≤ t-2*C by linarith) ht0.le
    have h1 : 2 ≤ t^2 := by nlinarith only [ht2,sq_nonneg (t-1)]
    nlinarith only [hm,hct,h1]
  have hExp : Real.exp (-20*Real.log t)=(t^20)⁻¹ := by
    rw [show -20*Real.log t=-(20*Real.log t) by ring,Real.exp_neg]
    rw [show 20*Real.log t=(20:ℕ)*Real.log t by norm_num,Real.exp_nat_mul,Real.exp_log ht0]
  rw [hExp]
  apply (mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr (pow_nonneg ht0.le 20))).trans_eq
  field_simp
  <;> ring

theorem finite_cover_loss_bound (N H H₀ t w : ℝ) (hN : 0 ≤ N) (ht : 0<t)
    (hH : 0 ≤ H) (hCard : N ≤ Real.exp (H₀*t^2/2))
    (hGap : H-H₀=40*w) (hSlack : w*t^2=Real.log t) :
    N*((1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(H*t^2/2))) ≤
      (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-20*Real.log t) := by
  have hC : 0 ≤ 1+Real.sqrt H*t/Real.sqrt (2*Real.pi) := by positivity
  have h := mul_le_mul_of_nonneg_right hCard
    (mul_nonneg hC (Real.exp_pos (-(H*t^2/2))).le)
  apply h.trans_eq
  calc
    Real.exp (H₀*t^2/2)*((1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(H*t^2/2)))=
        (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (H₀*t^2/2-H*t^2/2) := by
      rw [Real.exp_sub,Real.exp_neg]
      ring
    _ = _ := by
      congr 1
      congr 1
      nlinarith only [congrArg (fun z : ℝ => z*t^2) hGap,hSlack]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverDegree -/

set_option autoImplicit false
set_option maxHeartbeats 900000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegree_exp_degree (k β Cl : ℝ) (n : ℕ) (hn : 0<n)
    (hs : 0<highDegreeSquare k β Cl n) :
    Real.exp (highDegreeD k β Cl n*(highDegreeT k β Cl n)^2/2)=(n:ℝ)^β := by
  have ht : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hs.le
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  rw [ht,highDegreeD,Real.rpow_def_of_pos hn0]
  congr 1
  field_simp
  <;> ring

theorem highDegree_exp_population (k β Cl : ℝ) (n : ℕ) (hn : 0<n)
    (hs : 0<highDegreeSquare k β Cl n) :
    Real.exp (highDegreeH0 k β Cl n*(highDegreeT k β Cl n)^2/2)=(n:ℝ) := by
  have ht : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hs.le
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  have he : highDegreeH0 k β Cl n*(highDegreeT k β Cl n)^2/2=Real.log (n:ℝ) := by
    rw [ht,highDegreeH0]
    field_simp
  rw [he,Real.exp_log hn0]

theorem nbr_card_le_maxDegOn_univ {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Fin n)) (x : Fin n) :
    ((nbr G F x).card:ℝ) ≤ (maxDegOn G Finset.univ:ℝ) := by
  classical
  have hsub : nbr G F x⊆nbr G Finset.univ x := by
    intro y hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ y,(Finset.mem_filter.mp hy).2⟩
  have hcard : (nbr G F x).card ≤ (nbr G Finset.univ x).card := Finset.card_le_card hsub
  have hmax : (nbr G Finset.univ x).card ≤ maxDegOn G Finset.univ :=
    Finset.le_sup (f:=fun y => (nbr G Finset.univ y).card) (Finset.mem_univ x)
  exact_mod_cast hcard.trans hmax

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverLifting -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_cover_lifting_eventually (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    ∃Cl : ℝ,0<Cl ∧ ∀ᶠ n : ℕ in atTop,∀d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
      OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
      ∀F W : Finset (Fin n),W⊆F → ∀r : Fin n,∀U q : ℝ,0<U →
      IsCover (W.image (uvec v r)) (U*highDegreeT k β Cl n) q →
      (∀x∈W,pLocal G v F x ≤ Real.exp (-((highDegreeT k β Cl n)^2/2))) →
      IsCover ((neighborUnion G F W).image (uvec v r))
        ((U+40*roundingSlack (highDegreeT k β Cl n))*highDegreeT k β Cl n)
        (q-((highDegreeT k β Cl n)^18)⁻¹) := by
  classical
  obtain ⟨Cl,hCl,hDrift⟩ := ordinary_drift_eventually k β hk hβ hreg
  obtain ⟨t₀,ht₀,hLifting⟩ := ordinary_cover_lifting_bound
  have hRate := highDegreeRate_properties k β hk hβ hreg
  let B := 1/highDegreeRate k β+1
  have hHupper : ∀ᶠ n : ℕ in atTop,highDegreeH k β Cl n ≤ B :=
    ((highDegreeH_tendsto k β Cl hRate.1).eventually_lt_const (show 1/highDegreeRate k β<B by dsimp [B]; linarith)).mono fun _ h => h.le
  have hLoss := (highDegreeT_tendsto_atTop k β Cl hRate.1).eventually (gaussian_cover_loss_eventually B)
  refine ⟨Cl,hCl,?_⟩
  filter_upwards [hDrift,highDegree_eventually_regime k β Cl hk hβ hreg,
    highDegree_excess_ratio_bounds_eventually k β Cl hRate.1,
    (highDegreeT_tendsto_atTop k β Cl hRate.1).eventually_ge_atTop t₀,
    hHupper,hLoss,eventually_ge_atTop (1:ℕ)] with n hDrift hRegime hRat htt hHB hLoss hn
  intro d G v hv hdeg F W hWF r U q hU hCover hp
  let t := highDegreeT k β Cl n
  let w := roundingSlack t
  let D := highDegreeD k β Cl n
  let H := highDegreeH k β Cl n
  let H₀ := highDegreeH0 k β Cl n
  have ht : 0<t := (Real.exp_pos 1).trans hRegime.2.2.1
  have hw : 0<w := hRat.1
  have hH0 : 0 ≤ H := by linarith only [hRegime.2.1]
  have hCondition : DriftCondition k D H w t := by
    intro s hs hsh
    have h := hDrift s hs hsh
    simpa only [highDegreeDriftCost,highDegreeTheta,mul_assoc] using h
  have hcard : ∀x∈W,((nbr G F x).card:ℝ) ≤ Real.exp (D*t^2/2) := by
    intro x hx
    rw [highDegree_exp_degree k β Cl n (by omega) hRegime.2.2.2]
    exact (nbr_card_le_maxDegOn_univ G F x).trans hdeg
  have hLift := hLifting k D H U q w t hk hRegime.1 hRegime.2.1 hU ht hw.le rfl htt hCondition
    n d G v hv F W hWF r hCover hp hcard
  have hPopulation : (W.card:ℝ) ≤ Real.exp (H₀*t^2/2) := by
    rw [highDegree_exp_population k β Cl n (by omega) hRegime.2.2.2]
    have hcardNat : W.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ W
    exact_mod_cast hcardNat
  have hGap : H-H₀=40*w := by dsimp [H,H₀,w,t,highDegreeH]; ring
  have hSlack : w*t^2=Real.log t := div_mul_cancel₀ _ (pow_ne_zero 2 ht.ne')
  have hTotal := finite_cover_loss_bound (W.card:ℝ) H H₀ t w (Nat.cast_nonneg _) ht hH0 hPopulation hGap hSlack
  have hFinal := hTotal.trans (hLoss H hH0 hHB)
  unfold IsCover at hLift ⊢
  exact (sub_le_sub_left hFinal q).trans hLift

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverIterate -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def backwardCoverSets {n : ℕ} (G : SimpleGraph (Fin n)) (C : ℕ→Finset (Fin n))
    (W₀ : Finset (Fin n)) (m : ℕ) : ℕ→Finset (Fin n)
  | 0 => W₀
  | j+1 => neighborUnion G (C (m-(j+1))) (backwardCoverSets G C W₀ m j)

theorem neighborUnion_subset {n : ℕ} (G : SimpleGraph (Fin n)) (F W : Finset (Fin n)) :
    neighborUnion G F W⊆F := by
  classical
  intro y hy
  obtain ⟨x,hx,hxy⟩ := Finset.mem_biUnion.mp hy
  exact (Finset.mem_filter.mp hxy).1

theorem backwardCoverSets_subset {n : ℕ} (G : SimpleGraph (Fin n)) (C : ℕ→Finset (Fin n))
    (W₀ : Finset (Fin n)) (m : ℕ) (hW₀ : W₀⊆C m) :
    ∀j : ℕ,backwardCoverSets G C W₀ m j⊆C (m-j) := by
  intro j
  cases j with
  | zero => simpa only [backwardCoverSets,Nat.sub_zero] using hW₀
  | succ j => exact neighborUnion_subset G _ _

theorem backward_cover_iteration {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (r : Fin n) (C : ℕ→Finset (Fin n)) (W₀ : Finset (Fin n)) (m : ℕ)
    (hW₀ : W₀⊆C m) (hC : ∀j,C (j+1)⊆C j)
    (p U₀ w t q ε : ℝ) (hU₀ : 0<U₀) (hw : 0 ≤ w)
    (hCover : IsCover (W₀.image (uvec v r)) (U₀*t) q)
    (hP : ∀j,1 ≤ j → j ≤ m → ∀x∈C j,pLocal G v (C (j-1)) x ≤ p)
    (hLift : ∀F W : Finset (Fin n),W⊆F → ∀U q : ℝ,0<U →
      IsCover (W.image (uvec v r)) (U*t) q → (∀x∈W,pLocal G v F x ≤ p) →
      IsCover ((neighborUnion G F W).image (uvec v r)) ((U+40*w)*t) (q-ε)) :
    ∀j : ℕ,j ≤ m → IsCover ((backwardCoverSets G C W₀ m j).image (uvec v r))
      ((U₀+40*w*(j:ℝ))*t) (q-(j:ℝ)*ε) := by
  intro j
  induction j with
  | zero =>
    intro _
    simpa only [backwardCoverSets,Nat.cast_zero,mul_zero,zero_mul,add_zero,sub_zero] using hCover
  | succ j ih =>
    intro hj
    have hjm : j ≤ m := by omega
    have hCur := ih hjm
    have hSub := backwardCoverSets_subset G C W₀ m hW₀ j
    have hCore : C (m-j)⊆C (m-(j+1)) := by
      have heq : m-j=(m-(j+1))+1 := by omega
      rw [heq]
      exact hC _
    have hP' : ∀x∈backwardCoverSets G C W₀ m j,pLocal G v (C (m-(j+1))) x ≤ p := by
      intro x hx
      have h := hP (m-j) (by omega) (by omega) x (hSub hx)
      simpa only [show m-j-1=m-(j+1) by omega] using h
    have hU : 0<U₀+40*w*(j:ℝ) := by positivity
    have h := hLift (C (m-(j+1))) (backwardCoverSets G C W₀ m j) (hSub.trans hCore)
      (U₀+40*w*(j:ℝ)) (q-(j:ℝ)*ε) hU hCur hP'
    change IsCover ((neighborUnion G (C (m-(j+1))) (backwardCoverSets G C W₀ m j)).image (uvec v r))
      ((U₀+40*w*((j+1:ℕ):ℝ))*t) (q-((j+1:ℕ):ℝ)*ε)
    have hUeq : (U₀+40*w*((j+1:ℕ):ℝ))*t=(U₀+40*w*(j:ℝ)+40*w)*t := by
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    have hqeq : q-((j+1:ℕ):ℝ)*ε=q-(j:ℝ)*ε-ε := by
      simp only [Nat.cast_add,Nat.cast_one]
      ring
    rw [hUeq,hqeq]
    exact h

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoverUpper -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_inner_upper_ge {d : ℕ} (w : Space d) (hw : ‖w‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    gaussProb {g : Space d | a ≤ ⟪g,w⟫} ≤ Real.exp (-(a^2/2)) := by
  have h := (gaussian_inner_subgaussian_one w hw).measure_ge_le ha
  simpa only [gaussProb,real_inner_comm,NNReal.coe_one,mul_one,neg_div] using h

theorem gaussian_finite_cover_upper {n d : ℕ} (u : Fin n→Space d) (W : Finset (Fin n))
    (hu : ∀x∈W,‖u x‖ ≤ 1) (a : ℝ) (ha : 0 ≤ a) :
    gaussProb {g : Space d | ∃x∈W,a ≤ ⟪g,u x⟫} ≤ (W.card:ℝ)*Real.exp (-(a^2/2)) := by
  classical
  have heq : {g : Space d | ∃x∈W,a ≤ ⟪g,u x⟫}=⋃x∈W,{g : Space d | a ≤ ⟪g,u x⟫} := by
    ext g
    simp only [Set.mem_setOf_eq,Set.mem_iUnion]
    aesop
  unfold gaussProb
  rw [heq]
  calc
    _ ≤ ∑x∈W,(stdGaussian (Space d)).real {g : Space d | a ≤ ⟪g,u x⟫} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑_x∈W,Real.exp (-(a^2/2)) := Finset.sum_le_sum (fun x hx => gaussian_inner_upper_ge (u x) (hu x hx) a ha)
    _ = _ := by simp

theorem cover_mono_threshold {d : ℕ} (X : Finset (Space d)) (a b q : ℝ) (hab : a ≤ b)
    (hCover : IsCover X b q) : IsCover X a q := by
  unfold IsCover at hCover ⊢
  apply hCover.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨x,hx,hxg⟩ := hg
  exact ⟨x,hx,hab.trans hxg⟩

theorem cover_population_upper {n d : ℕ} (u : Fin n→Space d) (W : Finset (Fin n))
    (hu : ∀x,‖u x‖ ≤ 1) (a q : ℝ) (ha : 0 ≤ a) (hCover : IsCover (W.image u) a q) :
    q ≤ (n:ℝ)*Real.exp (-(a^2/2)) := by
  have hC : q ≤ gaussProb {g : Space d | ∃x∈W,a ≤ ⟪g,u x⟫} := by
    simpa only [IsCover,Finset.mem_image,exists_exists_and_eq_and] using hCover
  have hUpper := gaussian_finite_cover_upper u W (fun x _ => hu x) a ha
  have hCard : (W.card:ℝ) ≤ n := by
    have h : W.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ W
    exact_mod_cast h
  exact (hC.trans hUpper).trans (mul_le_mul_of_nonneg_right hCard (Real.exp_pos _).le)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxIterationLimits -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem levels_over_highDegreeSquare_tendsto (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => (numLevels n:ℝ)/highDegreeSquare k β Cl n) atTop (𝓝 (1/(2*highDegreeRate k β))) := by
  have h := numLevels_over_log_tendsto.mul (log_over_highDegreeSquare_tendsto k β Cl ha)
  have heq : (fun n : ℕ => ((numLevels n:ℝ)/Real.log (n:ℝ))*(Real.log (n:ℝ)/highDegreeSquare k β Cl n)) =ᶠ[atTop]
      (fun n : ℕ => (numLevels n:ℝ)/highDegreeSquare k β Cl n) := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
    field_simp
  simpa only [one_mul] using h.congr' heq

theorem iteration_cover_loss_tendsto_zero (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => (numLevels n:ℝ)*((highDegreeT k β Cl n)^18)⁻¹) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((highDegreeSquare k β Cl n)^8)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : (8:ℕ)≠0)).comp (highDegreeSquare_tendsto_atTop k β Cl ha))
  have h := (levels_over_highDegreeSquare_tendsto k β Cl ha).mul hi
  have heq : (fun n : ℕ => ((numLevels n:ℝ)/highDegreeSquare k β Cl n)*((highDegreeSquare k β Cl n)^8)⁻¹) =ᶠ[atTop]
      (fun n : ℕ => (numLevels n:ℝ)*((highDegreeT k β Cl n)^18)⁻¹) := by
    filter_upwards [(highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0] with n hn
    have hT : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hn.le
    have hT18 : (highDegreeT k β Cl n)^18=(highDegreeSquare k β Cl n)^9 := by
      rw [← hT]
      ring
    rw [hT18]
    field_simp
    <;> ring
  simpa only [mul_zero] using h.congr' heq

theorem iteration_slack_growth (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => roundingSlack (highDegreeT k β Cl n)*((numLevels n-1:ℕ):ℝ)) atTop atTop := by
  have hInv : Tendsto (fun n : ℕ => 1/highDegreeSquare k β Cl n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (highDegreeSquare_tendsto_atTop k β Cl ha)
  have hRatio : Tendsto (fun n : ℕ => ((numLevels n:ℝ)-1)/highDegreeSquare k β Cl n)
      atTop (𝓝 (1/(2*highDegreeRate k β))) := by
    have h := (levels_over_highDegreeSquare_tendsto k β Cl ha).sub hInv
    convert h using 1
    · ext n
      ring
    · ring
  have hRatioLower := hRatio.eventually_const_lt
    (show 1/(4*highDegreeRate k β)<1/(2*highDegreeRate k β) by
      apply div_lt_div_of_pos_left zero_lt_one (by positivity)
      linarith)
  have hLog : Tendsto (fun n : ℕ => Real.log (highDegreeT k β Cl n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (highDegreeT_tendsto_atTop k β Cl ha)
  have hLower : Tendsto (fun n : ℕ => (1/(4*highDegreeRate k β))*Real.log (highDegreeT k β Cl n)) atTop atTop :=
    hLog.const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' atTop _ hLower
  filter_upwards [hRatioLower,(highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0,
    (highDegreeT_tendsto_atTop k β Cl ha).eventually_gt_atTop 1,
    numLevels_real_tendsto_atTop.eventually_ge_atTop 1] with n hr hs ht hn
  have hNat : 1 ≤ numLevels n := by exact_mod_cast hn
  have hT : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hs.le
  have heq : roundingSlack (highDegreeT k β Cl n)*((numLevels n-1:ℕ):ℝ)=
      (((numLevels n:ℝ)-1)/highDegreeSquare k β Cl n)*Real.log (highDegreeT k β Cl n) := by
    rw [Nat.cast_sub hNat,Nat.cast_one]
    unfold roundingSlack
    rw [hT]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right hr.le (Real.log_nonneg ht.le)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOrdinaryCover -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ordinary_edge_uvec_eq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (r y : Fin n) (hry : G.Adj r y) :
    uvec v r y=((1-⟪v r,v y⟫)/cA k) • ordinaryResidual k v r y := by
  rw [uvec,rho]
  conv_lhs => lhs; rw [ordinary_edge_decomposition G v k hk hv r y hry]
  module

theorem ordinary_initial_cover {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k : ℝ) (hk : 2 < k) (hv : OrdinaryVectorColoring G v k)
    (F : Finset (Fin n)) (r : Fin n) (hr : r∈F) (t : ℝ) (ht : 2 ≤ t)
    (hp : pLocal G v F r ≤ Real.exp (-(t^2/2))) :
    IsCover ((nbr G F r).image (uvec v r)) ((1+1/(k-1))/Real.sqrt 2*t)
      (1-millsConstant⁻¹*t*Real.exp (-(t^2/4))) := by
  classical
  let a := cA k/Real.sqrt 2*t
  let A : Set (Space d) := {g | ordinaryNbrMax G v k F r g≤(a:WithBot ℝ)}
  have hc := cA_pos k hk
  have hs : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hat : a/cA k=t/Real.sqrt 2 := by dsimp [a]; field_simp
  have hL := (ordinary_local_probability G v k hk hv F r hr a).2
  have hB : gaussProb A ≤ Real.exp (-(t^2/2))/PhiTail (t/Real.sqrt 2) := by
    rw [hat] at hL
    exact hL.trans (div_le_div_of_nonneg_right hp (phiTail_nonneg _))
  have hB' : gaussProb A ≤ millsConstant⁻¹*t*Real.exp (-(t^2/4)) :=
    hB.trans (gaussian_tail_ratio_bound t ht)
  have hHigh : 1-millsConstant⁻¹*t*Real.exp (-(t^2/4)) ≤ gaussProb Aᶜ := by
    unfold gaussProb at hB' ⊢
    rw [probReal_compl_eq_one_sub (measurableSet_ordinaryNbrMax_le G v k F r a)]
    linarith
  have hsub : Aᶜ ⊆ {g : Space d | ∃z∈(nbr G F r).image (uvec v r),
      (1+1/(k-1))/Real.sqrt 2*t ≤ ⟪g,z⟫} := by
    intro g hg
    have hg' : (a:WithBot ℝ)<ordinaryNbrMax G v k F r g := lt_of_not_ge hg
    have hex : ∃y∈nbr G F r,a<⟪g,ordinaryResidual k v r y⟫ := by
      simpa only [ordinaryNbrMax,Finset.lt_sup_iff,WithBot.coe_lt_coe] using hg'
    obtain ⟨y,hy,hys⟩ := hex
    have hry := (Finset.mem_filter.mp hy).2
    have hip := hv.2 r y hry
    have hcoef : 0 ≤ (1-⟪v r,v y⟫)/cA k := by
      apply div_nonneg _ hc.le
      have hi := ordinary_edge_inner_neg G v k hk hv r y hry
      linarith
    refine ⟨uvec v r y,Finset.mem_image.mpr ⟨y,hy,rfl⟩,?_⟩
    rw [ordinary_edge_uvec_eq G v k hk hv r y hry,real_inner_smul_right]
    have hidentity : ((1-⟪v r,v y⟫)/cA k)*a=((1-⟪v r,v y⟫)/Real.sqrt 2)*t := by
      dsimp [a]
      field_simp
    have hm := mul_le_mul_of_nonneg_left hys.le hcoef
    rw [hidentity] at hm
    have hden : (1+1/(k-1))/Real.sqrt 2 ≤ (1-⟪v r,v y⟫)/Real.sqrt 2 :=
      div_le_div_of_nonneg_right (by linarith) hs.le
    exact (mul_le_mul_of_nonneg_right hden (by linarith : 0 ≤ t)).trans hm
  exact hHigh.trans (measureReal_mono hsub)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxInitialErrorLimits -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegree_initial_error_tendsto_zero (k β Cl K : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => K*highDegreeT k β Cl n*Real.exp (-((highDegreeT k β Cl n)^2/4))) atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2:ℝ) (1/4:ℝ) (by norm_num)
  have h := (hbase.comp (highDegreeSquare_tendsto_atTop k β Cl ha)).const_mul K
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [(highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0] with n hn
  change K*((highDegreeSquare k β Cl n)^(1/2:ℝ)*Real.exp (-(1/4:ℝ)*highDegreeSquare k β Cl n))=
    K*highDegreeT k β Cl n*Real.exp (-((highDegreeT k β Cl n)^2/4))
  have ht : (highDegreeT k β Cl n)^2=highDegreeSquare k β Cl n := Real.sq_sqrt hn.le
  rw [ht,highDegreeT,Real.sqrt_eq_rpow]
  have he : -(1/4:ℝ)*highDegreeSquare k β Cl n=-(highDegreeSquare k β Cl n/4) := by ring
  rw [he]
  ring

theorem iteration_sub_cover_loss_tendsto_zero (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => ((numLevels n-1:ℕ):ℝ)*((highDegreeT k β Cl n)^18)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) _ (iteration_cover_loss_tendsto_zero k β Cl ha)
  intro n
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.sub_le (numLevels n) 1

theorem highDegree_final_cover_quality (k β Cl K : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => 1-K*highDegreeT k β Cl n*Real.exp (-((highDegreeT k β Cl n)^2/4))-
      ((numLevels n-1:ℕ):ℝ)*((highDegreeT k β Cl n)^18)⁻¹) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x:=(1:ℝ))).sub (highDegree_initial_error_tendsto_zero k β Cl K ha)).sub
    (iteration_sub_cover_loss_tendsto_zero k β Cl ha)
  simpa only [sub_zero] using h

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLogLinear -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem log_linear_ratio_tendsto (b p : ℝ) :
    Tendsto (fun n : ℕ => (b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ))/Real.log (n:ℝ)) atTop (𝓝 b) := by
  have h := (log_numLevels_over_log_tendsto_zero.const_mul p).const_add b
  have heq : (fun n : ℕ => b+p*(Real.log (numLevels n:ℝ)/Real.log (n:ℝ))) =ᶠ[atTop]
      (fun n : ℕ => (b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ))/Real.log (n:ℝ)) := by
    filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hn
    field_simp
    <;> ring
  simpa only [mul_zero,add_zero] using h.congr' heq

theorem log_linear_tendsto_atBot (b p : ℝ) (hb : b<0) :
    Tendsto (fun n : ℕ => b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ)) atTop atBot := by
  have hratio := (log_linear_ratio_tendsto b p).eventually_lt_const (show b<b/2 by linarith)
  have hUpper : ∀ᶠ n : ℕ in atTop,b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ) ≤ (b/2)*Real.log (n:ℝ) := by
    filter_upwards [hratio,log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hr hn
    exact ((div_lt_iff₀ hn).mp hr).le
  exact tendsto_atBot_mono' atTop hUpper (log_nat_tendsto_atTop.const_mul_atTop_of_neg (by linarith : b/2<0))

theorem log_linear_tendsto_atTop (b p : ℝ) (hb : 0<b) :
    Tendsto (fun n : ℕ => b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ)) atTop atTop := by
  have hratio := (log_linear_ratio_tendsto b p).eventually_const_lt (show b/2<b by linarith)
  have hLower : ∀ᶠ n : ℕ in atTop,(b/2)*Real.log (n:ℝ) ≤ b*Real.log (n:ℝ)+p*Real.log (numLevels n:ℝ) := by
    filter_upwards [hratio,log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hr hn
    exact ((lt_div_iff₀ hn).mp hr).le
  exact tendsto_atTop_mono' atTop hLower (log_nat_tendsto_atTop.const_mul_atTop (by linarith : 0<b/2))

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxDeltaLimits -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegree_delta_pos (k β Cl : ℝ) (n : ℕ) (hreg : (k-2)/k<β) (hn : 2 ≤ n) :
    0<deltaA k β Cl n := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hell : 0<(numLevels n:ℝ) := (Real.log_pos hn1).trans_le (Nat.le_ceil _)
  rw [deltaA,if_neg (not_le_of_gt hreg)]
  exact mul_pos (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hell _)

theorem highDegree_delta_eq_exp (k β Cl : ℝ) (n : ℕ) (hreg : (k-2)/k<β) (hn : 2 ≤ n) :
    deltaA k β Cl n=Real.exp (-(highDegreeSquare k β Cl n/2)) := by
  have hδ := highDegree_delta_pos k β Cl n hreg hn
  have hs := highDegreeSquare_eq_neg_log_deltaA k β Cl n hreg hn
  have he : -(highDegreeSquare k β Cl n/2)=Real.log (deltaA k β Cl n) := by linarith only [hs]
  rw [he,Real.exp_log hδ]

theorem highDegree_delta_tendsto_zero (k β Cl : ℝ) (ha : 0<highDegreeRate k β) (hreg : (k-2)/k<β) :
    Tendsto (deltaA k β Cl) atTop (𝓝 0) := by
  have harg := (highDegreeSquare_tendsto_atTop k β Cl ha).const_mul_atTop_of_neg (by norm_num : (-1/2:ℝ)<0)
  have h := Real.tendsto_exp_atBot.comp harg
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  change Real.exp ((-1/2:ℝ)*highDegreeSquare k β Cl n)=deltaA k β Cl n
  rw [highDegree_delta_eq_exp k β Cl n hreg hn]
  congr 1
  ring

theorem highDegree_core_loss_term_tendsto_zero (k β Cl : ℝ) (ha : 0<highDegreeRate k β)
    (ha1 : highDegreeRate k β<1) (hreg : (k-2)/k<β) :
    Tendsto (fun n : ℕ => (numLevels n:ℝ)/((n:ℝ)*deltaA k β Cl n)) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp
    (log_linear_tendsto_atBot (highDegreeRate k β-1) (Cl+1) (by linarith))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hL : 0<(numLevels n:ℝ) := (Real.log_pos hn1).trans_le (Nat.le_ceil _)
  change Real.exp ((highDegreeRate k β-1)*Real.log (n:ℝ)+(Cl+1)*Real.log (numLevels n:ℝ))=_
  symm
  calc
    (numLevels n:ℝ)/((n:ℝ)*deltaA k β Cl n)=
        Real.exp (Real.log (numLevels n:ℝ))/(Real.exp (Real.log (n:ℝ))*Real.exp (-(highDegreeSquare k β Cl n/2))) := by
      rw [Real.exp_log hL,Real.exp_log hn0,← highDegree_delta_eq_exp k β Cl n hreg hn]
    _ = Real.exp (Real.log (numLevels n:ℝ)-Real.log (n:ℝ)+highDegreeSquare k β Cl n/2) := by
      rw [Real.exp_add,Real.exp_sub,Real.exp_neg]
      field_simp
    _ = _ := by
      congr 1
      unfold highDegreeSquare
      ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCoreBudget -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ceil_target_core_budget (N δ L T : ℝ) (hN : 0<N) (hδ : 0<δ) (hL : 1 ≤ L)
    (hT : T ≤ N*δ/(100*L^4)+1) (hSmall : 4*L<N*δ) : L*(2*T/δ)<N := by
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hL2 : L ≤ L^2 := by nlinarith only [mul_nonneg hL0.le (sub_nonneg.mpr hL)]
  have hL2one : 1 ≤ L^2 := hL.trans hL2
  have hL4 : L^2 ≤ L^4 := by nlinarith only [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL2one)]
  have hPow : L ≤ L^4 := hL2.trans hL4
  have hWeak : T ≤ N*δ/(100*L)+1 := hT.trans (add_le_add_left
    (div_le_div_of_nonneg_left (mul_pos hN hδ).le (by positivity) (by nlinarith only [hPow])) 1)
  have hMul := mul_le_mul_of_nonneg_left hWeak (show 0 ≤ 2*L by positivity)
  have heq : (2*L)*(N*δ/(100*L)+1)=N*δ/50+2*L := by field_simp <;> ring
  rw [heq] at hMul
  have hNumer : 2*L*T<N*δ := by nlinarith only [hMul,hSmall,mul_pos hN hδ]
  have heq' : L*(2*T/δ)=(2*L*T)/δ := by ring
  rw [heq']
  exact (div_lt_iff₀ hδ).mpr hNumer

theorem highDegree_core_budget_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β)
    (ha1 : highDegreeRate k β<1) (hreg : (k-2)/k<β) :
    ∀ᶠ n : ℕ in atTop,(numLevels n:ℝ)*(2*(targetA k β Cl n:ℝ)/deltaA k β Cl n)<n := by
  have hSmall := (highDegree_core_loss_term_tendsto_zero k β Cl ha ha1 hreg).eventually_lt_const
    (by norm_num : (0:ℝ)<1/4)
  filter_upwards [hSmall,eventually_ge_atTop (2:ℕ),numLevels_real_tendsto_atTop.eventually_ge_atTop 1] with n hSmall hn hL
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hδ := highDegree_delta_pos k β Cl n hreg hn
  have hND : 0<(n:ℝ)*deltaA k β Cl n := mul_pos hn0 hδ
  have hSmall' : 4*(numLevels n:ℝ)<(n:ℝ)*deltaA k β Cl n := by
    have h := (div_lt_iff₀ hND).mp hSmall
    nlinarith only [h]
  apply ceil_target_core_budget (n:ℝ) (deltaA k β Cl n) (numLevels n:ℝ) (targetA k β Cl n:ℝ) hn0 hδ hL _ hSmall'
  rw [targetA,if_neg (not_le_of_gt hreg)]
  exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (n:ℝ)*deltaA k β Cl n/(100*(numLevels n:ℝ)^4))).le

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxAdaptive -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurable_freq {n R : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : Fin R→Ω→Finset (Fin n)) (hI : ∀i,Measurable (I i)) (x : Fin n) :
    Measurable (fun ω => freq (fun i => I i ω) x) := by
  classical
  simp only [freq_eq_indicator_sum]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (measurableSet_setOfPred.mpr ((measurable_finset_mem x).comp (hI i)))
    measurable_const measurable_const

theorem measurable_sampledAt_fixed {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (F : Finset (Fin n)) (j : ℕ) (i : Fin R) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => sampledAt G v ω F j i) := by
  classical
  unfold sampledAt
  split_ifs with h
  · exact (measurable_localMax G v F).comp
      (measurable_pi_apply ((⟨j,h⟩:Fin (numLevels n)),i))
  · exact measurable_const

theorem measurable_cores {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => cores G v δ ω j) := by
  classical
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    let U : Finset (Fin n)×(Fin (numLevels n)×Fin R→Space d)→Finset (Fin n) :=
      fun p => p.1.filter (fun x => freq (sampledAt G v p.2 p.1 j) x<δ/2)
    have hU : Measurable U := by
      apply measurable_from_prod_countable_right
      intro F
      rw [measurable_finset_iff]
      intro x
      simp only [U,Finset.mem_filter]
      apply Measurable.and measurable_const
      apply measurableSet_setOfPred.mp
      exact measurableSet_lt
        (measurable_freq (fun i ω => sampledAt G v ω F j i)
          (measurable_sampledAt_fixed G v F j) x) measurable_const
    change Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
      U (cores G v δ ω j,ω))
    exact hU.comp (ih.prodMk measurable_id)

theorem cores_congr_before {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω ω' : Fin (numLevels n)×Fin R→Space d)
    (j : ℕ) (hω : ∀p,p.1.val<j → ω p=ω' p) :
    cores G v δ ω j=cores G v δ ω' j := by
  classical
  induction j with
  | zero => rfl
  | succ j ih =>
    have hc := ih (fun p hp => hω p (by omega))
    have hs : sampledAt G v ω (cores G v δ ω' j) j=
        sampledAt G v ω' (cores G v δ ω' j) j := by
      funext i
      unfold sampledAt
      split_ifs with h
      · rw [hω (⟨j,h⟩,i) (by simp)]
      · rfl
    simp only [cores,hc,hs]

def pastIndices (n R j : ℕ) : Finset (Fin (numLevels n)×Fin R) :=
  Finset.univ.filter (fun p => p.1.val<j)

def rowIndices (n R : ℕ) (j : Fin (numLevels n)) : Finset (Fin (numLevels n)×Fin R) :=
  Finset.univ.filter (fun p => p.1=j)

def fillPast {n d R : ℕ} (j : ℕ) (z : ↥(pastIndices n R j)→Space d) :
    Fin (numLevels n)×Fin R→Space d :=
  fun p => if hp : p∈pastIndices n R j then z ⟨p,hp⟩ else 0

theorem fillPast_measurable {n d R : ℕ} (j : ℕ) :
    Measurable (fillPast (n:=n) (d:=d) (R:=R) j) := by
  classical
  apply measurable_pi_iff.mpr
  intro p
  unfold fillPast
  split_ifs with h
  · exact measurable_pi_apply (⟨p,h⟩:↥(pastIndices n R j))
  · exact measurable_const

theorem cores_fillPast {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d) (j : ℕ) :
    cores G v δ (fillPast j (fun p : ↥(pastIndices n R j) => ω p)) j=cores G v δ ω j := by
  classical
  apply cores_congr_before
  intro p hp
  simp [fillPast,pastIndices,hp]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxAdaptiveLaw -/

set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

instance instIsProbabilityMeasureTrialLaw (n d R : ℕ) : IsProbabilityMeasure (trialLaw n d R) := by
  unfold trialLaw
  infer_instance

theorem cores_independent_row {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : Fin (numLevels n)) :
    IndepFun (fun ω : Fin (numLevels n)×Fin R→Space d => cores G v δ ω j.val)
      (fun ω i => ω (j,i)) (trialLaw n d R) := by
  classical
  have hI : iIndepFun (fun p (ω : Fin (numLevels n)×Fin R→Space d) => ω p)
      (trialLaw n d R) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hST : Disjoint (pastIndices n R j.val) (rowIndices n R j) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    simp only [pastIndices,rowIndices,Finset.mem_filter,Finset.mem_univ,true_and] at hp hq
    rw [hq] at hp
    exact (lt_irrefl _ hp)
  have h := iIndepFun.indepFun_finset (pastIndices n R j.val) (rowIndices n R j) hST hI
    (fun p => measurable_pi_apply p)
  let C : (↥(pastIndices n R j.val)→Space d)→Finset (Fin n) :=
    fun z => cores G v δ (fillPast j.val z) j.val
  let Y : (↥(rowIndices n R j)→Space d)→(Fin R→Space d) :=
    fun z i => z ⟨(j,i),by simp [rowIndices]⟩
  have hC : Measurable C := (measurable_cores G v δ j.val).comp (fillPast_measurable j.val)
  have hY : Measurable Y := by dsimp [Y]; fun_prop
  have hi := h.comp hC hY
  simpa only [C,Y,Function.comp_def,cores_fillPast] using hi

theorem trial_row_map {n d R : ℕ} (j : Fin (numLevels n)) :
    (trialLaw n d R).map (fun ω i => ω (j,i))=
      Measure.pi (fun _ : Fin R => stdGaussian (Space d)) := by
  have hI : iIndepFun (fun p (ω : Fin (numLevels n)×Fin R→Space d) => ω p)
      (trialLaw n d R) := iIndepFun_pi (fun _ => aemeasurable_id)
  have hrow := iIndepFun.precomp (g:=fun i : Fin R => (j,i))
    (fun a b h => (Prod.mk.inj h).2) hI
  rw [iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (j,i)).aemeasurable) hrow]
  congr 1
  funext i
  exact (measurePreserving_eval (fun _ : Fin (numLevels n)×Fin R => stdGaussian (Space d)) (j,i)).map_eq

theorem independent_finite_parameter_bound {κ Υ Ω : Type*} [Finite κ] [MeasurableSpace κ]
    [MeasurableSingletonClass κ] [MeasurableSpace Υ] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Υ) [IsProbabilityMeasure ν]
    (F : Ω→κ) (Y : Ω→Υ) (hF : Measurable F) (hY : Measurable Y)
    (hI : IndepFun F Y μ) (hν : μ.map Y=ν)
    (B : ℝ) (E : κ→Set Υ) (hE : ∀k,MeasurableSet (E k)) (hB : ∀k,ν.real (E k)≤B) :
    μ.real {ω | Y ω∈E (F ω)} ≤ B := by
  haveI : IsProbabilityMeasure (μ.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let A : Set (κ×Υ) := {z | z.2∈E z.1}
  have hA : MeasurableSet A := by
    apply measurableSet_setOfPred.mpr
    apply measurable_from_prod_countable_right
    intro k
    exact measurableSet_setOfPred.mp (hE k)
  let f : κ×Υ→ℝ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hfint : Integrable f ((μ.map F).prod ν) := (integrable_const (1:ℝ)).indicator hA
  calc
    μ.real {ω | Y ω∈E (F ω)} = ∫ω,f (F ω,Y ω) ∂μ := by
      simpa [f,A,Set.indicator,Set.preimage] using
        (integral_indicator_one (μ:=μ) (hA.preimage (hF.prodMk hY))).symm
    _ = ∫z,f z ∂μ.map (fun ω => (F ω,Y ω)) :=
      (integral_map (hF.prodMk hY).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫z,f z ∂(μ.map F).prod ν := by
      rw [hI.map_prod_eq_prod_map_map hF.aemeasurable hY.aemeasurable,hν]
    _ = ∫k,∫y,f (k,y) ∂ν ∂μ.map F := integral_prod f hfint
    _ = ∫k,ν.real (E k) ∂μ.map F := by
      apply integral_congr_ae
      filter_upwards [] with k
      simpa [f,A,Set.indicator] using
        (integral_indicator_one (μ:=ν) (hE k))
    _ ≤ ∫_k,B ∂μ.map F := by
      apply integral_mono Integrable.of_finite (integrable_const B)
      intro k
      exact hB k
    _ = B := by simp

theorem adaptive_core_deviation {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : Fin (numLevels n)) (x : Fin n)
    (hR : 0 < R) (ε : ℝ) (hε : 0 ≤ ε) :
    (trialLaw n d R).real {ω |
      ε < |freq (fun i => localMax G v (cores G v δ ω j.val) (ω (j,i))) x-
        pLocal G v (cores G v δ ω j.val) x|} ≤
      2*Real.exp (-2*R*ε^2) := by
  let E : Finset (Fin n)→Set (Fin R→Space d) := fun F =>
    {z | ε < |freq (fun i => localMax G v F (z i)) x-pLocal G v F x|}
  have hE : ∀F,MeasurableSet (E F) := by
    intro F
    have hf : Measurable (fun z : Fin R→Space d => freq (fun i => localMax G v F (z i)) x) :=
      measurable_freq (n:=n) (R:=R) (Ω:=Fin R→Space d)
        (fun (i : Fin R) (z : Fin R→Space d) => localMax G v F (z i))
        (fun i => (measurable_localMax G v F).comp (measurable_pi_apply i)) x
    exact measurableSet_lt measurable_const ((hf.sub_const (pLocal G v F x)).abs)
  exact independent_finite_parameter_bound (trialLaw n d R)
    (Measure.pi fun _ : Fin R => stdGaussian (Space d))
    (fun ω => cores G v δ ω j.val) (fun ω i => ω (j,i))
    (measurable_cores G v δ j.val) (by fun_prop) (cores_independent_row G v δ j)
    (trial_row_map j) _ E hE (fun F => fixed_core_deviation G v F x hR ε hε)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxSampleRate -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def concentrationRuns (n : ℕ) (δ : ℝ) : ℕ :=
  ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊

theorem concentrationRuns_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hℓ : 0 < numLevels n) :
    0 < concentrationRuns n δ ∧
      (numLevels n:ℝ)*n*(2*Real.exp (-2*(concentrationRuns n δ:ℝ)*(δ/8)^2)) ≤ 1/4 := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n=0 := by omega
    simp [numLevels,hn0] at hℓ
  have hnr : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hℓr : 1 ≤ (numLevels n:ℝ) := by exact_mod_cast hℓ
  have hA : 0 < 8*(n:ℝ)*(numLevels n:ℝ) := by positivity
  have hA1 : 1 < 8*(n:ℝ)*(numLevels n:ℝ) := by nlinarith
  have hlog : 0 < Real.log (8*(n:ℝ)*(numLevels n:ℝ)) := Real.log_pos hA1
  have hceil : 32*δ⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤
      (concentrationRuns n δ:ℝ) := Nat.le_ceil _
  have hRp : 0 < (concentrationRuns n δ:ℝ) :=
    lt_of_lt_of_le (by positivity) hceil
  constructor
  · exact_mod_cast hRp
  · have hmul := mul_le_mul_of_nonneg_right hceil (show 0 ≤ δ^2/32 by positivity)
    have heq : (32*δ⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ)))*(δ^2/32)=
        Real.log (8*(n:ℝ)*(numLevels n:ℝ)) := by field_simp
    have hmain : Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤
        (concentrationRuns n δ:ℝ)*δ^2/32 := by nlinarith [heq]
    calc
      _ = (numLevels n:ℝ)*n*(2*Real.exp (-((concentrationRuns n δ:ℝ)*δ^2/32))) := by
        congr 3
        ring
      _ ≤ (numLevels n:ℝ)*n*(2*Real.exp (-Real.log (8*(n:ℝ)*(numLevels n:ℝ)))) := by
        gcongr
      _ = 1/4 := by
        rw [Real.exp_neg,Real.exp_log hA]
        field_simp
        ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLemma21 -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem measurable_sampleSet {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) (i : Fin R) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => sampleSet G v δ ω j i) := by
  classical
  let U : Finset (Fin n)×(Fin (numLevels n)×Fin R→Space d)→Finset (Fin n) :=
    fun p => sampledAt G v p.2 p.1 (j-1) i
  have hU : Measurable U := measurable_from_prod_countable_right
    (fun F => measurable_sampledAt_fixed (R:=R) G v F (j-1) i)
  change Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => U (cores G v δ ω (j-1),ω))
  exact hU.comp ((measurable_cores (R:=R) G v δ (j-1)).prodMk measurable_id)

theorem measurable_phat {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (j : ℕ) (x : Fin n) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => phat G v δ ω j x) :=
  measurable_freq (n:=n) (R:=R) (Ω:=Fin (numLevels n)×Fin R→Space d)
    (fun (i : Fin R) (ω : Fin (numLevels n)×Fin R→Space d) => sampleSet G v δ ω j i)
    (measurable_sampleSet (R:=R) G v δ j) x

theorem phat_survivor_lt {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (j : ℕ) (hj : 1 ≤ j) (x : Fin n) (hx : x∈cores G v δ ω j) :
    phat G v δ ω j x<δ/2 := by
  classical
  obtain ⟨k,rfl⟩ : ∃k,j=k+1 := ⟨j-1,by omega⟩
  change freq (sampledAt G v ω (cores G v δ ω k) k) x<δ/2
  exact (Finset.mem_filter.mp hx).2

theorem phat_succ_eq {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n → Space d) (δ : ℝ) (ω : Fin (numLevels n)×Fin R→Space d)
    (j : Fin (numLevels n)) (x : Fin n) :
    phat G v δ ω (j.val+1) x=
      freq (fun i => localMax G v (cores G v δ ω j.val) (ω (j,i))) x := by
  classical
  change freq (sampledAt G v ω (cores G v δ ω j.val) j.val) x=_
  congr 1
  funext i
  rw [sampledAt,dif_pos j.isLt]

theorem accurate_survivor_bound (δ b p : ℝ) (hδ : 0 < δ)
    (hb : b<δ/2) (hp : -(δ/8) ≤ b-p) : p<δ := by
  linarith

theorem lemma_21 {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (T : ℕ) :
    (trialLaw n d ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊).real
        {ω | ∀j,1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀x∈cores G v δ ω (j-1),
            |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8) ∧
          (∀x∈cores G v δ ω j,pLocal G v (cores G v δ ω (j-1)) x<δ)} ≥ 3/4 := by
  classical
  by_cases hℓ : 0 < numLevels n
  · let R := concentrationRuns n δ
    let μ := trialLaw n d R
    haveI : IsProbabilityMeasure μ := instIsProbabilityMeasureTrialLaw n d R
    have hRate := concentrationRuns_bound n δ hδ0 hℓ
    let Bad : (Fin (numLevels n)×Fin n)→Set (Fin (numLevels n)×Fin R→Space d) :=
      fun p => {ω | δ/8 < |phat G v δ ω (p.1.val+1) p.2-
        pLocal G v (cores G v δ ω p.1.val) p.2|}
    have hBadMeas : ∀p,MeasurableSet (Bad p) := by
      intro p
      have hph : Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
          phat G v δ ω (p.1.val+1) p.2) := measurable_phat (R:=R) G v δ (p.1.val+1) p.2
      have hpc : Measurable (fun ω : Fin (numLevels n)×Fin R→Space d =>
          pLocal G v (cores G v δ ω p.1.val) p.2) :=
        (measurable_of_countable (fun F : Finset (Fin n) => pLocal G v F p.2)).comp
          (measurable_cores (R:=R) G v δ p.1.val)
      exact measurableSet_lt measurable_const (hph.sub hpc).abs
    have hBad : ∀p,μ.real (Bad p) ≤ 2*Real.exp (-2*R*(δ/8)^2) := by
      intro p
      have h := adaptive_core_deviation G v δ p.1 p.2 hRate.1 (δ/8) (by positivity)
      simpa only [Bad,phat_succ_eq] using h
    have hU : μ.real (⋃p,Bad p) ≤ 1/4 := by
      calc
        _ ≤ ∑p,μ.real (Bad p) := measureReal_iUnion_fintype_le Bad
        _ ≤ ∑_p : Fin (numLevels n)×Fin n,2*Real.exp (-2*R*(δ/8)^2) :=
          Finset.sum_le_sum (fun p _ => hBad p)
        _ = (numLevels n:ℝ)*n*(2*Real.exp (-2*R*(δ/8)^2)) := by simp [Fintype.card_prod]
        _ ≤ 1/4 := hRate.2
    have hGood : 3/4 ≤ μ.real (⋃p,Bad p)ᶜ := by
      rw [probReal_compl_eq_one_sub (MeasurableSet.iUnion hBadMeas)]
      linarith
    apply hGood.trans
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hω j hj1 hjℓ hjC
    have hAcc : ∀x : Fin n,
        |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8 := by
      intro x
      have hn : ω∉Bad (⟨j-1,by omega⟩,x) := by
        intro h
        exact hω (Set.mem_iUnion.mpr ⟨(⟨j-1,by omega⟩,x),h⟩)
      have hj : j-1+1=j := by omega
      simpa only [Bad,Set.mem_setOf_eq,hj,not_lt] using hn
    constructor
    · exact fun x _ => hAcc x
    · intro x hx
      have hp := phat_survivor_lt G v δ ω j hj1 x hx
      have ha := (abs_le.mp (hAcc x)).1
      exact accurate_survivor_bound δ _ _ hδ0 hp ha
  · have hz : numLevels n=0 := by omega
    have hE : {ω : Fin (numLevels n)×
        Fin ⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊→Space d |
        ∀j,1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
          (∀x∈cores G v δ ω (j-1),
            |phat G v δ ω j x-pLocal G v (cores G v δ ω (j-1)) x| ≤ δ/8) ∧
          (∀x∈cores G v δ ω j,pLocal G v (cores G v δ ω (j-1)) x<δ)}=Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
      intro j hj1 hjℓ
      omega
    rw [hE,probReal_univ]
    norm_num

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxNoFailure -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem alg2_ne_none_of_cover_parameters {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k δ w t H ε : ℝ) (T : ℕ)
    (ω : Fin (numLevels n)×Fin R→Space d) (hk : 2<k) (hv : OrdinaryVectorColoring G v k)
    (hδ : 0<δ) (hR : 0<R) (hℓ : 1 ≤ numLevels n) (hw : 0 ≤ w) (ht : 2 ≤ t) (hH : 0 ≤ H)
    (hδexp : δ=Real.exp (-(t^2/2)))
    (hBudget : (numLevels n:ℝ)*(2*T/δ)<n)
    (hGood : ∀j,1 ≤ j → j ≤ numLevels n → Constructed G v δ T ω j →
      ∀x∈cores G v δ ω j,pLocal G v (cores G v δ ω (j-1)) x<δ)
    (hLift : ∀F W : Finset (Fin n),W⊆F → ∀r : Fin n,∀U q : ℝ,0<U →
      IsCover (W.image (uvec v r)) (U*t) q → (∀x∈W,pLocal G v F x ≤ δ) →
      IsCover ((neighborUnion G F W).image (uvec v r)) ((U+40*w)*t) (q-ε))
    (hGrowth : Real.sqrt H ≤ (1+1/(k-1))/Real.sqrt 2+40*w*((numLevels n-1:ℕ):ℝ))
    (hQuality : (n:ℝ)*Real.exp (-(H*t^2/2)) <
      (1-millsConstant⁻¹*t*Real.exp (-(t^2/4)))-((numLevels n-1:ℕ):ℝ)*ε) :
    alg2 G v δ T ω≠none := by
  classical
  intro hfail
  let C := cores G v δ ω
  have hConstructed : ∀j,j ≤ numLevels n → Constructed G v δ T ω j := by
    intro j hj j' hj'1 hj'j i
    exact alg2_none_sample_small G v δ T ω hfail j' hj'1 (hj'j.trans hj) i
  have hP : ∀j,1 ≤ j → j ≤ numLevels n → ∀x∈C j,pLocal G v (C (j-1)) x ≤ δ := by
    intro j hj1 hj x hx
    exact (hGood j hj1 hj (hConstructed j hj) x hx).le
  obtain ⟨r,hr⟩ := failed_core_nonempty_of_budget G v δ hδ T ω hR hfail hBudget
  have hStep : C (numLevels n)⊆C (numLevels n-1) := by
    have h := cores_step_subset G v δ ω (numLevels n-1)
    simpa only [Nat.sub_add_cancel hℓ] using h
  have hrF := hStep hr
  have hrp : pLocal G v (C (numLevels n-1)) r ≤ Real.exp (-(t^2/2)) := by
    rw [← hδexp]
    exact hP (numLevels n) hℓ le_rfl r hr
  have hInitial := ordinary_initial_cover G v k hk hv (C (numLevels n-1)) r hrF t ht hrp
  let W₀ := nbr G (C (numLevels n-1)) r
  let U₀ := (1+1/(k-1))/Real.sqrt 2
  let q₀ := 1-millsConstant⁻¹*t*Real.exp (-(t^2/4))
  have hW₀ : W₀⊆C (numLevels n-1) := by intro x hx; exact (Finset.mem_filter.mp hx).1
  have hU₀ : 0<U₀ := by
    have hk1 : 0<k-1 := by linarith
    dsimp [U₀]
    positivity
  have hAll := backward_cover_iteration G v r C W₀ (numLevels n-1) hW₀
    (cores_step_subset G v δ ω) δ U₀ w t q₀ ε hU₀ hw hInitial
    (fun j hj1 hj x hx => hP j hj1 (by omega) x hx)
    (fun F W hWF U q hU hc hp => hLift F W hWF r U q hU hc hp)
  have hLast := hAll (numLevels n-1) le_rfl
  let S := backwardCoverSets G C W₀ (numLevels n-1) (numLevels n-1)
  have ht0 : 0<t := by linarith
  have hWeak := cover_mono_threshold (S.image (uvec v r)) (Real.sqrt H*t)
    ((U₀+40*w*((numLevels n-1:ℕ):ℝ))*t) (q₀-((numLevels n-1:ℕ):ℝ)*ε)
    (mul_le_mul_of_nonneg_right hGrowth ht0.le) hLast
  have hUpper := cover_population_upper (uvec v r) S (ordinary_root_residual_norm_le G v k hv r)
    (Real.sqrt H*t) (q₀-((numLevels n-1:ℕ):ℝ)*ε) (by positivity) hWeak
  have hT2 : (Real.sqrt H*t)^2=H*t^2 := by rw [mul_pow,Real.sq_sqrt hH]
  rw [hT2] at hUpper
  exact not_lt_of_ge hUpper hQuality

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxFailureLimits -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem highDegree_population_tail_identity (k β Cl : ℝ) (n : ℕ) (hn : 0<n)
    (hs : 0<highDegreeSquare k β Cl n) :
    (n:ℝ)*Real.exp (-(highDegreeH k β Cl n*(highDegreeT k β Cl n)^2/2))=((highDegreeT k β Cl n)^20)⁻¹ := by
  let t := highDegreeT k β Cl n
  let H := highDegreeH k β Cl n
  let H₀ := highDegreeH0 k β Cl n
  let w := roundingSlack t
  have ht : 0<t := Real.sqrt_pos.mpr hs
  have hGap : H-H₀=40*w := by dsimp [H,H₀,w,t,highDegreeH]; ring
  have hSlack : w*t^2=Real.log t := div_mul_cancel₀ _ (pow_ne_zero 2 ht.ne')
  have hExp : Real.exp (-20*Real.log t)=(t^20)⁻¹ := by
    rw [show -20*Real.log t=-(20*Real.log t) by ring,Real.exp_neg]
    rw [show 20*Real.log t=(20:ℕ)*Real.log t by norm_num,Real.exp_nat_mul,Real.exp_log ht]
  calc
    (n:ℝ)*Real.exp (-(H*t^2/2))=Real.exp (H₀*t^2/2)*Real.exp (-(H*t^2/2)) := by
      rw [highDegree_exp_population k β Cl n hn hs]
    _ = Real.exp (H₀*t^2/2-H*t^2/2) := by rw [Real.exp_sub,Real.exp_neg]; rfl
    _ = Real.exp (-20*Real.log t) := by
      congr 1
      nlinarith only [congrArg (fun z : ℝ => z*t^2) hGap,hSlack]
    _ = (t^20)⁻¹ := hExp

theorem highDegree_population_tail_tendsto_zero (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    Tendsto (fun n : ℕ => (n:ℝ)*Real.exp (-(highDegreeH k β Cl n*(highDegreeT k β Cl n)^2/2))) atTop (𝓝 0) := by
  have h := tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : (20:ℕ)≠0)).comp (highDegreeT_tendsto_atTop k β Cl ha))
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),(highDegreeSquare_tendsto_atTop k β Cl ha).eventually_gt_atTop 0] with n hn hs
  exact (highDegree_population_tail_identity k β Cl n (by omega) hs).symm

theorem highDegree_threshold_growth (k β Cl U₀ : ℝ) (ha : 0<highDegreeRate k β) :
    ∀ᶠ n : ℕ in atTop,Real.sqrt (highDegreeH k β Cl n) ≤
      U₀+40*roundingSlack (highDegreeT k β Cl n)*((numLevels n-1:ℕ):ℝ) := by
  let B := 1/highDegreeRate k β+1
  have hH : ∀ᶠ n : ℕ in atTop,highDegreeH k β Cl n ≤ B :=
    ((highDegreeH_tendsto k β Cl ha).eventually_lt_const (show 1/highDegreeRate k β<B by dsimp [B]; linarith)).mono fun _ h => h.le
  have hG := (iteration_slack_growth k β Cl ha).eventually_ge_atTop ((Real.sqrt B-U₀)/40)
  filter_upwards [hH,hG] with n hH hG
  have hBound : Real.sqrt B ≤ U₀+40*roundingSlack (highDegreeT k β Cl n)*((numLevels n-1:ℕ):ℝ) := by
    nlinarith only [hG]
  exact (Real.sqrt_le_sqrt hH).trans hBound

theorem highDegree_quality_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β) :
    ∀ᶠ n : ℕ in atTop,(n:ℝ)*Real.exp (-(highDegreeH k β Cl n*(highDegreeT k β Cl n)^2/2)) <
      (1-millsConstant⁻¹*highDegreeT k β Cl n*Real.exp (-((highDegreeT k β Cl n)^2/4)))-
        ((numLevels n-1:ℕ):ℝ)*((highDegreeT k β Cl n)^18)⁻¹ := by
  filter_upwards [(highDegree_population_tail_tendsto_zero k β Cl ha).eventually_lt_const (by norm_num : (0:ℝ)<1/4),
    (highDegree_final_cover_quality k β Cl millsConstant⁻¹ ha).eventually_const_lt (by norm_num : (1/2:ℝ)<1)] with n hp hq
  linarith only [hp,hq]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxAmplification -/

set_option autoImplicit false
set_option maxHeartbeats 500000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

instance instIsProbabilityMeasureThm2Law (n d : ℕ) (k β Cl cT : ℝ) :
    IsProbabilityMeasure (thm2Law n d k β Cl cT) := by
  unfold thm2Law
  infer_instance

theorem finite_pi_map_curry {ι J E : Type*} [Fintype ι] [Fintype J]
    [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : ι×J => ν)).map (MeasurableEquiv.curry ι J E)=
      Measure.pi (fun _ : ι => Measure.pi (fun _ : J => ν)) := by
  simpa only [Measure.infinitePi_eq_pi] using
    (Measure.infinitePi_map_curry (fun (_ : ι) (_ : J) => ν))

theorem flat_trials_all_event {J E : Type*} [Fintype J] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (N : ℕ) (B : Set (J→E))
    (hB : MeasurableSet B) :
    (Measure.pi (fun _ : Fin N×J => ν)).real
      {ω | ∀t : Fin N,(fun j => ω (t,j))∈B} =
        ((Measure.pi (fun _ : J => ν)).real B)^N := by
  have hpi : MeasurableSet (Set.univ.pi (fun _ : Fin N => B)) :=
    MeasurableSet.univ_pi (fun _ => hB)
  have hset : {ω : Fin N×J→E | ∀t : Fin N,(fun j => ω (t,j))∈B}=
      (MeasurableEquiv.curry (Fin N) J E) ⁻¹' (Set.univ.pi (fun _ : Fin N => B)) := by
    ext ω
    simp only [MeasurableEquiv.curry,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_univ_pi]
    rfl
  rw [hset,← map_measureReal_apply (MeasurableEquiv.curry (Fin N) J E).measurable hpi,
    finite_pi_map_curry]
  simp only [measureReal_def,Measure.pi_pi,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow]

theorem flat_trials_failure_bound {J E : Type*} [Fintype J] [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (N : ℕ) (B : Set (J→E))
    (hB : MeasurableSet B) (q : ℝ) (hprob : (Measure.pi (fun _ : J => ν)).real B ≤ q) :
    (Measure.pi (fun _ : Fin N×J => ν)).real
      {ω | ∀t : Fin N,(fun j => ω (t,j))∈B} ≤ q^N := by
  rw [flat_trials_all_event ν N B hB]
  exact pow_le_pow_left₀ (measureReal_nonneg) hprob N

theorem measurable_largest {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (l : List (Ω→Finset (Fin n))) (hl : ∀f∈l,Measurable f) :
    Measurable (fun ω => largest (l.map (fun f => f ω))) := by
  classical
  letI : MeasurableSpace (List (Finset (Fin n))) := ⊤
  haveI : MeasurableSingletonClass (List (Finset (Fin n))) := ⟨fun _ => trivial⟩
  have h : Measurable (fun p : List (Finset (Fin n)) => largest p) := measurable_of_countable _
  apply h.comp
  induction l with
  | nil => exact measurable_const
  | cons f l ih =>
    have hc : Measurable (fun p : Finset (Fin n)×List (Finset (Fin n)) => p.1::p.2) :=
      measurable_of_countable _
    exact hc.comp ((hl f List.mem_cons_self).prodMk
      (ih (fun f hf => hl f (List.mem_cons_of_mem _ hf))))

theorem measurable_trialObtained {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) :
    Measurable (fun ω : Fin (numLevels n)×Fin R→Space d => trialObtained G v δ T ω) := by
  classical
  letI : MeasurableSpace (List (Finset (Fin n))) := ⊤
  haveI : MeasurableSingletonClass (List (Finset (Fin n))) := ⟨fun _ => trivial⟩
  let l : List ((Fin (numLevels n)×Fin R→Space d)→Finset (Fin n)) :=
    (List.range (numLevels n)).flatMap (fun j => (List.finRange R).map
      (fun i => fun ω => sampleSet G v δ ω (j+1) i))
  have hl : ∀f∈l,Measurable f := by
    intro f hf
    obtain ⟨j,hj,hi⟩ := List.mem_flatMap.mp hf
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hi
    exact measurable_sampleSet G v δ (j+1) i
  have hlistGen : ∀L : List ((Fin (numLevels n)×Fin R→Space d)→Finset (Fin n)),
      (∀f∈L,Measurable f) → Measurable (fun ω => L.map (fun f => f ω)) := by
    intro L hL
    induction L with
    | nil => exact measurable_const
    | cons f L ih =>
      have hc : Measurable (fun p : Finset (Fin n)×List (Finset (Fin n)) => p.1::p.2) :=
        measurable_of_countable _
      exact hc.comp ((hL f List.mem_cons_self).prodMk
        (ih (fun f hf => hL f (List.mem_cons_of_mem _ hf))))
  have hlist := hlistGen l hl
  let P : List (Finset (Fin n))→Finset (Fin n) := fun z =>
    match z.find? (fun I => T ≤ I.card) with
    | some I => I
    | none => largest z
  have hP : Measurable P := measurable_of_countable _
  have hEq : ∀ω,P (l.map (fun f => f ω))=trialObtained G v δ T ω := by
    intro ω
    have hm : l.map (fun f => f ω)=alg2Sampled G v δ ω := by
      simp only [l,alg2Sampled,List.map_flatMap,List.map_map,Function.comp_def]
    rw [hm]
    rfl
  simpa only [Function.comp_def,hEq] using hP.comp hlist

theorem measurable_thm2Output {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl cT : ℝ) :
    Measurable (fun ω : Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d =>
      thm2Output G v k β Cl cT ω) := by
  let l : List ((Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d)→Finset (Fin n)) :=
    List.ofFn (fun t : Fin (trialsA cT n) => fun ω =>
      trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) (fun p => ω (t,p)))
  have hl : ∀f∈l,Measurable f := by
    intro f hf
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hf
    exact (measurable_trialObtained G v _ _).comp (by fun_prop)
  simpa only [l,List.map_ofFn,Function.comp_def,thm2Output] using measurable_largest l hl

theorem thm2_failure_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl cT : ℝ) (T : ℕ) (q : ℝ)
    (hfail : (trialLaw n d (runsA k β Cl n)).real
      {ω | (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<T} ≤ q) :
    (thm2Law n d k β Cl cT).real {ω | (thm2Output G v k β Cl cT ω).card<T} ≤
      q^(trialsA cT n) := by
  let B : Set (Fin (numLevels n)×Fin (runsA k β Cl n)→Space d) :=
    {ω | (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<T}
  have hB : MeasurableSet B := by
    exact (Set.to_countable {I : Finset (Fin n) | I.card<T}).measurableSet.preimage
      (measurable_trialObtained G v _ _)
  have hAll := flat_trials_failure_bound (stdGaussian (Space d)) (trialsA cT n) B hB q hfail
  have hsub : {ω | (thm2Output G v k β Cl cT ω).card<T} ⊆
      {ω | ∀t : Fin (trialsA cT n),(fun p => ω (t,p))∈B} := by
    intro ω hω t
    exact lt_of_le_of_lt (thm2Output_card_trial G v k β Cl cT ω t) hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans hAll

theorem quarter_trials_le_rpow (C : ℝ) (hC : 0 < C) (n : ℕ) (hn : 0 < n) :
    (1/4:ℝ)^(trialsA (C/Real.log 4) n) ≤ (n:ℝ)^(-C) := by
  have hl : 0 < Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hc : (C/Real.log 4)*Real.log n ≤ (trialsA (C/Real.log 4) n:ℝ) := Nat.le_ceil _
  have hm := mul_le_mul_of_nonneg_left hc hl.le
  have heq : Real.log (4:ℝ)*((C/Real.log 4)*Real.log n)=C*Real.log n := by field_simp
  rw [heq] at hm
  rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ)<1/4),
    Real.rpow_def_of_pos hnR]
  have hlog : Real.log (1/4:ℝ)=-Real.log 4 := by
    rw [show (1/4:ℝ)=(4:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [hlog]
  apply Real.exp_le_exp.mpr
  nlinarith only [hm]

theorem thm2_amplified_size_bound {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl C : ℝ) (hC : 0 < C) (hn : 0 < n)
    (T : ℕ) (B : ℝ) (hBT : B ≤ (T:ℝ))
    (hfail : (trialLaw n d (runsA k β Cl n)).real
      {ω | (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<T} ≤ 1/4) :
    (thm2Law n d k β Cl (C/Real.log 4)).real
      {ω | IsIndep G (thm2Output G v k β Cl (C/Real.log 4) ω) ∧
        B ≤ ((thm2Output G v k β Cl (C/Real.log 4) ω).card:ℝ)} ≥ 1-(n:ℝ)^(-C) := by
  let cT := C/Real.log 4
  let μ := thm2Law n d k β Cl cT
  haveI : IsProbabilityMeasure μ := instIsProbabilityMeasureThm2Law n d k β Cl cT
  let A : Set (Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d) :=
    {ω | (thm2Output G v k β Cl cT ω).card<T}
  have hA : MeasurableSet A :=
    (Set.to_countable {I : Finset (Fin n) | I.card<T}).measurableSet.preimage
      (measurable_thm2Output G v k β Cl cT)
  have hF : μ.real A ≤ (n:ℝ)^(-C) :=
    (thm2_failure_probability G v k β Cl cT T (1/4) hfail).trans
      (quarter_trials_le_rpow C hC n hn)
  have hhigh : 1-(n:ℝ)^(-C) ≤ μ.real Aᶜ := by
    rw [probReal_compl_eq_one_sub hA]
    linarith
  apply hhigh.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  refine ⟨thm2Output_independent G v k β Cl cT ω,?_⟩
  have hcard : T ≤ (thm2Output G v k β Cl cT ω).card := Nat.le_of_not_gt hω
  exact hBT.trans (by exact_mod_cast hcard)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxHighDegreeTrial -/

set_option autoImplicit false
set_option maxHeartbeats 1700000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem trialObtained_card_of_not_none {n d R : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d)
    (h : alg2 G v δ T ω≠none) : T ≤ (trialObtained G v δ T ω).card := by
  classical
  cases he : alg2 G v δ T ω with
  | none => exact (h he).elim
  | some I =>
    have hFind := he
    rw [alg2_eq_find] at hFind
    have hP : T ≤ I.card := by simpa only [decide_eq_true_eq] using List.find?_some hFind
    simpa only [trialObtained,he] using hP

theorem theorem2_high_degree_trial_failure (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) :
    ∃Cl : ℝ,0<Cl ∧ ∀ᶠ n : ℕ in atTop,∀d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
      OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
      (trialLaw n d (runsA k β Cl n)).real {ω |
        (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<targetA k β Cl n} ≤ 1/4 := by
  classical
  obtain ⟨Cl,hCl,hLifting⟩ := ordinary_cover_lifting_eventually k β hk hβ hreg
  have hRate := highDegreeRate_properties k β hk hβ hreg
  have hδ1 := (highDegree_delta_tendsto_zero k β Cl hRate.1 hreg).eventually_lt_const (by norm_num : (0:ℝ)<1)
  refine ⟨Cl,hCl,?_⟩
  filter_upwards [hLifting,highDegree_core_budget_eventually k β Cl hRate.1 hRate.2.1 hreg,
    highDegree_eventually_regime k β Cl hk hβ hreg,highDegree_quality_eventually k β Cl hRate.1,
    highDegree_threshold_growth k β Cl ((1+1/(k-1))/Real.sqrt 2) hRate.1,
    (highDegreeT_tendsto_atTop k β Cl hRate.1).eventually_ge_atTop 2,hδ1,
    numLevels_real_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (2:ℕ)] with n hLift hBudget hReg hQuality hGrowth ht2 hδ1 hℓ hn
  intro d G v hv hdeg
  let δ := deltaA k β Cl n
  let T := targetA k β Cl n
  let R := runsA k β Cl n
  let t := highDegreeT k β Cl n
  let w := roundingSlack t
  let H := highDegreeH k β Cl n
  let ε := (t^18)⁻¹
  let μ := trialLaw n d R
  letI : IsProbabilityMeasure μ := instIsProbabilityMeasureTrialLaw n d R
  have hδ := highDegree_delta_pos k β Cl n hreg hn
  have hℓNat : 1 ≤ numLevels n := by exact_mod_cast hℓ
  have hRdef : R=⌈32*δ⁻¹^2*Real.log (8*n*(numLevels n:ℝ))⌉₊ := by
    dsimp [R]
    rw [runsA,if_neg (not_le_of_gt hreg)]
  have hR : 0<R := by
    rw [hRdef]
    exact (concentrationRuns_bound n δ hδ (by omega)).1
  have hT2 : t^2=highDegreeSquare k β Cl n := Real.sq_sqrt hReg.2.2.2.le
  have hδexp : δ=Real.exp (-(t^2/2)) := by
    rw [hT2]
    exact highDegree_delta_eq_exp k β Cl n hreg hn
  have hLift' : ∀F W : Finset (Fin n),W⊆F → ∀r : Fin n,∀U q : ℝ,0<U →
      IsCover (W.image (uvec v r)) (U*t) q → (∀x∈W,pLocal G v F x ≤ δ) →
      IsCover ((neighborUnion G F W).image (uvec v r)) ((U+40*w)*t) (q-ε) := by
    intro F W hWF r U q hU hc hp
    apply hLift d G v hv hdeg F W hWF r U q hU hc
    intro x hx
    rw [← hδexp]
    exact hp x hx
  let Failure : Set (Fin (numLevels n)×Fin R→Space d) := {ω | (trialObtained G v δ T ω).card<T}
  have hFm : MeasurableSet Failure := by
    apply measurableSet_setOfPred.mpr
    exact (measurable_of_countable (fun I : Finset (Fin n) => I.card<T)).comp
      (measurable_trialObtained (R:=R) G v δ T)
  have hM := lemma_21 G v δ hδ hδ1 T
  rw [← hRdef] at hM
  have hGoodCompl : 3/4 ≤ μ.real Failureᶜ := by
    apply hM.trans
    apply measureReal_mono _ (measure_ne_top _ _)
    intro ω hGood hFail
    have hNotNone := alg2_ne_none_of_cover_parameters G v k δ w t H ε T ω hk hv hδ hR hℓNat
      (by exact (div_nonneg (Real.log_nonneg (by linarith : 1 ≤ t)) (sq_nonneg t))) ht2 (by linarith only [hReg.2.1])
      hδexp hBudget (fun j hj1 hj hjC x hx => (hGood j hj1 hj hjC).2 x hx) hLift' hGrowth hQuality
    have hc := trialObtained_card_of_not_none G v δ T ω hNotNone
    exact Nat.not_lt_of_ge hc hFail
  rw [probReal_compl_eq_one_sub hFm] at hGoodCompl
  linarith only [hGoodCompl]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxNonempty -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem localMax_nonempty {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (F : Finset (Fin n)) (hF : F.Nonempty) (g : Space d) : (localMax G v F g).Nonempty := by
  classical
  obtain ⟨x,hx,hmax⟩ := F.exists_max_image (fun x => ⟪g,v x⟫) hF
  let M := F.filter (fun y => ⟪g,v y⟫=⟪g,v x⟫)
  have hM : M.Nonempty := ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
  let y := M.max' hM
  have hyM : y∈M := Finset.max'_mem _ _
  have hyF := (Finset.mem_filter.mp hyM).1
  have hyscore := (Finset.mem_filter.mp hyM).2
  refine ⟨y,Finset.mem_filter.mpr ⟨hyF,?_⟩⟩
  intro z hz
  have hzF := (Finset.mem_filter.mp hz).1
  have hzy : ⟪g,v z⟫ ≤ ⟪g,v y⟫ := (hmax z hzF).trans_eq hyscore.symm
  rcases lt_or_eq_of_le hzy with hlt|heq
  · exact Or.inl hlt
  · apply Or.inr
    refine ⟨heq,?_⟩
    have hzM : z∈M := Finset.mem_filter.mpr ⟨hzF,heq.trans hyscore⟩
    have hle : z ≤ y := Finset.le_max' _ _ hzM
    have hne : z≠y := (Finset.mem_filter.mp hz).2.ne.symm
    exact lt_of_le_of_ne hle hne

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxOneTrial -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem bounded_reverse_markov {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω→ℝ) (hZ : Measurable Z) (N p : ℝ)
    (hN : 0 < N) (hp : 0 ≤ p) (hB : ∀ω,0 ≤ Z ω ∧ Z ω ≤ N)
    (hmean : N*p ≤ ∫ω,Z ω ∂μ) : p/2 ≤ μ.real {ω | N*p/2 ≤ Z ω} := by
  let A := {ω | N*p/2 ≤ Z ω}
  have hA : MeasurableSet A := measurableSet_le measurable_const hZ
  have hZi : Integrable Z μ := by
    refine (integrable_const N).mono' hZ.aestronglyMeasurable ?_
    exact Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hB ω).1] using (hB ω).2)
  have hpoint : ∀ω,Z ω ≤ N*p/2+A.indicator (fun _ => N) ω := by
    intro ω
    by_cases h : ω∈A
    · rw [Set.indicator_of_mem h]
      nlinarith [hB ω]
    · rw [Set.indicator_of_notMem h]
      have hn : Z ω<N*p/2 := lt_of_not_ge h
      linarith
  have hI := integral_mono hZi ((integrable_const _).add ((integrable_const N).indicator hA)) hpoint
  change (∫ω,Z ω ∂μ) ≤ ∫ω,N*p/2+A.indicator (fun _ => N) ω ∂μ at hI
  rw [integral_add (integrable_const _) ((integrable_const N).indicator hA),
    integral_const,integral_indicator_const N hA,probReal_univ,one_smul,smul_eq_mul] at hI
  nlinarith

theorem localIndicator_integrable {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (F : Finset (Fin n)) (x : Fin n) :
    Integrable (localIndicator G v F x) (stdGaussian (Space d)) := by
  refine (integrable_const (1:ℝ)).mono' (localIndicator_measurable G v F x).aestronglyMeasurable ?_
  filter_upwards [] with g
  have h := localIndicator_range G v F x g
  simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2

theorem card_localMax_expectation {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (F : Finset (Fin n)) :
    (∫g,((localMax G v F g).card:ℝ) ∂stdGaussian (Space d))=∑x : Fin n,pLocal G v F x := by
  classical
  have heq : ∀g,((localMax G v F g).card:ℝ)=∑x : Fin n,localIndicator G v F x g := by
    intro g
    symm
    simp only [localIndicator,Finset.sum_boole]
    have hf : Finset.univ.filter (fun x => x∈localMax G v F g)=localMax G v F g := by ext; simp
    rw [hf]
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun x _ => localIndicator_integrable G v F x)]
  apply Finset.sum_congr rfl
  intro x hx
  exact localIndicator_mean G v F x

theorem first_sample_large_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β : ℝ) (hk : 2 < k) (hβ : 0 ≤ β)
    (hv : OrdinaryVectorColoring G v k) (hn : 0 < n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) :
    pStarA k β n/2 ≤ gaussProb {g : Space d |
      (n:ℝ)*pStarA k β n/2 ≤ ((localMax G v Finset.univ g).card:ℝ)} := by
  have hM : Measurable (fun g : Space d => ((localMax G v Finset.univ g).card:ℝ)) :=
    (measurable_of_countable (fun S : Finset (Fin n) => (S.card:ℝ))).comp (measurable_localMax G v Finset.univ)
  have hp : 0 ≤ pStarA k β n := by unfold pStarA; exact div_nonneg (phiTail_nonneg _) (by norm_num)
  have hmean : (n:ℝ)*pStarA k β n ≤ ∫g,((localMax G v Finset.univ g).card:ℝ) ∂stdGaussian (Space d) := by
    rw [card_localMax_expectation]
    calc
      _ = ∑_x : Fin n,pStarA k β n := by simp
      _ ≤ ∑x : Fin n,pLocal G v Finset.univ x := Finset.sum_le_sum (fun x _ => ordinary_pLocal_lower G v k β hk hβ hv hn hdeg x)
  apply bounded_reverse_markov (stdGaussian (Space d)) _ hM n (pStarA k β n)
    (by exact_mod_cast hn) hp _ hmean
  intro g
  constructor
  · positivity
  · have h : (localMax G v Finset.univ g).card ≤ n := by
      simpa only [Fintype.card_fin] using Finset.card_le_univ (localMax G v Finset.univ g)
    exact_mod_cast h

theorem pStarA_pos (k β : ℝ) (n : ℕ) : 0 < pStarA k β n := by
  unfold pStarA
  exact div_pos (phiTail_pos _) (by norm_num)

theorem pStarA_le_half (k β : ℝ) (n : ℕ) : pStarA k β n ≤ 1/2 := by
  unfold pStarA
  exact div_le_div_of_nonneg_right (phiTail_le_one _) (by norm_num)

theorem repeat_low_degree_bound (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (1-p/2)^⌈2*Real.log 4/p⌉₊ ≤ (1/4:ℝ) := by
  have hc : 2*Real.log 4/p ≤ (⌈2*Real.log 4/p⌉₊:ℝ) := Nat.le_ceil _
  have hmul := (div_le_iff₀ hp).mp hc
  have he : 1-p/2 ≤ Real.exp (-(p/2)) := by
    simpa only [sub_eq_add_neg,add_comm] using Real.add_one_le_exp (-(p/2))
  calc
    _ ≤ (Real.exp (-(p/2)))^⌈2*Real.log 4/p⌉₊ := pow_le_pow_left₀ (by linarith) he _
    _ = Real.exp (-(p/2)*(⌈2*Real.log 4/p⌉₊:ℝ)) := by
      rw [← Real.rpow_natCast,← Real.exp_mul]
    _ ≤ Real.exp (-Real.log 4) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = 1/4 := by rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<4)]; norm_num

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxSmallN -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem alg2Sampled_head {n d R : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d) (δ : ℝ)
    (ω : Fin (numLevels n)×Fin R→Space d) (hℓ : 0<numLevels n) (hR : 0<R) :
    (alg2Sampled G v δ ω).head?=some (sampleSet G v δ ω 1 ⟨0,hR⟩) := by
  have hRange : List.range (numLevels n)=0::(List.range (numLevels n-1)).map Nat.succ := by
    have h := List.range_succ_eq_map (n:=numLevels n-1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ numLevels n)] at h
    exact h
  cases R with
  | zero => omega
  | succ R =>
    unfold alg2Sampled
    rw [hRange]
    simp only [List.flatMap_cons,List.finRange_succ,List.map_cons,List.cons_append,List.head?_cons,zero_add]
    rfl

theorem trialObtained_card_ge_head {n d R : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d) (I : Finset (Fin n))
    (hHead : (alg2Sampled G v δ ω).head?=some I) : I.card ≤ (trialObtained G v δ T ω).card := by
  classical
  obtain ⟨tail,hCons⟩ := List.head?_eq_some_iff.mp hHead
  unfold trialObtained
  rw [alg2_eq_find,hCons]
  by_cases hT : T ≤ I.card
  · simp only [List.find?_cons,hT,decide_true]
    exact le_rfl
  · simp only [List.find?_cons,hT,decide_false]
    cases hFind : tail.find? (fun J => decide (T ≤ J.card)) with
    | none => exact largest_card_mem _ I (by simp)
    | some J =>
      have hJ : T ≤ J.card := by simpa only [decide_eq_true_eq] using List.find?_some hFind
      exact (le_of_lt (lt_of_not_ge hT)).trans hJ

theorem trialObtained_nonempty {n d R : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (δ : ℝ) (T : ℕ) (ω : Fin (numLevels n)×Fin R→Space d) (hn : 0<n) (hℓ : 0<numLevels n) (hR : 0<R) :
    1 ≤ (trialObtained G v δ T ω).card := by
  classical
  let I := sampleSet G v δ ω 1 ⟨0,hR⟩
  have hI : I.Nonempty := by
    have hF : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
    have h := localMax_nonempty G v Finset.univ hF (ω (⟨0,hℓ⟩,⟨0,hR⟩))
    simpa only [I,sampleSet,cores,Nat.sub_self,sampledAt,dif_pos hℓ] using h
  have hCard : 1 ≤ I.card := Finset.card_pos.mpr hI
  exact hCard.trans (trialObtained_card_ge_head G v δ T ω I (alg2Sampled_head G v δ ω hℓ hR))

theorem runsA_pos (k β Cl : ℝ) (n : ℕ) (hn : 2 ≤ n) : 0<runsA k β Cl n := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hL : 0<(numLevels n:ℝ) := (Real.log_pos hn1).trans_le (Nat.le_ceil _)
  unfold runsA
  split
  · exact Nat.ceil_pos.mpr (div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) (pStarA_pos k β n))
  · apply Nat.ceil_pos.mpr
    have hδ : 0<deltaA k β Cl n := by
      rw [deltaA,if_neg (by assumption)]
      exact mul_pos (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos hL _)
    have hLNat : 1 ≤ numLevels n := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hL.ne')
    have hL1 : (1:ℝ) ≤ numLevels n := by exact_mod_cast hLNat
    have hArg : 1<8*(n:ℝ)*(numLevels n:ℝ) := by nlinarith
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (inv_pos.mpr hδ))) (Real.log_pos hArg)

theorem thm2Output_nonempty {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n→Space d)
    (k β Cl cT : ℝ) (hcT : 0<cT) (hn : 2 ≤ n)
    (ω : Fin (trialsA cT n)×(Fin (numLevels n)×Fin (runsA k β Cl n))→Space d) :
    1 ≤ (thm2Output G v k β Cl cT ω).card := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hLog : 0<Real.log (n:ℝ) := Real.log_pos hn1
  have hℓ : 0<numLevels n := Nat.ceil_pos.mpr hLog
  have hTrials : 0<trialsA cT n := Nat.ceil_pos.mpr (mul_pos hcT hLog)
  let j : Fin (trialsA cT n) := ⟨0,hTrials⟩
  have h := trialObtained_nonempty G v (deltaA k β Cl n) (targetA k β Cl n)
    (fun p => ω (j,p)) (by omega) hℓ (runsA_pos k β Cl n hn)
  exact h.trans (thm2Output_card_trial G v k β Cl cT ω j)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxHighSize -/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def highSizeGap (Cl : ℝ) (n : ℕ) : ℝ :=
  ((Cl+4)*Real.log (numLevels n:ℝ)+Real.log 100)/Real.log (n:ℝ)

theorem highSizeGap_tendsto (Cl : ℝ) : IsLittleO1 (highSizeGap Cl) := by
  have h := (log_numLevels_over_log_tendsto_zero.const_mul (Cl+4)).add
    ((tendsto_const_nhds (x:=Real.log (100:ℝ))).div_atTop log_nat_tendsto_atTop)
  have hEq : (fun n : ℕ => (Cl+4)*(Real.log (numLevels n:ℝ)/Real.log (n:ℝ))+Real.log 100/Real.log (n:ℝ))=
      highSizeGap Cl := by
    funext n
    unfold highSizeGap
    ring
  rw [hEq] at h
  simpa only [IsLittleO1,mul_zero,add_zero] using h

theorem high_target_size_bound (k β Cl : ℝ) (hreg : (k-2)/k<β) (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ)^(thm2Exponent k β-highSizeGap Cl n) ≤ (targetA k β Cl n:ℝ) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hlog : 0<Real.log (n:ℝ) := Real.log_pos hn1
  have hL : 0<(numLevels n:ℝ) := hlog.trans_le (Nat.le_ceil _)
  have hδ := highDegree_delta_pos k β Cl n hreg hn
  have hEq : (n:ℝ)^(thm2Exponent k β-highSizeGap Cl n)=
      (n:ℝ)*deltaA k β Cl n/(100*(numLevels n:ℝ)^4) := by
    rw [thm2Exponent,if_neg (not_le_of_gt hreg),highSizeGap,Real.rpow_def_of_pos hn0,
      highDegree_delta_eq_exp k β Cl n hreg hn]
    have hE : Real.log (n:ℝ)*(1-(k-2)*β/(2+k*β)-
        ((Cl+4)*Real.log (numLevels n:ℝ)+Real.log 100)/Real.log (n:ℝ))=
      Real.log (n:ℝ)-highDegreeSquare k β Cl n/2-Real.log 100-4*Real.log (numLevels n:ℝ) := by
      unfold highDegreeSquare highDegreeRate
      field_simp
      <;> ring
    rw [hE]
    rw [Real.exp_sub,Real.exp_sub,Real.exp_sub,Real.exp_log hn0,Real.exp_log (by norm_num : (0:ℝ)<100)]
    rw [show (4:ℝ)*Real.log (numLevels n:ℝ)=(4:ℕ)*Real.log (numLevels n:ℝ) by norm_num,
      Real.exp_nat_mul,Real.exp_log hL,Real.exp_neg]
    ring
  rw [hEq,targetA,if_neg (not_le_of_gt hreg)]
  exact Nat.le_ceil _

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxCallBounds -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem numLevels_le_input_eventually : ∀ᶠ n : ℕ in atTop,(numLevels n:ℝ) ≤ n := by
  have hr := log_numLevels_over_log_tendsto_zero.eventually_lt_const (by norm_num : (0:ℝ)<1)
  filter_upwards [hr,eventually_ge_atTop (2:ℕ),numLevels_real_tendsto_atTop.eventually_gt_atTop 0] with n hr hn hL
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hlogs := (div_lt_iff₀ (Real.log_pos hn1)).mp hr
  calc
    (numLevels n:ℝ)=Real.exp (Real.log (numLevels n:ℝ)) := (Real.exp_log hL).symm
    _ ≤ Real.exp (Real.log (n:ℝ)) := Real.exp_le_exp.mpr (by simpa only [one_mul] using hlogs.le)
    _ = n := Real.exp_log hn0

theorem trialsA_le_square_eventually (cT : ℝ) (hcT : 0<cT) :
    ∀ᶠ n : ℕ in atTop,(trialsA cT n:ℝ) ≤ (n:ℝ)^2 := by
  filter_upwards [eventually_ge_atTop (2:ℕ),(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (cT+1)] with n hn hnC
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hceil : (trialsA cT n:ℝ) ≤ cT*Real.log (n:ℝ)+1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hcT.le (Real.log_nonneg hn1))).le
  have hm := mul_le_mul_of_nonneg_left (Real.log_le_self hn0.le) hcT.le
  nlinarith only [hceil,hm,mul_nonneg (sub_nonneg.mpr hnC) hn0.le,hn1]

theorem highDegree_inverse_delta_le_square_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β)
    (ha1 : highDegreeRate k β<1) (hreg : (k-2)/k<β) :
    ∀ᶠ n : ℕ in atTop,(deltaA k β Cl n)⁻¹ ≤ (n:ℝ)^2 := by
  have hr := (highDegreeSquare_over_log_tendsto k β Cl).eventually_lt_const
    (show 2*highDegreeRate k β<4 by linarith)
  filter_upwards [hr,eventually_ge_atTop (2:ℕ)] with n hr hn
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hscaled := (div_lt_iff₀ (Real.log_pos hn1)).mp hr
  have hNpow : Real.exp (2*Real.log (n:ℝ))=(n:ℝ)^2 := by
    rw [show (2:ℝ)*Real.log (n:ℝ)=(2:ℕ)*Real.log (n:ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hn0]
  rw [highDegree_delta_eq_exp k β Cl n hreg hn,Real.exp_neg,inv_inv,← hNpow]
  apply Real.exp_le_exp.mpr
  linarith only [hscaled]

theorem highDegree_runs_le_pow_eight_eventually (k β Cl : ℝ) (ha : 0<highDegreeRate k β)
    (ha1 : highDegreeRate k β<1) (hreg : (k-2)/k<β) :
    ∀ᶠ n : ℕ in atTop,(runsA k β Cl n:ℝ) ≤ (n:ℝ)^8 := by
  filter_upwards [highDegree_inverse_delta_le_square_eventually k β Cl ha ha1 hreg,
    numLevels_le_input_eventually,numLevels_real_tendsto_atTop.eventually_ge_atTop 1,eventually_ge_atTop (257:ℕ)] with n hd hL hL1 hn
  have hn257 : (257:ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by linarith
  have hn0 : 0<(n:ℝ) := by linarith
  have hδ := highDegree_delta_pos k β Cl n hreg (by omega)
  have hArg : 1<8*(n:ℝ)*(numLevels n:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 8*(n:ℝ) by positivity)
    nlinarith only [h,hn257]
  have hLog0 : 0 ≤ Real.log (8*(n:ℝ)*(numLevels n:ℝ)) := (Real.log_pos hArg).le
  have hLog : Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤ 8*(n:ℝ)^2 := by
    apply (Real.log_le_self (by positivity)).trans
    have hm := mul_le_mul_of_nonneg_left hL (show 0 ≤ 8*(n:ℝ) by positivity)
    nlinarith only [hm]
  have hSq : (deltaA k β Cl n)⁻¹^2 ≤ (n:ℝ)^4 := by
    calc
      _ ≤ ((n:ℝ)^2)^2 := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hd 2
      _ = _ := by ring
  have hExpr : 32*(deltaA k β Cl n)⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ)) ≤ 256*(n:ℝ)^6 := by
    have hm := mul_le_mul hSq hLog hLog0 (by positivity : 0 ≤ (n:ℝ)^4)
    nlinarith only [hm]
  have hCeil : (runsA k β Cl n:ℝ) ≤ 32*(deltaA k β Cl n)⁻¹^2*Real.log (8*(n:ℝ)*(numLevels n:ℝ))+1 := by
    rw [runsA,if_neg (not_le_of_gt hreg)]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have h6 : (1:ℝ) ≤ (n:ℝ)^6 := one_le_pow₀ hn1
  have hN2 : (n:ℝ) ≤ (n:ℝ)^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hn1) hn0.le]
  calc
    (runsA k β Cl n:ℝ) ≤ 256*(n:ℝ)^6+1 := by linarith only [hExpr,hCeil]
    _ ≤ 257*(n:ℝ)^6 := by nlinarith only [h6]
    _ ≤ (n:ℝ)^2*(n:ℝ)^6 := mul_le_mul_of_nonneg_right (hn257.trans hN2) (by positivity)
    _ = (n:ℝ)^8 := by ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxPolynomialCalls -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem global_polynomial_bound_of_eventual (f : ℕ→ℕ) (m : ℕ)
    (hf : ∀ᶠ n : ℕ in atTop,(f n:ℝ) ≤ (n:ℝ)^m) :
    ∃K : ℝ,∀n : ℕ,(f n:ℝ) ≤ K*(n:ℝ)^K+K := by
  classical
  have hBoth : ∀ᶠ n : ℕ in atTop,1 ≤ n ∧ (f n:ℝ) ≤ (n:ℝ)^m := by
    filter_upwards [hf,eventually_ge_atTop (1:ℕ)] with n h hn
    exact ⟨hn,h⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hBoth
  let M := (Finset.range N).sup f
  let K := max m M+1
  have hK : 1 ≤ K := by dsimp [K]; omega
  have hmK : m ≤ K := by dsimp [K]; omega
  refine ⟨(K:ℝ),?_⟩
  intro n
  rw [Real.rpow_natCast]
  by_cases hn : N ≤ n
  · obtain ⟨hn1,hfn⟩ := hN n hn
    have hn1R : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hPow : (n:ℝ)^m ≤ (n:ℝ)^K := pow_le_pow_right₀ hn1R hmK
    have hF := hfn.trans hPow
    have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
    have hTerm := mul_nonneg (sub_nonneg.mpr hK1) (pow_nonneg (Nat.cast_nonneg n) K)
    have hK0 : (0:ℝ) ≤ K := by positivity
    nlinarith only [hF,hTerm,hK0]
  · have hnN : n<N := lt_of_not_ge hn
    have hNat : f n ≤ K := (Finset.le_sup (f:=f) (Finset.mem_range.mpr hnN)).trans
      (show M ≤ K by dsimp [K]; omega)
    have hF : (f n:ℝ) ≤ K := by exact_mod_cast hNat
    have hTerm : (0:ℝ) ≤ (K:ℝ)*(n:ℝ)^K := by positivity
    linarith only [hF,hTerm]

theorem thm2Calls_polynomial_of_runs (k β Cl cT : ℝ) (hcT : 0<cT)
    (hRuns : ∀ᶠ n : ℕ in atTop,(runsA k β Cl n:ℝ) ≤ (n:ℝ)^8) :
    ∃K : ℝ,∀n : ℕ,(thm2Calls k β Cl cT n:ℝ) ≤ K*(n:ℝ)^K+K := by
  apply global_polynomial_bound_of_eventual _ 11
  filter_upwards [trialsA_le_square_eventually cT hcT,numLevels_le_input_eventually,hRuns] with n hT hL hR
  simp only [thm2Calls,Nat.cast_mul]
  have h₁ := mul_le_mul hT hL (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg n) 2)
  have h₂ := mul_le_mul h₁ hR (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 2) (Nat.cast_nonneg n))
  apply h₂.trans_eq
  ring

theorem highDegree_calls_polynomial (k β Cl cT : ℝ) (hcT : 0<cT) (ha : 0<highDegreeRate k β)
    (ha1 : highDegreeRate k β<1) (hreg : (k-2)/k<β) :
    ∃K : ℝ,∀n : ℕ,(thm2Calls k β Cl cT n:ℝ) ≤ K*(n:ℝ)^K+K :=
  thm2Calls_polynomial_of_runs k β Cl cT hcT (highDegree_runs_le_pow_eight_eventually k β Cl ha ha1 hreg)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxTheorem2Assembly -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem theorem2_assemble (k β Cl C : ℝ) (hC : 0<C) (gap : ℕ→ℝ) (hgap : IsLittleO1 gap)
    (hEventually : ∀ᶠ n : ℕ in atTop,∀d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
      OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
      (n:ℝ)^(thm2Exponent k β-gap n) ≤ (targetA k β Cl n:ℝ) ∧
      (trialLaw n d (runsA k β Cl n)).real {ω |
        (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<targetA k β Cl n} ≤ 1/4) :
    ∃g : ℕ→ℝ,IsLittleO1 g ∧
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
        (thm2Law n d k β Cl (C/Real.log 4)).real
          {ω | IsIndep G (thm2Output G v k β Cl (C/Real.log 4) ω) ∧
            (n:ℝ)^(thm2Exponent k β-g n) ≤ ((thm2Output G v k β Cl (C/Real.log 4) ω).card:ℝ)} ≥ 1-(n:ℝ)^(-C) := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp hEventually
  let g : ℕ→ℝ := fun n => if n=0 then thm2Exponent k β-1 else if N ≤ n then gap n else thm2Exponent k β
  have hcT : 0<C/Real.log 4 := div_pos hC (Real.log_pos (by norm_num))
  have hg : IsLittleO1 g := by
    apply hgap.congr'
    filter_upwards [eventually_ge_atTop N,eventually_ge_atTop (1:ℕ)] with n hn hn1
    simp only [g,if_neg (by omega : n≠0),if_pos hn]
  refine ⟨g,hg,?_⟩
  intro n d G v hv hdeg
  cases n with
  | zero =>
    simp only [Nat.cast_zero]
    have hB : (0:ℝ)^(thm2Exponent k β-g 0)=0 := by
      simp only [g,if_pos rfl]
      rw [show thm2Exponent k β-(thm2Exponent k β-1)=1 by ring]
      norm_num
    have hEvent : {ω | IsIndep G (thm2Output G v k β Cl (C/Real.log 4) ω) ∧
        (0:ℝ)^(thm2Exponent k β-g 0) ≤ ((thm2Output G v k β Cl (C/Real.log 4) ω).card:ℝ)}=Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true,hB]
      exact ⟨thm2Output_independent G v k β Cl _ ω,by positivity⟩
    rw [hEvent,probReal_univ]
    have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 0) (-C)
    linarith only [h]
  | succ n =>
    by_cases hn1 : n+1=1
    · have hn0 : n=0 := by omega
      subst n
      simp only [Nat.cast_add,Nat.cast_zero,Nat.cast_one,zero_add,Real.one_rpow,sub_self]
      exact measureReal_nonneg
    · have hn2 : 2 ≤ n+1 := by omega
      by_cases hnN : N ≤ n+1
      · obtain ⟨hBT,hFail⟩ := hN (n+1) hnN d G v hv hdeg
        have h := thm2_amplified_size_bound G v k β Cl C hC (by omega) (targetA k β Cl (n+1)) _ hBT hFail
        simpa only [g,if_neg (by omega : n+1≠0),if_pos hnN] using h
      · have hB : ((n+1:ℕ):ℝ)^(thm2Exponent k β-g (n+1))=1 := by
          simp only [g,if_neg (by omega : n+1≠0),if_neg hnN,sub_self,Real.rpow_zero]
        have hEvent : {ω | IsIndep G (thm2Output G v k β Cl (C/Real.log 4) ω) ∧
            ((n+1:ℕ):ℝ)^(thm2Exponent k β-g (n+1)) ≤ ((thm2Output G v k β Cl (C/Real.log 4) ω).card:ℝ)}=Set.univ := by
          ext ω
          simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true,hB]
          refine ⟨thm2Output_independent G v k β Cl _ ω,?_⟩
          exact_mod_cast thm2Output_nonempty G v k β Cl (C/Real.log 4) hcT hn2 ω
        rw [hEvent,probReal_univ]
        have h := Real.rpow_nonneg (Nat.cast_nonneg (n+1)) (-C)
        linarith only [h]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxHighTheorem -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem theorem_2_high (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hreg : (k-2)/k<β) (C : ℝ) (hC : 0<C) :
    ∃(Cl cT : ℝ)(g : ℕ→ℝ),0<cT ∧ IsLittleO1 g ∧
      (∃K : ℝ,∀n : ℕ,(thm2Calls k β Cl cT n:ℝ) ≤ K*(n:ℝ)^K+K) ∧
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
        (thm2Law n d k β Cl cT).real
          {ω | IsIndep G (thm2Output G v k β Cl cT ω) ∧
            (n:ℝ)^(thm2Exponent k β-g n) ≤ ((thm2Output G v k β Cl cT ω).card:ℝ)} ≥ 1-(n:ℝ)^(-C) := by
  obtain ⟨Cl,hCl,hTrial⟩ := theorem2_high_degree_trial_failure k β hk hβ hreg
  let cT := C/Real.log 4
  have hcT : 0<cT := div_pos hC (Real.log_pos (by norm_num))
  have hRate := highDegreeRate_properties k β hk hβ hreg
  have hCalls := highDegree_calls_polynomial k β Cl cT hcT hRate.1 hRate.2.1 hreg
  have hEventually : ∀ᶠ n : ℕ in atTop,∀d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
      OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
      (n:ℝ)^(thm2Exponent k β-highSizeGap Cl n) ≤ (targetA k β Cl n:ℝ) ∧
      (trialLaw n d (runsA k β Cl n)).real {ω |
        (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<targetA k β Cl n} ≤ 1/4 := by
    filter_upwards [hTrial,eventually_ge_atTop (2:ℕ)] with n hTrial hn
    intro d G v hv hdeg
    exact ⟨high_target_size_bound k β Cl hreg n hn,hTrial d G v hv hdeg⟩
  obtain ⟨g,hg,hResult⟩ := theorem2_assemble k β Cl C hC (highSizeGap Cl) (highSizeGap_tendsto Cl) hEventually
  exact ⟨Cl,cT,g,hcT,hg,hCalls,hResult⟩

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLogTail -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_log_bounds (u : ℝ) (hu : 1 ≤ u) :
    -(u^2/2)+Real.log millsConstant-Real.log u ≤ Real.log (PhiTail u) ∧
      Real.log (PhiTail u) ≤ -(u^2/2) := by
  have hu0 : 0<u := zero_lt_one.trans_le hu
  have hC := millsConstant_pos
  have hprod : 0<u⁻¹*millsConstant*Real.exp (-(u^2/2)) := by positivity
  have hlo := Real.log_le_log hprod (phiTail_mills_lower u hu)
  rw [Real.log_mul (mul_ne_zero (inv_ne_zero hu0.ne') hC.ne') (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hu0.ne') hC.ne',Real.log_inv,Real.log_exp] at hlo
  have hhi := Real.log_le_log (phiTail_pos u) (phiTail_exp_upper u hu0.le)
  rw [Real.log_exp] at hhi
  exact ⟨by linarith only [hlo],hhi⟩

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowScale -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def lowGaussianBase (β : ℝ) (n : ℕ) : ℝ := 2*Real.log (2*(n:ℝ)^β)
def lowGaussianThreshold (k β : ℝ) (n : ℕ) : ℝ := Real.sqrt (lowGaussianBase β n)/cA k

theorem tendsto_atTop_of_ratio_log (f : ℕ→ℝ) (a : ℝ) (ha : 0<a)
    (h : Tendsto (fun n => f n/Real.log (n:ℝ)) atTop (𝓝 a)) : Tendsto f atTop atTop := by
  have hr := h.eventually_const_lt (show a/2<a by linarith)
  have hL : ∀ᶠ n : ℕ in atTop,(a/2)*Real.log (n:ℝ) ≤ f n := by
    filter_upwards [hr,log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hr hn
    exact ((lt_div_iff₀ hn).mp hr).le
  exact tendsto_atTop_mono' atTop hL (log_nat_tendsto_atTop.const_mul_atTop (by linarith : 0<a/2))

theorem lowGaussianBase_eq (β : ℝ) (n : ℕ) (hn : 0<n) :
    lowGaussianBase β n=2*(Real.log 2+β*Real.log (n:ℝ)) := by
  have hn0 : 0<(n:ℝ) := by exact_mod_cast hn
  rw [lowGaussianBase,Real.log_mul (by norm_num : (2:ℝ)≠0) (Real.rpow_pos_of_pos hn0 β).ne',Real.log_rpow hn0]

theorem lowGaussianBase_over_log_tendsto (β : ℝ) :
    Tendsto (fun n : ℕ => lowGaussianBase β n/Real.log (n:ℝ)) atTop (𝓝 (2*β)) := by
  have h := (tendsto_const_nhds (x:=2*β)).add
    ((tendsto_const_nhds (x:=2*Real.log (2:ℝ))).div_atTop log_nat_tendsto_atTop)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  change 2*β+(2*Real.log 2)/Real.log (n:ℝ)=lowGaussianBase β n/Real.log (n:ℝ)
  rw [lowGaussianBase_eq β n (by omega)]
  have hlog : Real.log (n:ℝ)≠0 := (Real.log_pos (by exact_mod_cast (show 1<n by omega))).ne'
  field_simp
  <;> ring

theorem lowGaussianBase_tendsto_atTop (β : ℝ) (hβ : 0<β) : Tendsto (lowGaussianBase β) atTop atTop :=
  tendsto_atTop_of_ratio_log _ _ (by positivity) (lowGaussianBase_over_log_tendsto β)

theorem lowGaussianThreshold_tendsto_atTop (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (lowGaussianThreshold k β) atTop atTop := by
  change Tendsto (fun n => Real.sqrt (lowGaussianBase β n)/cA k) atTop atTop
  have h := (Real.tendsto_sqrt_atTop.comp (lowGaussianBase_tendsto_atTop β hβ)).atTop_mul_const
    (inv_pos.mpr (cA_pos k hk))
  simpa only [Function.comp_apply,div_eq_mul_inv] using h

theorem log_lowGaussianBase_over_log_tendsto (β : ℝ) (hβ : 0<β) :
    Tendsto (fun n : ℕ => Real.log (lowGaussianBase β n)/Real.log (n:ℝ)) atTop (𝓝 0) := by
  have h₁ := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (lowGaussianBase_tendsto_atTop β hβ)
  have h := h₁.mul (lowGaussianBase_over_log_tendsto β)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [(lowGaussianBase_tendsto_atTop β hβ).eventually_gt_atTop 0] with n hn
  change (Real.log (lowGaussianBase β n)/lowGaussianBase β n)*(lowGaussianBase β n/Real.log (n:ℝ))=_
  field_simp

theorem log_lowGaussianThreshold_over_log_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (fun n : ℕ => Real.log (lowGaussianThreshold k β n)/Real.log (n:ℝ)) atTop (𝓝 0) := by
  have h := ((log_lowGaussianBase_over_log_tendsto β hβ).const_mul (1/2:ℝ)).sub
    ((tendsto_const_nhds (x:=Real.log (cA k))).div_atTop log_nat_tendsto_atTop)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  filter_upwards [(lowGaussianBase_tendsto_atTop β hβ).eventually_gt_atTop 0] with n hn
  change (1/2:ℝ)*(Real.log (lowGaussianBase β n)/Real.log (n:ℝ))-Real.log (cA k)/Real.log (n:ℝ)=_
  rw [lowGaussianThreshold,Real.log_div (Real.sqrt_pos.mpr hn).ne' (cA_pos k hk).ne',Real.log_sqrt hn.le]
  ring

theorem lowGaussianThreshold_sq (k β : ℝ) (hk : 2<k) (hβ : 0 ≤ β) (n : ℕ) (hn : 1 ≤ n) :
    (lowGaussianThreshold k β n)^2/2=((k-2)/k)*(Real.log 2+β*Real.log (n:ℝ)) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := zero_lt_one.trans_le hn1
  have hPow : 1 ≤ (n:ℝ)^β := Real.one_le_rpow hn1 hβ
  have hBase : 0 ≤ lowGaussianBase β n := mul_nonneg (by norm_num)
    (Real.log_nonneg (by nlinarith only [hPow]))
  rw [lowGaussianThreshold,div_pow,Real.sq_sqrt hBase,cA_sq k hk,lowGaussianBase_eq β n (by omega)]
  have hk0 : 0<k := by linarith
  have hk2 : 0<k-2 := by linarith
  field_simp
  <;> ring

theorem lowGaussianThreshold_square_over_log_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (fun n : ℕ => ((lowGaussianThreshold k β n)^2/2)/Real.log (n:ℝ)) atTop (𝓝 (((k-2)/k)*β)) := by
  have h := (((tendsto_const_nhds (x:=Real.log (2:ℝ))).div_atTop log_nat_tendsto_atTop).add_const β).const_mul ((k-2)/k)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
  change ((k-2)/k)*(Real.log 2/Real.log (n:ℝ)+β)=_
  rw [lowGaussianThreshold_sq k β hk hβ.le n (by omega)]
  have hlog : Real.log (n:ℝ)≠0 := (Real.log_pos (by exact_mod_cast (show 1<n by omega))).ne'
  field_simp
  <;> ring

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowDegreeTrial -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem pi_all_event_probability {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (N : ℕ) (B : Set E) :
    (Measure.pi (fun _ : Fin N => ν)).real {z | ∀i : Fin N,z i∈B}=(ν.real B)^N := by
  have hs : {z : Fin N→E | ∀i : Fin N,z i∈B}=Set.univ.pi (fun _ : Fin N => B) := by
    ext z
    simp
  rw [hs,measureReal_def,Measure.pi_pi]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,ENNReal.toReal_pow]
  rfl

theorem first_sample_bad_probability {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β : ℝ) (hk : 2 < k) (hβ : 0 ≤ β)
    (hv : OrdinaryVectorColoring G v k) (hn : 0 < n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) :
    gaussProb {g : Space d | (localMax G v Finset.univ g).card<⌊(n:ℝ)*pStarA k β n/2⌋₊} ≤
      1-pStarA k β n/2 := by
  let A : Set (Space d) := {g | (n:ℝ)*pStarA k β n/2 ≤ ((localMax G v Finset.univ g).card:ℝ)}
  have hcardM : Measurable (fun g : Space d => ((localMax G v Finset.univ g).card:ℝ)) :=
    (measurable_of_countable (fun I : Finset (Fin n) => (I.card:ℝ))).comp (measurable_localMax G v Finset.univ)
  have hA : MeasurableSet A := measurableSet_le measurable_const hcardM
  have hp := first_sample_large_probability G v k β hk hβ hv hn hdeg
  have hfloor : (⌊(n:ℝ)*pStarA k β n/2⌋₊:ℝ) ≤ (n:ℝ)*pStarA k β n/2 :=
    Nat.floor_le (by have hp := pStarA_pos k β n; positivity)
  have hsub : {g : Space d | (localMax G v Finset.univ g).card<⌊(n:ℝ)*pStarA k β n/2⌋₊} ⊆ Aᶜ := by
    intro g hg hA
    change (localMax G v Finset.univ g).card<⌊(n:ℝ)*pStarA k β n/2⌋₊ at hg
    change (n:ℝ)*pStarA k β n/2 ≤ ((localMax G v Finset.univ g).card:ℝ) at hA
    have hcast : ((localMax G v Finset.univ g).card:ℝ)<(⌊(n:ℝ)*pStarA k β n/2⌋₊:ℝ) := by exact_mod_cast hg
    linarith
  unfold gaussProb at hp ⊢
  calc
    _ ≤ (stdGaussian (Space d)).real Aᶜ := measureReal_mono hsub
    _ = 1-(stdGaussian (Space d)).real A := probReal_compl_eq_one_sub hA
    _ ≤ _ := by linarith

theorem low_degree_trial_failure {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β : ℝ) (hk : 2 < k) (hβ : 0 ≤ β)
    (hv : OrdinaryVectorColoring G v k) (hn : 2 ≤ n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) :
    (trialLaw n d ⌈2*Real.log 4/pStarA k β n⌉₊).real
      {ω | (trialObtained G v (1/2) ⌊(n:ℝ)*pStarA k β n/2⌋₊ ω).card<⌊(n:ℝ)*pStarA k β n/2⌋₊} ≤ 1/4 := by
  classical
  let p := pStarA k β n
  let T := ⌊(n:ℝ)*p/2⌋₊
  let R := ⌈2*Real.log 4/p⌉₊
  let μ := trialLaw n d R
  let row : (Fin (numLevels n)×Fin R→Space d)→(Fin R→Space d) := fun ω i => ω (⟨0,by
    unfold numLevels
    exact Nat.ceil_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<n by omega)))⟩,i)
  have hℓ : 0<numLevels n := by
    unfold numLevels
    exact Nat.ceil_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<n by omega)))
  let B : Set (Space d) := {g | (localMax G v Finset.univ g).card<T}
  have hB : MeasurableSet B := (Set.to_countable {I : Finset (Fin n) | I.card<T}).measurableSet.preimage
    (measurable_localMax G v Finset.univ)
  have hbp : (stdGaussian (Space d)).real B ≤ 1-p/2 := first_sample_bad_probability G v k β hk hβ hv (by omega) hdeg
  let A := Set.univ.pi (fun _ : Fin R => B)
  have hA : MeasurableSet A := MeasurableSet.univ_pi (fun _ => hB)
  have hsub : {ω | (trialObtained G v (1/2) T ω).card<T} ⊆ row ⁻¹' A := by
    intro ω hω
    change row ω∈A
    simp only [A,Set.mem_univ_pi]
    intro i
    change (localMax G v Finset.univ (row ω i)).card<T
    change (trialObtained G v (1/2) T ω).card<T at hω
    by_contra h
    have hm := sampleSet_mem_alg2Sampled G v (1/2) ω 1 (by omega) hℓ i
    have heq : sampleSet G v (1/2) ω 1 i=localMax G v Finset.univ (row ω i) := by
      unfold sampleSet sampledAt row
      simp only [Nat.sub_self,cores,dif_pos hℓ]
    rw [heq] at hm
    exact (not_le_of_gt hω) (trialObtained_card_of_sample G v (1/2) T ω _ hm (Nat.le_of_not_gt h))
  have hmap : μ.map row=Measure.pi (fun _ : Fin R => stdGaussian (Space d)) := trial_row_map ⟨0,hℓ⟩
  calc
    _ ≤ μ.real (row ⁻¹' A) := measureReal_mono hsub
    _ = (μ.map row).real A := (map_measureReal_apply (by dsimp [row]; fun_prop) hA).symm
    _ = (Measure.pi (fun _ : Fin R => stdGaussian (Space d))).real A := by rw [hmap]
    _ = ((stdGaussian (Space d)).real B)^R := by
      have hs : A={z : Fin R→Space d | ∀i : Fin R,z i∈B} := by ext; simp [A]
      rw [hs,pi_all_event_probability]
    _ ≤ (1-p/2)^R := pow_le_pow_left₀ measureReal_nonneg hbp R
    _ ≤ 1/4 := repeat_low_degree_bound p (pStarA_pos k β n) ((pStarA_le_half k β n).trans (by norm_num))

theorem theorem2_low_degree_failure {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl : ℝ) (hk : 2 < k) (hβ : 0 ≤ β)
    (hreg : β ≤ (k-2)/k) (hv : OrdinaryVectorColoring G v k) (hn : 2 ≤ n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) :
    (trialLaw n d (runsA k β Cl n)).real
      {ω | (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<targetA k β Cl n} ≤ 1/4 := by
  unfold runsA targetA deltaA
  rw [if_pos hreg]
  simp only [if_pos hreg]
  exact low_degree_trial_failure G v k β hk hβ hv hn hdeg

theorem theorem2_low_degree_target_success {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (k β Cl C : ℝ) (hk : 2 < k) (hβ : 0 ≤ β) (hC : 0 < C)
    (hreg : β ≤ (k-2)/k) (hv : OrdinaryVectorColoring G v k) (hn : 2 ≤ n)
    (hdeg : (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β) :
    (thm2Law n d k β Cl (C/Real.log 4)).real
      {ω | IsIndep G (thm2Output G v k β Cl (C/Real.log 4) ω) ∧
        (targetA k β Cl n:ℝ) ≤ ((thm2Output G v k β Cl (C/Real.log 4) ω).card:ℝ)} ≥ 1-(n:ℝ)^(-C) :=
  thm2_amplified_size_bound G v k β Cl C hC (by omega) (targetA k β Cl n) _ le_rfl
    (theorem2_low_degree_failure G v k β Cl hk hβ hreg hv hn hdeg)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowAsymptotics -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem lowDecayRate_properties (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hβ1 : β ≤ 1) :
    0<((k-2)/k)*β ∧ ((k-2)/k)*β<1 := by
  have hk0 : 0<k := by linarith
  have hr : 0<(k-2)/k := div_pos (by linarith) hk0
  have hr1 : (k-2)/k<1 := (div_lt_one hk0).mpr (by linarith)
  have hmul : ((k-2)/k)*β ≤ (k-2)/k := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hβ1 hr.le
  exact ⟨mul_pos hr hβ,hmul.trans_lt hr1⟩

theorem log_low_tail_over_log_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (fun n : ℕ => Real.log (PhiTail (lowGaussianThreshold k β n))/Real.log (n:ℝ)) atTop
      (𝓝 (-(((k-2)/k)*β))) := by
  have hUpper := (lowGaussianThreshold_square_over_log_tendsto k β hk hβ).neg
  have hConst : Tendsto (fun n : ℕ => Real.log millsConstant/Real.log (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_nat_tendsto_atTop
  have hLower := (hUpper.add hConst).sub (log_lowGaussianThreshold_over_log_tendsto k β hk hβ)
  simp only [add_zero,sub_zero] at hLower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · filter_upwards [(lowGaussianThreshold_tendsto_atTop k β hk hβ).eventually_ge_atTop 1,
      log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hu hn
    have h := (div_le_div_iff_of_pos_right hn).mpr (phiTail_log_bounds _ hu).1
    change -((lowGaussianThreshold k β n)^2/2/Real.log (n:ℝ))+Real.log millsConstant/Real.log (n:ℝ)-
      Real.log (lowGaussianThreshold k β n)/Real.log (n:ℝ) ≤ _
    calc
      _ = (-((lowGaussianThreshold k β n)^2/2)+Real.log millsConstant-Real.log (lowGaussianThreshold k β n))/Real.log (n:ℝ) := by ring
      _ ≤ _ := h
  · filter_upwards [(lowGaussianThreshold_tendsto_atTop k β hk hβ).eventually_ge_atTop 1,
      log_nat_tendsto_atTop.eventually_gt_atTop 0] with n hu hn
    have h := (div_le_div_iff_of_pos_right hn).mpr (phiTail_log_bounds _ hu).2
    change _ ≤ -((lowGaussianThreshold k β n)^2/2/Real.log (n:ℝ))
    simpa only [neg_div] using h

theorem log_pStarA_over_log_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (fun n : ℕ => Real.log (pStarA k β n)/Real.log (n:ℝ)) atTop (𝓝 (-(((k-2)/k)*β))) := by
  have h := (log_low_tail_over_log_tendsto k β hk hβ).sub
    ((tendsto_const_nhds (x:=Real.log (2:ℝ))).div_atTop log_nat_tendsto_atTop)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with n
  change Real.log (PhiTail (lowGaussianThreshold k β n))/Real.log (n:ℝ)-Real.log 2/Real.log (n:ℝ)=_
  have he : pStarA k β n=PhiTail (lowGaussianThreshold k β n)/2 := rfl
  rw [he,Real.log_div (phiTail_pos _).ne' (by norm_num : (2:ℝ)≠0)]
  ring

def lowExpectedSize (k β : ℝ) (n : ℕ) : ℝ := (n:ℝ)*pStarA k β n/2

theorem log_lowExpectedSize_over_log_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) :
    Tendsto (fun n : ℕ => Real.log (lowExpectedSize k β n)/Real.log (n:ℝ)) atTop
      (𝓝 (1-((k-2)/k)*β)) := by
  have h := ((log_pStarA_over_log_tendsto k β hk hβ).const_add 1).sub
    ((tendsto_const_nhds (x:=Real.log (2:ℝ))).div_atTop log_nat_tendsto_atTop)
  have hlim : 1 + -(((k-2)/k)*β)-0=1-((k-2)/k)*β := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [log_nat_tendsto_atTop.eventually_gt_atTop 0,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  change 1+Real.log (pStarA k β n)/Real.log (n:ℝ)-Real.log 2/Real.log (n:ℝ)=_
  rw [lowExpectedSize,Real.log_div (mul_pos hn0 (pStarA_pos k β n)).ne' (by norm_num : (2:ℝ)≠0),
    Real.log_mul hn0.ne' (pStarA_pos k β n).ne']
  field_simp
  <;> ring

theorem lowExpectedSize_tendsto_atTop (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hβ1 : β ≤ 1) :
    Tendsto (lowExpectedSize k β) atTop atTop := by
  have hLog := tendsto_atTop_of_ratio_log (fun n => Real.log (lowExpectedSize k β n))
    (1-((k-2)/k)*β) (by linarith [(lowDecayRate_properties k β hk hβ hβ1).2])
    (log_lowExpectedSize_over_log_tendsto k β hk hβ)
  have h := Real.tendsto_exp_atTop.comp hLog
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  change Real.exp (Real.log (lowExpectedSize k β n))=lowExpectedSize k β n
  apply Real.exp_log
  exact div_pos (mul_pos (by exact_mod_cast (show 0<n by omega)) (pStarA_pos k β n)) (by norm_num)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowSize -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def lowSizeGap (k β : ℝ) (n : ℕ) : ℝ :=
  -(((k-2)/k)*β)-Real.log (pStarA k β n/4)/Real.log (n:ℝ)

theorem lowSizeGap_tendsto (k β : ℝ) (hk : 2<k) (hβ : 0<β) : IsLittleO1 (lowSizeGap k β) := by
  have hRatio := (log_pStarA_over_log_tendsto k β hk hβ).sub
    ((tendsto_const_nhds (x:=Real.log (4:ℝ))).div_atTop log_nat_tendsto_atTop)
  have h := (tendsto_const_nhds (x:=-(((k-2)/k)*β))).sub hRatio
  simp only [sub_zero,sub_self] at h
  apply h.congr'
  filter_upwards [] with n
  change -(((k-2)/k)*β)-(Real.log (pStarA k β n)/Real.log (n:ℝ)-Real.log 4/Real.log (n:ℝ))=_
  rw [lowSizeGap,Real.log_div (pStarA_pos k β n).ne' (by norm_num : (4:ℝ)≠0)]
  ring

theorem low_size_power_identity (k β : ℝ) (hreg : β ≤ (k-2)/k) (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ)^(thm2Exponent k β-lowSizeGap k β n)=lowExpectedSize k β n/2 := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hnLog : Real.log (n:ℝ)≠0 := (Real.log_pos hn1).ne'
  rw [Real.rpow_def_of_pos hn0]
  have he : Real.log (n:ℝ)*(thm2Exponent k β-lowSizeGap k β n)=
      Real.log (n:ℝ)+Real.log (pStarA k β n/4) := by
    rw [thm2Exponent,if_pos hreg,lowSizeGap]
    field_simp
    <;> ring
  rw [he,Real.exp_add,Real.exp_log hn0,Real.exp_log (div_pos (pStarA_pos k β n) (by norm_num))]
  unfold lowExpectedSize
  ring

theorem low_target_size_bound_eventually (k β Cl : ℝ) (hk : 2<k) (hβ : 0<β)
    (hβ1 : β ≤ 1) (hreg : β ≤ (k-2)/k) :
    ∀ᶠ n : ℕ in atTop,(n:ℝ)^(thm2Exponent k β-lowSizeGap k β n) ≤ (targetA k β Cl n:ℝ) := by
  filter_upwards [(lowExpectedSize_tendsto_atTop k β hk hβ hβ1).eventually_ge_atTop 2,eventually_ge_atTop (2:ℕ)] with n hx hn
  rw [low_size_power_identity k β hreg n hn,targetA,if_pos hreg]
  change lowExpectedSize k β n/2 ≤ (⌊lowExpectedSize k β n⌋₊:ℝ)
  have h := Nat.lt_floor_add_one (lowExpectedSize k β n)
  nlinarith only [h,hx]

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowCalls -/

set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem pStarA_inverse_le_square_eventually (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hβ1 : β ≤ 1) :
    ∀ᶠ n : ℕ in atTop,(pStarA k β n)⁻¹ ≤ (n:ℝ)^2 := by
  have hDecay := lowDecayRate_properties k β hk hβ hβ1
  have hr := (log_pStarA_over_log_tendsto k β hk hβ).eventually_const_lt
    (show (-2:ℝ)< -(((k-2)/k)*β) by linarith only [hDecay.2])
  filter_upwards [hr,eventually_ge_atTop (2:ℕ)] with n hr hn
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : 0<(n:ℝ) := by linarith
  have hscaled := (lt_div_iff₀ (Real.log_pos hn1)).mp hr
  have hNpow : Real.exp (2*Real.log (n:ℝ))=(n:ℝ)^2 := by
    rw [show (2:ℝ)*Real.log (n:ℝ)=(2:ℕ)*Real.log (n:ℝ) by norm_num,Real.exp_nat_mul,Real.exp_log hn0]
  calc
    (pStarA k β n)⁻¹=Real.exp (-Real.log (pStarA k β n)) := by rw [Real.exp_neg,Real.exp_log (pStarA_pos k β n)]
    _ ≤ Real.exp (2*Real.log (n:ℝ)) := Real.exp_le_exp.mpr (by linarith only [hscaled])
    _ = _ := hNpow

theorem low_runs_le_pow_eight_eventually (k β Cl : ℝ) (hk : 2<k) (hβ : 0<β)
    (hβ1 : β ≤ 1) (hreg : β ≤ (k-2)/k) :
    ∀ᶠ n : ℕ in atTop,(runsA k β Cl n:ℝ) ≤ (n:ℝ)^8 := by
  filter_upwards [pStarA_inverse_le_square_eventually k β hk hβ hβ1,eventually_ge_atTop (2:ℕ),
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (2*Real.log 4+1)] with n hp hn hN
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hLog4 : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  have hRaw : 2*Real.log 4/pStarA k β n ≤ (2*Real.log 4)*(n:ℝ)^2 := by
    simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hp (show 0 ≤ 2*Real.log 4 by positivity)
  have hCeil : (runsA k β Cl n:ℝ) ≤ 2*Real.log 4/pStarA k β n+1 := by
    rw [runsA,if_pos hreg]
    exact (Nat.ceil_lt_add_one (div_nonneg (by positivity) (pStarA_pos k β n).le)).le
  have h2 : (1:ℝ) ≤ (n:ℝ)^2 := one_le_pow₀ hn1
  calc
    (runsA k β Cl n:ℝ) ≤ (2*Real.log 4)*(n:ℝ)^2+1 := by linarith only [hRaw,hCeil]
    _ ≤ (2*Real.log 4+1)*(n:ℝ)^2 := by nlinarith only [h2]
    _ ≤ (n:ℝ)*(n:ℝ)^2 := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = (n:ℝ)^3 := by ring
    _ ≤ (n:ℝ)^8 := pow_le_pow_right₀ hn1 (by norm_num)

theorem low_calls_polynomial (k β Cl cT : ℝ) (hk : 2<k) (hβ : 0<β) (hβ1 : β ≤ 1)
    (hreg : β ≤ (k-2)/k) (hcT : 0<cT) :
    ∃K : ℝ,∀n : ℕ,(thm2Calls k β Cl cT n:ℝ) ≤ K*(n:ℝ)^K+K :=
  thm2Calls_polynomial_of_runs k β Cl cT hcT (low_runs_le_pow_eight_eventually k β Cl hk hβ hβ1 hreg)

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxLowTheorem -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem theorem_2_low (k β : ℝ) (hk : 2<k) (hβ : 0<β) (hβ1 : β ≤ 1) (hreg : β ≤ (k-2)/k)
    (C : ℝ) (hC : 0<C) :
    ∃(Cl cT : ℝ)(g : ℕ→ℝ),0<cT ∧ IsLittleO1 g ∧
      (∃K : ℝ,∀n : ℕ,(thm2Calls k β Cl cT n:ℝ) ≤ K*(n:ℝ)^K+K) ∧
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
        (thm2Law n d k β Cl cT).real
          {ω | IsIndep G (thm2Output G v k β Cl cT ω) ∧
            (n:ℝ)^(thm2Exponent k β-g n) ≤ ((thm2Output G v k β Cl cT ω).card:ℝ)} ≥ 1-(n:ℝ)^(-C) := by
  let Cl : ℝ := 0
  let cT := C/Real.log 4
  have hcT : 0<cT := div_pos hC (Real.log_pos (by norm_num))
  have hCalls := low_calls_polynomial k β Cl cT hk hβ hβ1 hreg hcT
  have hEventually : ∀ᶠ n : ℕ in atTop,∀d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,
      OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ:ℝ) ≤ (n:ℝ)^β →
      (n:ℝ)^(thm2Exponent k β-lowSizeGap k β n) ≤ (targetA k β Cl n:ℝ) ∧
      (trialLaw n d (runsA k β Cl n)).real {ω |
        (trialObtained G v (deltaA k β Cl n) (targetA k β Cl n) ω).card<targetA k β Cl n} ≤ 1/4 := by
    filter_upwards [low_target_size_bound_eventually k β Cl hk hβ hβ1 hreg,eventually_ge_atTop (2:ℕ)] with n hSize hn
    intro d G v hv hdeg
    exact ⟨hSize,theorem2_low_degree_failure G v k β Cl hk hβ.le hreg hv hn hdeg⟩
  obtain ⟨g,hg,hResult⟩ := theorem2_assemble k β Cl C hC (lowSizeGap k β) (lowSizeGap_tendsto k β hk hβ) hEventually
  exact ⟨Cl,cT,g,hcT,hg,hCalls,hResult⟩

end
end GaussLocalMaxColoring.Main

/- Bundled module: Solutions.GaussLocalMaxTheorem2 -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem theorem_2 (k β : ℝ) (hk : 2 < k) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (C : ℝ) (hC : 0 < C) :
    ∃ (Cl cT : ℝ) (g : ℕ → ℝ), 0 < cT ∧ IsLittleO1 g ∧
      (∃ K : ℝ, ∀ n : ℕ, (thm2Calls k β Cl cT n : ℝ) ≤ K * (n : ℝ) ^ K + K) ∧
      ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n → Space d),
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ β →
        (thm2Law n d k β Cl cT).real
            {ω | IsIndep G (thm2Output G v k β Cl cT ω) ∧
              (n : ℝ) ^ (thm2Exponent k β - g n) ≤ ((thm2Output G v k β Cl cT ω).card : ℝ)}
          ≥ 1 - (n : ℝ) ^ (-C) := by
  by_cases hreg : β ≤ (k-2)/k
  · exact theorem_2_low k β hk hβ0 hβ1 hreg C hC
  · exact theorem_2_high k β hk hβ0 (lt_of_not_ge hreg) C hC

end
end GaussLocalMaxColoring.Main


open GaussLocalMaxColoring.Main
theorem solution (k β : ℝ) (hk : 2 < k) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (C : ℝ) (hC : 0 < C) :
    ∃ (Cl cT : ℝ) (g : ℕ → ℝ), 0 < cT ∧ IsLittleO1 g ∧
      (∃ K : ℝ, ∀ n : ℕ, (thm2Calls k β Cl cT n : ℝ) ≤ K * (n : ℝ) ^ K + K) ∧
      ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) (v : Fin n → Space d),
        OrdinaryVectorColoring G v k → (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ β →
        (thm2Law n d k β Cl cT).real
            {ω | IsIndep G (thm2Output G v k β Cl cT ω) ∧
              (n : ℝ) ^ (thm2Exponent k β - g n) ≤ ((thm2Output G v k β Cl cT ω).card : ℝ)}
          ≥ 1 - (n : ℝ) ^ (-C) := GaussLocalMaxColoring.Main.theorem_2 k β hk hβ0 hβ1 C hC
