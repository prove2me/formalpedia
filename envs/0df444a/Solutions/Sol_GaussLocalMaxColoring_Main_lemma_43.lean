-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_43
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T20:08:21.304208+00:00
-- url     : https://prove2.me/submissions/38f4e166-ee4f-4391-bb42-78a2b926734a

import Definitions.Def_GaussLocalMaxColoring_Main_Bands
import Definitions.Def_GaussLocalMaxColoring_Main_Basic
import Definitions.Def_GaussLocalMaxColoring_Main_Section5
import Definitions.Def_GaussLocalMaxColoring_Main_VectorRounding
import Mathlib
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_29

set_option autoImplicit false
set_option maxHeartbeats 2200000


-- Source module: Solutions.GaussLocalMaxImprovedDrift
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

def improvedNu : ℝ := 437/2000

def improvedPsi (s : ℝ) : ℝ :=
  if s ≤ improvedNu then Real.sqrt 3*Real.sqrt (1-s^2)
  else Real.sqrt 3*(1-improvedNu*s)/Real.sqrt (1-improvedNu^2)

theorem improved_nu_pos : 0 < improvedNu := by norm_num [improvedNu]
theorem improved_nu_lt_one : improvedNu < 1 := by norm_num [improvedNu]

theorem improved_drift (U : ℝ) (hU0 : 0 ≤ U) (hUH : U ≤ Real.sqrt H5) :
    U/2+1/1500 ≤ Real.sqrt 3/2*improvedPsi (Real.sqrt (H5-U^2)) := by
  have hH : 0 ≤ H5 := by norm_num [H5,H0,beta5,eta5]
  have hHsmall : H5 < (13/5:ℝ)^2 := by norm_num [H5,H0,beta5,eta5]
  have hHU : U ≤ 13/5 := hUH.trans (Real.sqrt_le_iff.mpr ⟨by norm_num,hHsmall.le⟩)
  have hU2 : U^2 ≤ H5 := by
    have hm := pow_le_pow_left₀ hU0 hUH 2
    rwa [Real.sq_sqrt hH] at hm
  let s : ℝ := Real.sqrt (H5-U^2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s^2=H5-U^2 := Real.sq_sqrt (sub_nonneg.mpr hU2)
  have hrt3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  change U/2+1/1500 ≤ Real.sqrt 3/2*improvedPsi s
  unfold improvedPsi
  split
  · rename_i hsν
    have hprod := mul_nonneg (sub_nonneg.mpr hsν) (add_nonneg improved_nu_pos.le hs0)
    have hrad : (9/10:ℝ)^2 ≤ 1-s^2 := by
      have hν2 : improvedNu^2 < (1/10:ℝ) := by norm_num [improvedNu]
      nlinarith only [hprod,hν2]
    have hr := Real.le_sqrt_of_sq_le hrad
    have hmul : Real.sqrt 3/2*(Real.sqrt 3*Real.sqrt (1-s^2))=3/2*Real.sqrt (1-s^2) := by
      nlinarith only [congrArg (fun x : ℝ => x*Real.sqrt (1-s^2)) hrt3]
    rw [hmul]
    linarith only [hr,hHU]
  · rename_i hsν
    let a : ℝ := Real.sqrt (1-improvedNu^2)
    have haRad : 0 < 1-improvedNu^2 := by norm_num [improvedNu]
    have ha : 0 < a := Real.sqrt_pos.mpr haRad
    have ha2 : a^2=1-improvedNu^2 := Real.sq_sqrt haRad.le
    have ha1 : a ≤ 1 := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨by norm_num,by have h := sq_nonneg improvedNu; linarith only [h]⟩
    have hCS : (a*U+3*improvedNu*s)^2 ≤ (1+8*improvedNu^2)*H5 := by
      have hh := sq_nonneg (a*s-3*improvedNu*U)
      have hid : (a*U+3*improvedNu*s)^2+(a*s-3*improvedNu*U)^2=
          (a^2+9*improvedNu^2)*(U^2+s^2) := by ring
      rw [ha2,show U^2+s^2=H5 by linarith only [hs2]] at hid
      nlinarith only [hh,hid]
    have hNum : (1+8*improvedNu^2)*H5 ≤ (3-1/750:ℝ)^2 := by
      norm_num [improvedNu,H5,H0,beta5,eta5]
    have hupper : a*U+3*improvedNu*s ≤ 3-1/750 := by
      nlinarith only [hCS,hNum]
    have htarget : (U+1/750)*a ≤ 3*(1-improvedNu*s) := by
      nlinarith only [hupper,ha1]
    have hid : Real.sqrt 3/2*(Real.sqrt 3*(1-improvedNu*s)/a)=3*(1-improvedNu*s)/(2*a) := by
      apply (eq_div_iff (mul_ne_zero (by norm_num) ha.ne')).mpr
      calc
        Real.sqrt 3/2*(Real.sqrt 3*(1-improvedNu*s)/a)*(2*a) =
            (Real.sqrt 3)^2*(1-improvedNu*s)*(a/a) := by ring
        _ = 3*(1-improvedNu*s) := by rw [div_self ha.ne',mul_one,hrt3]
    rw [hid]
    apply (le_div_iff₀ (mul_pos (by norm_num) ha)).mpr
    nlinarith only [htarget]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxImprovedOptimization
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem improved_flat_optimization (x y s : ℝ) (hy : 0 ≤ y) (hs : 0 ≤ s)
    (hsq : s^2=x^2+y^2) (hS : s ≤ Real.sqrt H5) :
    ∃a b μ c κ θ : ℝ,
      Real.sqrt (1-improvedNu^2) ≤ a ∧ |b| ≤ improvedNu ∧ 0 ≤ μ ∧ μ ≤ improvedNu ∧
      0 ≤ c ∧ 0 ≤ κ ∧ 0 ≤ θ ∧ θ ≤ 4 ∧ a^2+b^2+μ^2=1 ∧
      c^2+κ^2 ≤ (499/1000:ℝ)^2 ∧ μ+θ*(μ+κ)=y ∧
      |x-(1+θ)*b| ≤ θ*c ∧ improvedPsi s ≤ (1+θ)*Real.sqrt 3*a-(1968/1000)*θ := by
  let ν : ℝ := improvedNu
  let q : ℝ := 499/1000
  have hν : 0 < ν := improved_nu_pos
  have hν1 : ν < 1 := improved_nu_lt_one
  have hq : 0 < q := by norm_num [q]
  have hden : 0 < ν+q := add_pos hν hq
  have haArg : 0 < 1-ν^2 := by norm_num [ν,improvedNu]
  have ha : 0 < Real.sqrt (1-ν^2) := Real.sqrt_pos.mpr haArg
  have ha2 : (Real.sqrt (1-ν^2))^2=1-ν^2 := Real.sq_sqrt haArg.le
  have hrt3 : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hx : |x| ≤ s := by apply abs_le.mpr; constructor <;> nlinarith only [hsq,hs,sq_nonneg y]
  have hyS : y ≤ s := by nlinarith only [hsq,hs,hy,sq_nonneg x]
  by_cases hsmall : s ≤ ν
  · have hsArg : 0 ≤ 1-s^2 := by nlinarith only [hsmall,hν1,hs]
    refine ⟨Real.sqrt (1-s^2),x,y,0,0,0,?_,hx.trans hsmall,hy,hyS.trans hsmall,le_rfl,le_rfl,le_rfl,by norm_num,?_,by norm_num,?_,?_,?_⟩
    · exact Real.sqrt_le_sqrt (by nlinarith only [hsmall,hs,hν])
    · rw [Real.sq_sqrt hsArg]
      nlinarith only [hsq]
    · ring
    · simp
    · unfold improvedPsi
      rw [if_pos hsmall]
      simp
  · have hsν : ν < s := lt_of_not_ge hsmall
    have hs0 : 0 < s := hν.trans hsν
    let a := Real.sqrt (1-ν^2)
    let b := ν*x/s
    let μ := ν*y/s
    let c := q*|x|/s
    let κ := q*y/s
    let θ := (s-ν)/(ν+q)
    have hθ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr hsν.le) hden.le
    have hθeq : θ*(ν+q)=s-ν := div_mul_cancel₀ _ hden.ne'
    have hSbound : Real.sqrt H5 ≤ 13/5 := by
      apply Real.sqrt_le_iff.mpr
      norm_num [H5,H0,beta5,eta5]
    have hθ4 : θ ≤ 4 := by
      apply (div_le_iff₀ hden).mpr
      have hsb := hS.trans hSbound
      have hnq : (13/5:ℝ)-ν ≤ 4*(ν+q) := by norm_num [ν,q,improvedNu]
      exact (sub_le_sub_right hsb ν).trans hnq
    have hμ : 0 ≤ μ := by dsimp only [μ]; positivity
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
    have hbμ : b^2+μ^2=ν^2 := by
      dsimp only [b,μ]
      field_simp [hs0.ne']
      nlinarith only [hsq]
    have hb : |b| ≤ ν := by apply abs_le.mpr; constructor <;> nlinarith only [hbμ,hν,sq_nonneg μ]
    have hμν : μ ≤ ν := by nlinarith only [hbμ,hν,hμ,sq_nonneg b]
    have hcκ : c^2+κ^2=q^2 := by
      dsimp only [c,κ]
      rw [div_pow,div_pow,mul_pow,mul_pow,sq_abs]
      rw [←add_div]
      apply (div_eq_iff (pow_ne_zero 2 hs0.ne')).mpr
      nlinarith only [congrArg (fun z : ℝ => q^2*z) hsq]
    have htarget : μ+θ*(μ+κ)=y := by
      dsimp only [μ,κ]
      field_simp [hs0.ne']
      nlinarith only [congrArg (fun z : ℝ => y*z) hθeq]
    have hxEq : x-(1+θ)*b=θ*q*x/s := by
      dsimp only [b]
      field_simp [hs0.ne']
      nlinarith only [congrArg (fun z : ℝ => x*z) hθeq]
    have hcancel : |x-(1+θ)*b| ≤ θ*c := by
      rw [hxEq,abs_div,abs_mul,abs_mul,abs_of_nonneg hθ,abs_of_pos hq,abs_of_pos hs0]
      dsimp only [c]
      exact le_of_eq (by ring)
    have hA : (1968/1000:ℝ)*a ≤ Real.sqrt 3*(1+q*ν) := by
      have hn : (1968/1000:ℝ)^2*(1-ν^2) ≤ 3*(1+q*ν)^2 := by norm_num [ν,q,improvedNu]
      have hsLeft : ((1968/1000:ℝ)*a)^2=(1968/1000:ℝ)^2*(1-ν^2) := by rw [mul_pow,ha2]
      have hsRight : (Real.sqrt 3*(1+q*ν))^2=3*(1+q*ν)^2 := by rw [mul_pow,hrt3]
      have hright : 0 < Real.sqrt 3*(1+q*ν) := by positivity
      apply (sq_le_sq₀ (by positivity) hright.le).mp
      rw [hsLeft,hsRight]
      exact hn
    have hthreshold : improvedPsi s ≤ (1+θ)*Real.sqrt 3*a-(1968/1000)*θ := by
      unfold improvedPsi
      rw [if_neg hsmall]
      change Real.sqrt 3*(1-ν*s)/a ≤ _
      apply (div_le_iff₀ ha).mpr
      have he : ((1+θ)*Real.sqrt 3*a-(1968/1000)*θ)*a =
          Real.sqrt 3*(1-ν*s)+θ*(Real.sqrt 3*(1+q*ν)-(1968/1000)*a) := by
        have haSq : a^2=1-ν^2 := ha2
        calc
          ((1+θ)*Real.sqrt 3*a-(1968/1000)*θ)*a =
              (1+θ)*Real.sqrt 3*a^2-(1968/1000)*θ*a := by ring
          _ = (1+θ)*Real.sqrt 3*(1-ν^2)-(1968/1000)*θ*a := by rw [haSq]
          _ = Real.sqrt 3*(1-ν*(ν+θ*(ν+q)))+θ*(Real.sqrt 3*(1+q*ν)-(1968/1000)*a) := by ring
          _ = Real.sqrt 3*(1-ν*s)+θ*(Real.sqrt 3*(1+q*ν)-(1968/1000)*a) := by
            rw [show ν+θ*(ν+q)=s by linarith only [hθeq]]
      rw [he]
      exact le_add_of_nonneg_right (mul_nonneg hθ (sub_nonneg.mpr hA))
    refine ⟨a,b,μ,c,κ,θ,le_rfl,hb,hμ,hμν,hc,hκ,hθ,hθ4,?_,?_,htarget,hcancel,hthreshold⟩
    · dsimp only [a]
      rw [ha2]
      linarith only [hbμ]
    · exact hcκ.le

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxGeometry
section
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

end


-- Source module: Solutions.GaussLocalMaxGaussian
section
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

end


-- Source module: Solutions.GaussLocalMaxGaussianBlocks
section
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

end


-- Source module: Solutions.GaussLocalMaxGaussianBox
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryGeometry
section
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

end


-- Source module: Solutions.GaussLocalMaxOrthogonalProjection
section
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

end


-- Source module: Solutions.GaussLocalMaxTail
section
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

end


-- Source module: Solutions.GaussLocalMaxProbability
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryProbability
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryBox
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryPlane
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedGeometry
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem ExactSDPVectors.strict {n d : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n→Space d}
    (hv : ExactSDPVectors G v) : StrictVectorColoring G v := ⟨hv.1,hv.2.2.1⟩

theorem ExactSDPVectors.ordinary {n d : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n→Space d}
    (hv : ExactSDPVectors G v) : OrdinaryVectorColoring G v 3 := by
  refine ⟨hv.1,?_⟩
  intro x y hxy
  rw [hv.2.2.1 x y hxy]
  norm_num

theorem cA_three : cA 3=Real.sqrt 3 := by norm_num [cA]

theorem strict_ordinaryResidual_three_eq {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (hv : StrictVectorColoring G v) (x y : Fin n) (hxy : G.Adj x y) :
    ordinaryResidual 3 v x y=residual v x y := by
  have hroot : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hcoef : cA 3/(1-(-(1/2):ℝ))=2/Real.sqrt 3 := by
    rw [cA_three]
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)]
  rw [strict_edge_residual_eq G v hv x y hxy,ordinaryResidual,hv.2 x y hxy,hcoef,neg_smul,sub_neg_eq_add]

theorem strict_nbrMax_eq_ordinary {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (hv : StrictVectorColoring G v) (F : Finset (Fin n)) (x : Fin n) (g : Space d) :
    nbrMax G v F x g=ordinaryNbrMax G v 3 F x g := by
  classical
  apply Finset.sup_congr rfl
  intro y hy
  rw [strict_ordinaryResidual_three_eq G v hv x y (Finset.mem_filter.mp hy).2]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxImprovedPolytope
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_shifted_polytope_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (u e : Space d) (hu : ‖u‖=1) (he : ‖e‖=1) (hue : ⟪u,e⟫=0)
    (z : ι→Space d) (huz : ∀i,⟪u,z i⟫=0) (hez : ∀i,⟪e,z i⟫=0)
    (ξ : ι→ℝ) (A c t : ℝ) :
    1-gaussProb {g : Space d | ∀i,⟪g,z i⟫  ≤  (A-c*|ξ i|)*t}  ≤ 
      gaussProb {g : Space d | ∃i,A*t < ⟪g,ξ i • e+z i⟫}/PhiTail (c*t) := by
  classical
  let F : Space d→(ι→ℝ) := fun g i => ⟪z i,g⟫
  let B : Set (ι→ℝ) := {w | ∃i,(A-c*|ξ i|)*t < w i}
  let Bp : Set (ι→ℝ) := {w | ∃i,0  ≤  ξ i ∧ (A-c*ξ i)*t < w i}
  let Bm : Set (ι→ℝ) := B\Bp
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have hB : MeasurableSet B := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro i
    exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const (measurable_pi_apply i))
  have hBp : MeasurableSet Bp := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro i
    by_cases hi : 0  ≤  ξ i
    · simpa only [hi,true_and] using measurableSet_setOfPred.mp
        (measurableSet_lt measurable_const (measurable_pi_apply i))
    · simp only [hi,false_and]
      exact measurable_const
  have hBm : MeasurableSet Bm := hB.diff hBp
  have hpSub : Bp⊆B := by
    intro w hw
    obtain ⟨i,hi,hwi⟩ := hw
    exact ⟨i,by simpa only [abs_of_nonneg hi] using hwi⟩
  let Ep : Set (Space d) := {g | (⟪u,g⟫∈Set.univ ∧ ⟪e,g⟫∈Set.Ioi (c*t)) ∧ F g∈Bp}
  let Em : Set (Space d) := {g | (⟪u,g⟫∈Set.univ ∧ ⟪-e,g⟫∈Set.Ioi (c*t)) ∧ F g∈Bm}
  have hEm : MeasurableSet Em := by
    have hm : MeasurableSet {g : Space d | c*t < ⟪-e,g⟫} := measurableSet_lt measurable_const (by fun_prop)
    convert hm.inter (hBm.preimage hF) using 1
    ext g
    simp only [Em,Set.mem_setOf_eq,Set.mem_inter_iff,Set.mem_preimage,Set.mem_univ,true_and,Set.mem_Ioi]
  have hdis : Disjoint Ep Em := by
    apply Set.disjoint_left.mpr
    intro g hp hm
    exact hm.2.2 hp.2
  have hfacp := gaussian_coordinate_box_factor u e hu he hue z huz hez Set.univ (Set.Ioi (c*t))
    MeasurableSet.univ measurableSet_Ioi Bp hBp
  have hfacm := gaussian_coordinate_box_factor u (-e) hu (by simpa only [norm_neg] using he)
    (by simpa only [inner_neg_right,neg_zero] using congrArg Neg.neg hue) z huz
    (fun i => by rw [inner_neg_left,hez i,neg_zero]) Set.univ (Set.Ioi (c*t))
    MeasurableSet.univ measurableSet_Ioi Bm hBm
  have hfacp' : gaussProb Ep=PhiTail (c*t)*gaussProb (F⁻¹'Bp) := by
    simpa only [Ep,F,gaussProb,probReal_univ,one_mul,phiTail_eq_Ioi,Set.preimage] using hfacp
  have hfacm' : gaussProb Em=PhiTail (c*t)*gaussProb (F⁻¹'Bm) := by
    simpa only [Em,F,gaussProb,probReal_univ,one_mul,phiTail_eq_Ioi,Set.preimage] using hfacm
  have hsplit : F⁻¹'B=(F⁻¹'Bp)∪(F⁻¹'Bm) := by
    ext g
    change F g∈B ↔ F g∈Bp ∨ F g∈B∧F g∉Bp
    constructor
    · intro hg
      by_cases hp : F g∈Bp
      · exact Or.inl hp
      · exact Or.inr ⟨hg,hp⟩
    · rintro (hp|hm)
      · exact hpSub hp
      · exact hm.1
  have hdataDis : Disjoint (F⁻¹'Bp) (F⁻¹'Bm) := by
    apply Set.disjoint_left.mpr
    intro g hp hm
    exact hm.2 hp
  have hdata : gaussProb (F⁻¹'B)=gaussProb (F⁻¹'Bp)+gaussProb (F⁻¹'Bm) := by
    unfold gaussProb
    rw [hsplit,measureReal_union hdataDis (hBm.preimage hF)]
  have hsub : Ep∪Em⊆{g : Space d | ∃i,A*t < ⟪g,ξ i • e+z i⟫} := by
    intro g hg
    rcases hg with hp|hm
    · obtain ⟨i,hξ,hi⟩ := hp.2
      refine ⟨i,?_⟩
      have hx := mul_le_mul_of_nonneg_left hp.1.2.le hξ
      change (A-c*ξ i)*t < ⟪z i,g⟫ at hi
      rw [inner_add_right,real_inner_smul_right,real_inner_comm e g,real_inner_comm (z i) g]
      nlinarith only [hx,hi]
    · obtain ⟨i,hi⟩ := hm.2.1
      have hξ : ξ i < 0 := by
        by_contra hn
        have hξ0 : 0  ≤  ξ i := le_of_not_gt hn
        apply hm.2.2
        exact ⟨i,hξ0,by simpa only [abs_of_nonneg hξ0] using hi⟩
      have hx := mul_le_mul_of_nonneg_left hm.1.2.le (neg_nonneg.mpr hξ.le)
      rw [inner_neg_left] at hx
      change (A-c*|ξ i|)*t < ⟪z i,g⟫ at hi
      rw [abs_of_neg hξ] at hi
      refine ⟨i,?_⟩
      rw [inner_add_right,real_inner_smul_right,real_inner_comm e g,real_inner_comm (z i) g]
      nlinarith only [hx,hi]
  have hsmall : PhiTail (c*t)*gaussProb (F⁻¹'B)  ≤  gaussProb {g : Space d | ∃i,A*t < ⟪g,ξ i • e+z i⟫} := by
    calc
      PhiTail (c*t)*gaussProb (F⁻¹'B) = gaussProb Ep+gaussProb Em := by rw [hdata,mul_add,hfacp',hfacm']
      _ = gaussProb (Ep∪Em) := (measureReal_union hdis hEm).symm
      _  ≤  _ := measureReal_mono hsub (measure_ne_top _ _)
  have hK : MeasurableSet {g : Space d | ∀i,⟪g,z i⟫  ≤  (A-c*|ξ i|)*t} := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.forall
    intro i
    exact measurableSet_setOfPred.mp (measurableSet_le (by fun_prop) measurable_const)
  have heq : F⁻¹'B={g : Space d | ∀i,⟪g,z i⟫  ≤  (A-c*|ξ i|)*t}ᶜ := by
    ext g
    simp only [F,B,Set.mem_preimage,Set.mem_setOf_eq,Set.mem_compl_iff,not_forall,not_le,real_inner_comm]
  rw [heq,gaussProb,probReal_compl_eq_one_sub hK] at hsmall
  apply (le_div_iff₀ (phiTail_pos (c*t))).mpr
  simpa only [mul_comm,gaussProb] using hsmall

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxMills
section
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

end


-- Source module: Solutions.GaussLocalMaxUniformTail
section
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

end


-- Source module: Solutions.GaussLocalMaxTailShift
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverIntegral
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedTailProduct
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem phiTail_quarter_product_eventually :
    ∃t₀ : ℝ, 1 ≤ t₀ ∧ ∀t : ℝ, t₀ ≤ t → ∀c κ : ℝ,
      0 ≤ c → 0 ≤ κ → c^2+κ^2 ≤ 1/4 →
      (t^4)⁻¹*PhiTail (t/2) ≤ PhiTail (c*t)*PhiTail (κ*t) := by
  refine ⟨max 1 (1/uniformMillsConstant),le_max_left _ _,?_⟩
  intro t ht c κ hc hκ hsq
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hC : 0 < uniformMillsConstant := uniformMillsConstant_pos
  have hCt : 1 ≤ uniformMillsConstant*t := by
    have hh : 1/uniformMillsConstant ≤ t := (le_max_right _ _).trans ht
    have hm := (div_le_iff₀ hC).mp hh
    simpa only [mul_comm] using hm
  have hc1 : c ≤ 1 := by nlinarith only [hsq,hc,sq_nonneg κ]
  have hκ1 : κ ≤ 1 := by nlinarith only [hsq,hκ,sq_nonneg c]
  have hlowC := phiTail_uniform_lower c t hc hc1 ht1
  have hlowK := phiTail_uniform_lower κ t hκ hκ1 ht1
  have hprod := mul_le_mul hlowC hlowK (by positivity) (phiTail_nonneg (c*t))
  have hid : (((1/t)*uniformMillsConstant)*Real.exp (-((c*t)^2/2)))*
      (((1/t)*uniformMillsConstant)*Real.exp (-((κ*t)^2/2))) =
      ((1/t)*uniformMillsConstant)^2*Real.exp (-((c^2+κ^2)*t^2/2)) := by
    rw [show -((c^2+κ^2)*t^2/2)=-((c*t)^2/2)+ -((κ*t)^2/2) by ring,Real.exp_add]
    ring
  rw [hid] at hprod
  have hscalar : (t^4)⁻¹ ≤ ((1/t)*uniformMillsConstant)^2 := by
    have he : ((1/t)*uniformMillsConstant)^2=(uniformMillsConstant*t)^2/t^4 := by field_simp <;> ring
    rw [he,inv_eq_one_div]
    apply (div_le_div_iff_of_pos_right (pow_pos ht0 4)).mpr
    exact one_le_pow₀ hCt
  have hexp : Real.exp (-((t/2)^2/2)) ≤ Real.exp (-((c^2+κ^2)*t^2/2)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
    nlinarith only [hm]
  calc
    (t^4)⁻¹*PhiTail (t/2) ≤ (t^4)⁻¹*Real.exp (-((t/2)^2/2)) :=
      mul_le_mul_of_nonneg_left (phiTail_exp_upper (t/2) (by positivity)) (by positivity)
    _ ≤ ((1/t)*uniformMillsConstant)^2*Real.exp (-((c^2+κ^2)*t^2/2)) :=
      mul_le_mul hscalar hexp (Real.exp_nonneg _) (sq_nonneg _)
    _ ≤ PhiTail (c*t)*PhiTail (κ*t) := hprod

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxImprovedPolytopeLarge
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_shifted_polytope_large_eventually :
    ∃t₀ : ℝ, 1 ≤ t₀ ∧ ∀t : ℝ, t₀ ≤ t → ∀d : ℕ, ∀ι : Type, ∀_ : Fintype ι,
      ∀u e : Space d, ‖u‖=1 → ‖e‖=1 → ⟪u,e⟫=0 →
      ∀z : ι→Space d, (∀i,⟪u,z i⟫=0) → (∀i,⟪e,z i⟫=0) →
      ∀ξ : ι→ℝ, ∀A c κ : ℝ, 0 ≤ c → 0 ≤ κ → c^2+κ^2 ≤ 1/4 →
      gaussProb {g : Space d | ∃i,A*t < ⟪g,ξ i • e+z i⟫} ≤ (t^4)⁻¹*PhiTail (t/2) →
      1-PhiTail (κ*t) ≤ gaussProb {g : Space d | ∀i,⟪g,z i⟫ ≤ (A-c*|ξ i|)*t} := by
  obtain ⟨t₀,ht₀,hTail⟩ := phiTail_quarter_product_eventually
  refine ⟨t₀,ht₀,?_⟩
  intro t ht d ι hι u e hu he hue z huz hez ξ A c κ hc hκ hck hBad
  letI := hι
  have hb := gaussian_shifted_polytope_bound u e hu he hue z huz hez ξ A c t
  have hratio : gaussProb {g : Space d | ∃i,A*t < ⟪g,ξ i • e+z i⟫}/PhiTail (c*t) ≤ PhiTail (κ*t) := by
    apply (div_le_iff₀ (phiTail_pos (c*t))).mpr
    have hh := hBad.trans (hTail t ht c κ hc hκ hck)
    simpa only [mul_comm] using hh
  linarith only [hb,hratio]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxGaussianInterval
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryBoxBound
section
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

end


-- Source module: Solutions.GaussLocalMaxEhrhardTransmission
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedTransmission
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem flat_ehrhard_transmission_bound {d : ℕ} {Y : Type*} [Fintype Y]
    (z : Y→Space d) (ξ : Y→ℝ) (a b c A x μ κ θ t : ℝ)
    (hμ : 0 ≤ μ) (hκ : 0 ≤ κ) (hθ : 0 ≤ θ) (ht : 0 ≤ t)
    (hcancel : |x-(1+θ)*b| ≤ θ*c)
    (h₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤ (Real.sqrt 3*a-b*ξ y)*t-1/t} ≤ PhiTail (μ*t))
    (h₁ : 1-PhiTail (κ*t) ≤ gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤ (A-c*|ξ y|)*t}) :
    1-PhiTail ((μ+θ*(μ+κ))*t) ≤ gaussProb {g : Space d | ∃y,
      ((1+θ)*Real.sqrt 3*a-θ*A)*t-(1+θ)/t  <  ⟪g,z y⟫+x*ξ y*t} := by
  have hE := polyhedral_extrapolation_exceedance z
    (fun y => (Real.sqrt 3*a-b*ξ y)*t-1/t)
    (fun y => (A-c*|ξ y|)*t) (μ*t) (κ*t) θ
    (mul_nonneg hμ ht) (mul_nonneg hκ ht) hθ h₀ h₁
  have he : μ*t+θ*(μ*t+κ*t)=(μ+θ*(μ+κ))*t := by ring
  rw [he] at hE
  apply hE.trans
  unfold gaussProb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨y,hy⟩ := hg
  refine ⟨y,?_⟩
  have h₁ := neg_abs_le ((x-(1+θ)*b)*ξ y)
  rw [abs_mul] at h₁
  have h₂ := mul_le_mul_of_nonneg_right hcancel (abs_nonneg (ξ y))
  have hcoef : 0 ≤ (x-(1+θ)*b)*ξ y+θ*c*|ξ y| := by linarith only [h₁,h₂]
  have hmul := mul_nonneg hcoef ht
  calc
    ((1+θ)*Real.sqrt 3*a-θ*A)*t-(1+θ)/t ≤
        ((1+θ)*Real.sqrt 3*a-θ*A)*t-(1+θ)/t+((x-(1+θ)*b)*ξ y+θ*c*|ξ y|)*t := le_add_of_nonneg_right hmul
    _ = (1+θ)*((Real.sqrt 3*a-b*ξ y)*t-1/t)-θ*((A-c*|ξ y|)*t)+x*ξ y*t := by ring
    _ < ⟪g,z y⟫+x*ξ y*t := by linarith only [hy]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxBoxTail
section
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

end


-- Source module: Solutions.GaussLocalMaxBoxTailAsymptotic
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedEhrhard
section
set_option autoImplicit false
set_option maxHeartbeats 2200000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem improved_threshold_error (ψ θ w t : ℝ) (hθ : 0 ≤ θ) (hθ4 : θ ≤ 4)
    (hw : 0 ≤ w) (ht : 0 < t) (hwt : 1 ≤ w*t^2) :
    (ψ-200*w)*t ≤ (ψ-20*(1+θ)*Real.sqrt 3*w)*t-(1+θ)/t := by
  have hroot : Real.sqrt (3:ℝ) ≤ 7/4 := Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩
  have hprod : 20*(1+θ)*Real.sqrt 3 ≤ 175 := by
    have hh := mul_le_mul hroot (show 1+θ ≤ 5 by linarith only [hθ4]) (by linarith only [hθ]) (by norm_num : (0:ℝ) ≤ 7/4)
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_right hprod (mul_nonneg hw ht.le)
  have hi : (1+θ)/t ≤ 5*w*t := by
    apply (div_le_iff₀ ht).mpr
    nlinarith only [hwt,hθ4]
  nlinarith only [hm,hi,mul_nonneg hw ht.le]

theorem improved_ehrhard_transmission_eventually :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀t : ℝ,t₀ ≤ t → ∀L ρ : ℝ,0 < L → L < Real.sqrt H5 → ρ∈Set.Icc (-1) 1 →
      ∀n d : ℕ,∀G : SimpleGraph (Fin n),∀v : Fin n→Space d,ExactSDPVectors G v →
      ∀F : Finset (Fin n),∀r x : Fin n,x∈F → 0 < ‖uvec v r x‖ →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) →
      gaussProb {g : Space d | ((1968/1000*t:ℝ):WithBot ℝ) < nbrMax G v F x g} ≤ (t^4)⁻¹*PhiTail (t/2) →
      1-PhiTail (Real.sqrt (H5-L^2)*t) ≤ gaussProb {g : Space d | ∃y∈nbr G F x,
        (improvedPsi (Real.sqrt (H5-L^2*(1-ρ^2)))-200*roundingSlack t)*t ≤
          ⟪g,ordinaryBoxResidual 3 v x (ordinaryPlaneAxis v r x) y⟫+
            L*ρ*ordinaryBoxProjection 3 v x (ordinaryPlaneAxis v r x) y*t} := by
  classical
  obtain ⟨t₁,ht₁,hTail⟩ := gaussian_box_tail_eventually
  obtain ⟨t₂,ht₂,hLarge⟩ := gaussian_shifted_polytope_large_eventually
  have hslack : ∀ᶠ t : ℝ in atTop,roundingSlack t ≤ 1/100 :=
    (roundingSlack_tendsto.eventually_lt_const (by norm_num : (0:ℝ) < 1/100)).mono (fun _ h => h.le)
  obtain ⟨t₃,ht₃⟩ := eventually_atTop.mp hslack
  refine ⟨max (max (max t₁ t₂) t₃) (Real.exp 1),?_,?_⟩
  · exact ht₁.trans ((le_max_left t₁ t₂).trans ((le_max_left _ _).trans (le_max_left _ _)))
  intro t ht L ρ hL hLH hρ n d G v hv F r x hxF hx hp hMax
  have htt₁ : t₁ ≤ t := (le_max_left t₁ t₂).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have htt₂ : t₂ ≤ t := (le_max_right t₁ t₂).trans ((le_max_left _ _).trans ((le_max_left _ _).trans ht))
  have htt₃ : t₃ ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht1 : 1 ≤ t := ht₁.trans htt₁
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have htlog : 1 ≤ Real.log t := (Real.le_log_iff_exp_le ht0).mpr ((le_max_right _ _).trans ht)
  have hw : 0 ≤ roundingSlack t := div_nonneg (Real.log_nonneg ht1) (sq_nonneg t)
  have hw1 : roundingSlack t ≤ 1/100 := ht₃ t htt₃
  have hwt : roundingSlack t*t^2=Real.log t := div_mul_cancel₀ _ (pow_ne_zero 2 ht0.ne')
  have hH : 0 ≤ H5 := by norm_num [H5,H0,beta5,eta5]
  have hHsq : (Real.sqrt H5)^2=H5 := Real.sq_sqrt hH
  have hLsq : L^2 < H5 := by nlinarith only [hLH,hL,hHsq,Real.sqrt_nonneg H5]
  have hρsq : ρ^2 ≤ 1 := by nlinarith only [hρ.1,hρ.2]
  have hySq : (Real.sqrt (H5-L^2))^2=H5-L^2 := Real.sq_sqrt (by linarith only [hLsq])
  have hsArg : 0 ≤ H5-L^2*(1-ρ^2) := by nlinarith only [hLsq,sq_nonneg (L*ρ)]
  have hsSq : (Real.sqrt (H5-L^2*(1-ρ^2)))^2=H5-L^2*(1-ρ^2) := Real.sq_sqrt hsArg
  obtain ⟨a₀,b,μ,c,κ,θ,ha₀,hb,hμ,hμν,hc,hκ,hθ,hθ4,hnorm,hck,hμθ,hcancel,hopt⟩ :=
    improved_flat_optimization (L*ρ) (Real.sqrt (H5-L^2)) (Real.sqrt (H5-L^2*(1-ρ^2)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by rw [hsSq,hySq]; ring)
      (Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hρsq)]))
  have hν1 : improvedNu ≤ 1 := improved_nu_lt_one.le
  have haLower : 7/10 ≤ a₀ := (Real.le_sqrt_of_sq_le (by norm_num [improvedNu] : (7/10:ℝ)^2 ≤ 1-improvedNu^2)).trans ha₀
  have haUpper : a₀ ≤ 1 := by nlinarith only [hnorm,sq_nonneg b,sq_nonneg μ]
  have ha : 0 ≤ a₀-20*roundingSlack t := by linarith only [haLower,hw1]
  have hOrd := hv.ordinary
  let e := ordinaryPlaneAxis v r x
  let z : ↥(nbr G F x)→Space d := fun y => ordinaryBoxResidual 3 v x e y
  let ξ : ↥(nbr G F x)→ℝ := fun y => ordinaryBoxProjection 3 v x e y
  have he : ‖e‖=1 := ordinary_plane_axis_unit G v 3 hOrd r x hx
  have hue : ⟪v x,e⟫=0 := ordinary_plane_axis_orthogonal G v 3 hOrd r x
  have hz : ∀y : ↥(nbr G F x),⟪v x,z y⟫=0 := fun y => (ordinary_plane_residual_orthogonal G v 3 hOrd r x y hx).1
  have hez : ∀y : ↥(nbr G F x),⟪e,z y⟫=0 := fun y => (ordinary_plane_residual_orthogonal G v 3 hOrd r x y hx).2
  have hK₀ : gaussProb {g : Space d | ∀y,⟪g,z y⟫ ≤
      (Real.sqrt 3*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t} ≤ PhiTail (μ*t) := by
    have hBox := ordinary_box_exponential_bound G v 3 (by norm_num) hOrd F x hxF e he hue
      (a₀-20*roundingSlack t) b t ha ht0 hp
    have hB := hTail t htt₁ a₀ b μ haLower haUpper (hb.trans hν1) hμ (hμν.trans hν1) hnorm
    have hset : {g : Space d | ∀y,⟪g,z y⟫ ≤
        (Real.sqrt 3*(a₀-20*roundingSlack t)-b*ξ y)*t-1/t}=
        ordinaryBoxEvent G 3 v F x e (a₀-20*roundingSlack t) b t := by
      ext g
      simp only [ordinaryBoxEvent,z,ξ,cA_three,Set.mem_setOf_eq,Subtype.forall,real_inner_comm]
    rw [hset]
    exact hBox.trans hB
  have hdecomp (y : ↥(nbr G F x)) : ξ y • e+z y=residual v x y := by
    exact (orthogonalRemainder_decomposition e (ordinaryResidual 3 v x y)).symm.trans
      (strict_ordinaryResidual_three_eq G v hv.strict x y (Finset.mem_filter.mp y.2).2)
  have hBad : gaussProb {g : Space d | ∃y : ↥(nbr G F x),(1968/1000)*t < ⟪g,ξ y • e+z y⟫} ≤
      (t^4)⁻¹*PhiTail (t/2) := by
    have hset : {g : Space d | ∃y : ↥(nbr G F x),(1968/1000)*t < ⟪g,ξ y • e+z y⟫}=
        {g : Space d | (((1968/1000)*t:ℝ):WithBot ℝ) < nbrMax G v F x g} := by
      ext g
      simp only [Set.mem_setOf_eq,nbrMax,Finset.lt_sup_iff,WithBot.coe_lt_coe]
      constructor
      · rintro ⟨y,hy⟩
        exact ⟨y,y.2,by rwa [hdecomp y] at hy⟩
      · rintro ⟨y,hy,hyg⟩
        exact ⟨⟨y,hy⟩,by rwa [hdecomp ⟨y,hy⟩]⟩
    rw [hset]
    exact hMax
  have hK₁ := hLarge t htt₂ d ↥(nbr G F x) inferInstance (v x) e (hv.1 x) he hue z hz hez ξ
    (1968/1000) c κ hc hκ (hck.trans (by norm_num)) hBad
  have hE := flat_ehrhard_transmission_bound z ξ (a₀-20*roundingSlack t) b c (1968/1000)
    (L*ρ) μ κ θ t hμ hκ hθ ht0.le hcancel hK₀ hK₁
  rw [hμθ] at hE
  apply hE.trans
  unfold gaussProb
  apply measureReal_mono _ (measure_ne_top _ _)
  intro g hg
  obtain ⟨y,hy⟩ := hg
  refine ⟨y,y.2,?_⟩
  have herr := improved_threshold_error (improvedPsi (Real.sqrt (H5-L^2*(1-ρ^2)))) θ (roundingSlack t) t hθ hθ4 hw ht0
    (by rw [hwt]; exact htlog)
  have hoptT := mul_le_mul_of_nonneg_right hopt ht0.le
  nlinarith only [hy,herr,hoptT]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxPlaneGeometry
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryTransmission
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverSliceGeometry
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedSlice
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem improved_cover_slice_threshold {n d : ℕ} (G : SimpleGraph (Fin n))
    (v : Fin n→Space d) (hv : ExactSDPVectors G v) (U t z : ℝ)
    (r x y : Fin n) (hx : 0 < ‖uvec v r x‖) (hxy : G.Adj x y)
    (ht : 0 < t) (hz : 0 < z) (hzH : z < Real.sqrt H5*t)
    (hLoss : 100*Real.sqrt 3*roundingSlack t ≤ 1/3000)
    (hU : U*t ≤ ‖uvec v r x‖*z) (W : ℝ)
    (hW : (improvedPsi (Real.sqrt (H5-(z/t)^2*(1-(rho v r x)^2)))-200*roundingSlack t)*t ≤
      W+(z/t)*rho v r x*ordinaryBoxProjection 3 v x (ordinaryPlaneAxis v r x) y*t) :
    (U+1/3000)*t ≤ planeNeighborScore v 3 r x y z W := by
  let L := z/t
  let U' := ‖uvec v r x‖*L
  have hL : 0 < L := div_pos hz ht
  have hLH : L < Real.sqrt H5 := (div_lt_iff₀ ht).mpr hzH
  have hUt : U'*t=‖uvec v r x‖*z := by dsimp [U',L]; field_simp
  have hUU : U ≤ U' := by nlinarith only [hU,hUt,ht]
  have hU' : 0 ≤ U' := mul_nonneg hx.le hL.le
  have hU'H : U' ≤ Real.sqrt H5 := by
    have hn := ordinary_root_residual_norm_le G v 3 hv.ordinary r x
    have hh : U' ≤ L := by dsimp only [U']; nlinarith only [mul_nonneg (sub_nonneg.mpr hn) hL.le]
    exact hh.trans hLH.le
  have hsq : U'^2=L^2*(1-(rho v r x)^2) := by
    dsimp only [U']
    rw [mul_pow,ordinary_root_residual_norm_sq G v 3 hv.ordinary r x]
    ring
  have hDrift := improved_drift U' hU' hU'H
  rw [hsq] at hDrift
  have hψT := mul_le_mul_of_nonneg_right hDrift ht.le
  have hWT := mul_le_mul_of_nonneg_left hW (div_nonneg (Real.sqrt_nonneg (3:ℝ)) (by norm_num : (0:ℝ) ≤ 2))
  have hLossT := mul_le_mul_of_nonneg_right hLoss ht.le
  have hroot : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hcoeff : (1-(-(1/2):ℝ))/cA 3=Real.sqrt 3/2 := by
    rw [cA_three]
    field_simp
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hScore : planeNeighborScore v 3 r x y z W=
      U'/2*t+Real.sqrt 3/2*(W+L*rho v r x*ordinaryBoxProjection 3 v x (ordinaryPlaneAxis v r x) y*t) := by
    unfold planeNeighborScore
    rw [hv.2.2.1 x y hxy,hcoeff]
    dsimp only [U',L]
    field_simp
    <;> ring
  rw [hScore]
  have hUU' := mul_le_mul_of_nonneg_right hUU ht.le
  nlinarith only [hψT,hWT,hLossT,hUU']

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxCoverSliceScalar
section
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

end


-- Source module: Solutions.GaussLocalMaxThresholdOptimization
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryOptimization
section
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

end


-- Source module: Solutions.GaussLocalMaxDriftGeometry
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryNuBound
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryGap
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverSliceThreshold
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverFubini
section
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

end


-- Source module: Solutions.GaussLocalMaxGaussianPolytopeLarge
section
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

end


-- Source module: Solutions.GaussLocalMaxOrdinaryEhrhard
section
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

end


-- Source module: Solutions.GaussLocalMaxEhrhardUniform
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverBadEvent
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedFiber
section
set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem improved_cover_bad_fiber_bound :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀t : ℝ,t₀ ≤ t → ∀n d : ℕ,∀G : SimpleGraph (Fin n),
      ∀v : Fin n→Space d,ExactSDPVectors G v → ∀F : Finset (Fin n),∀r x : Fin n,
      x∈F → 0 < ‖uvec v r x‖ → ∀U : ℝ,0 < U →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) →
      gaussProb {g : Space d | ((1968/1000*t:ℝ):WithBot ℝ) < nbrMax G v F x g} ≤ (t^4)⁻¹*PhiTail (t/2) →
      ∀z : ℝ,0 ≤ z → z < Real.sqrt H5*t →
      ((stdGaussian (Space d)).map (coverBoxSample G v 3 F r x)).real
        {W | (z,W)∈coverBadEvent G v 3 F r x U (1/120000) t} ≤
          PhiTail (Real.sqrt ((Real.sqrt H5*t)^2-z^2)) := by
  classical
  obtain ⟨t₁,ht₁,hTail⟩ := improved_ehrhard_transmission_eventually
  have hLoss : ∀ᶠ t : ℝ in atTop,100*Real.sqrt 3*roundingSlack t ≤ 1/3000 := by
    have hh := roundingSlack_tendsto.const_mul (100*Real.sqrt (3:ℝ))
    have hh' : Tendsto (fun t => 100*Real.sqrt 3*roundingSlack t) atTop (nhds 0) := by simpa only [mul_zero] using hh
    exact (hh'.eventually_lt_const (by norm_num : (0:ℝ) < 1/3000)).mono (fun _ h => h.le)
  obtain ⟨t₂,ht₂⟩ := eventually_atTop.mp hLoss
  refine ⟨max t₁ t₂,ht₁.trans (le_max_left _ _),?_⟩
  intro t ht n d G v hv F r x hxF hx U hU hp hMax z hz0 hzA
  have htt : t₁ ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := ht₁.trans htt
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hLoss := ht₂ t ((le_max_right _ _).trans ht)
  let E := coverBadEvent G v 3 F r x U (1/120000) t
  let W := coverBoxSample G v 3 F r x
  have hWm : Measurable W := coverBoxSample_measurable G v 3 F r x
  have hEm : MeasurableSet E := coverBadEvent_measurable G v 3 F r x U (1/120000) t
  have hMap : ((stdGaussian (Space d)).map W).real {a | (z,a)∈E}=gaussProb {g : Space d | (z,W g)∈E} := by
    change ((stdGaussian (Space d)).map W).real (Prod.mk z ⁻¹' E)=_
    rw [map_measureReal_apply hWm (measurable_prodMk_left hEm)]
    rfl
  rw [hMap]
  by_cases hTrigger : U*t ≤ ‖uvec v r x‖*z
  · have hz : 0 < z := by nlinarith only [hTrigger,mul_pos hU ht0,hx]
    have hL : 0 < z/t := div_pos hz ht0
    have hLH : z/t < Real.sqrt H5 := (div_lt_iff₀ ht0).mpr hzA
    let B : ℝ := improvedPsi (Real.sqrt (H5-(z/t)^2*(1-(rho v r x)^2)))-200*roundingSlack t
    let S : Set (Space d) := {g | ∃y∈nbr G F x,
      B*t ≤ ⟪g,ordinaryBoxResidual 3 v x (ordinaryPlaneAxis v r x) y⟫+
        (z/t)*rho v r x*ordinaryBoxProjection 3 v x (ordinaryPlaneAxis v r x) y*t}
    have hS : MeasurableSet S := by
      apply measurableSet_setOfPred.mpr
      apply Measurable.exists
      intro y
      apply Measurable.and measurable_const
      exact measurableSet_setOfPred.mp (measurableSet_le measurable_const (by fun_prop))
    have hT : 1-PhiTail (Real.sqrt (H5-(z/t)^2)*t) ≤ gaussProb S := by
      exact hTail t htt (z/t) (rho v r x) hL hLH (ordinary_root_rho_mem G v 3 hv.ordinary r x)
        n d G v hv F r x hxF hx hp hMax
    have hComp : gaussProb Sᶜ ≤ PhiTail (Real.sqrt (H5-(z/t)^2)*t) := by
      unfold gaussProb at hT ⊢
      rw [probReal_compl_eq_one_sub hS]
      linarith only [hT]
    have hSub : {g : Space d | (z,W g)∈E} ⊆ Sᶜ := by
      intro g hg hs
      obtain ⟨y,hy,hQ⟩ := hs
      have hscore := improved_cover_slice_threshold G v hv U t z r x y hx
        (Finset.mem_filter.mp hy).2 ht0 hz hzA hLoss hTrigger
        ⟪g,ordinaryBoxResidual 3 v x (ordinaryPlaneAxis v r x) y⟫ hQ
      have hbad := hg.2 ⟨y,hy⟩
      have heq : U+40*(1/120000:ℝ)=U+1/3000 := by ring
      rw [heq] at hbad
      exact not_lt_of_ge hscore hbad
    apply (measureReal_mono hSub (measure_ne_top _ _)).trans
    apply hComp.trans_eq
    congr 1
    have hH0 : 0 ≤ H5 := by norm_num [H5,H0,beta5,eta5]
    have hsub : 0 ≤ H5-(z/t)^2 := by nlinarith only [hL,hLH,Real.sq_sqrt hH0,Real.sqrt_nonneg H5]
    symm
    apply (Real.sqrt_eq_iff_eq_sq (by nlinarith only [hz0,hzA,Real.sqrt_nonneg H5,mul_nonneg (Real.sqrt_nonneg H5) ht0.le])
      (mul_nonneg (Real.sqrt_nonneg _) ht0.le)).mpr
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
    simpa only [gaussProb,measureReal_empty] using phiTail_nonneg (Real.sqrt ((Real.sqrt H5*t)^2-z^2))

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxCoverOneVertex
section
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

end


-- Source module: Solutions.GaussLocalMaxImprovedOneVertex
section
set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem improved_cover_one_vertex_bound :
    ∃t₀ : ℝ,1 ≤ t₀ ∧ ∀t : ℝ,t₀ ≤ t → ∀n d : ℕ,∀G : SimpleGraph (Fin n),
      ∀v : Fin n→Space d,ExactSDPVectors G v → ∀F : Finset (Fin n),∀r x : Fin n,
      x∈F → 0<‖uvec v r x‖ → ∀U : ℝ,0<U →
      pLocal G v F x ≤ Real.exp (-(t^2/2)) →
      gaussProb {g : Space d | ((1968/1000*t:ℝ):WithBot ℝ)<nbrMax G v F x g} ≤ (t^4)⁻¹*PhiTail (t/2) →
      gaussProb {g : Space d | ⟪g,uvec v r x⟫ ≤ -(U*t) ∧
        ∀y∈nbr G F x,⟪g,uvec v r y⟫<(U+1/3000)*t} ≤
          (1+Real.sqrt H5*t/Real.sqrt (2*Real.pi))*Real.exp (-(H5*t^2/2)) := by
  classical
  obtain ⟨t₀,ht₀,hFiber⟩ := improved_cover_bad_fiber_bound
  refine ⟨t₀,ht₀,?_⟩
  intro t htt n d G v hvExact F r x hxF hx U hU hp hMax
  let k : ℝ := 3
  let H : ℝ := H5
  let w : ℝ := 1/120000
  have hk : 2<k := by norm_num [k]
  have hH : 1<H := by norm_num [H,H5,H0,beta5,eta5]
  have ht : 0<t := zero_lt_one.trans_le (ht₀.trans htt)
  have hv : OrdinaryVectorColoring G v k := hvExact.ordinary
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
    exact hFiber t htt n d G v hvExact F r x hxF hx U hU hp hMax Z hZ hZA
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
  have hThreshold : U+40*w=U+1/3000 := by dsimp only [w]; ring
  rw [hThreshold] at hResult
  exact hResult


end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxCapacity
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem capacity_le_add_two (D ρ : ℝ) : capacity D ρ ≤ D+2 := by
  unfold capacity
  split
  · exact min_le_left _ _
  · split
    · exact min_le_left _ _
    · linarith

theorem capacity_ge_add_one (D ρ : ℝ) (hD : 0 ≤ D) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) :
    D+1 ≤ capacity D ρ := by
  have hDD : 0 ≤ D*(D+1) := by positivity
  have hroot (r : ℝ) (hr : 2/3 ≤ r) : D+1 ≤ (1+Real.sqrt (1+6*D*(D+1)*r))/2 := by
    have hrad : (2*D+1)^2 ≤ 1+6*D*(D+1)*r := by
      have h := mul_nonneg hDD (sub_nonneg.mpr hr)
      nlinarith only [h]
    have hnon : 0 ≤ 1+6*D*(D+1)*r := (sq_nonneg _).trans hrad
    have hsq := Real.sq_sqrt hnon
    have hn := Real.sqrt_nonneg (1+6*D*(D+1)*r)
    nlinarith only [hrad,hsq,hn,hD]
  unfold capacity
  split
  · rename_i hρ0
    apply le_min (by linarith)
    apply hroot
    apply (le_div_iff₀ (show 0<1-4*ρ by linarith)).mpr
    nlinarith only [hρ.1]
  · rename_i hρ0
    split
    · rename_i hρ4
      have hρp : 0<ρ := lt_of_not_ge hρ0
      apply le_min (by linarith)
      have h := hroot (1/(1+2*ρ)) (by
        apply (le_div_iff₀ (show 0<1+2*ρ by linarith)).mpr
        nlinarith only [hρ4])
      simpa only [div_eq_mul_inv,one_mul] using h
    · exact le_rfl

theorem capacity_D5_ge (ρ : ℝ) (hρ : ρ∈Set.Icc (-(1/2):ℝ) 1) : D5+1 ≤ capacity D5 ρ := by
  apply capacity_ge_add_one _ _ _ hρ
  norm_num [D5,beta5]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxSection5Scale
section
set_option autoImplicit false
set_option maxHeartbeats 1300000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem section5_log_nat_tendsto_atTop : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem beta5_pos : 0<beta5 := by norm_num [beta5]
theorem beta5_lt_one : beta5<1 := by norm_num [beta5]
theorem D5_pos : 0<D5 := by norm_num [D5,beta5]
theorem eta5_pos : 0<eta5 := by norm_num [eta5]

theorem t5_sq (n : ℕ) (hn : 1≤n) : t5 n^2=(1-beta5)*Real.log (n:ℝ) := by
  apply Real.sq_sqrt
  exact mul_nonneg (sub_nonneg.mpr beta5_lt_one.le) (Real.log_nonneg (by exact_mod_cast hn))

theorem t5_sq_tendsto_atTop : Tendsto (fun n : ℕ => t5 n^2) atTop atTop := by
  apply (section5_log_nat_tendsto_atTop.const_mul_atTop (sub_pos.mpr beta5_lt_one)).congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact (t5_sq n hn).symm

theorem t5_tendsto_atTop : Tendsto t5 atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (section5_log_nat_tendsto_atTop.const_mul_atTop (sub_pos.mpr beta5_lt_one))

theorem exp_D5_add_two (n : ℕ) (hn : 1≤n) : Real.exp ((D5+2)*t5 n^2/2)=n := by
  rw [t5_sq n hn]
  have he : (D5+2)*((1-beta5)*Real.log (n:ℝ))/2=Real.log (n:ℝ) := by
    unfold D5
    field_simp [show 1-beta5≠0 from (sub_pos.mpr beta5_lt_one).ne']
    <;> ring
  rw [he,Real.exp_log (by exact_mod_cast (show 0<n by omega))]

theorem degree5_exp (n : ℕ) (hn : 1≤n) : (n:ℝ)^beta5=Real.exp (D5*t5 n^2/2) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0<n by omega)),t5_sq n hn]
  congr 1
  unfold D5
  field_simp [show 1-beta5≠0 from (sub_pos.mpr beta5_lt_one).ne']
  <;> ring

theorem capacity_trivial_band_bound {n : ℕ} (hn : 1≤n) (S : Finset (Fin n)) (ρ : ℝ)
    (hcap : D5+2≤capacity D5 ρ+eta5) :
    (S.card:ℝ) ≤ Real.exp ((capacity D5 ρ+eta5)*t5 n^2/2) := by
  have hc : S.card≤n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hcard : (S.card:ℝ) ≤ n := by exact_mod_cast hc
  rw [←exp_D5_add_two n hn] at hcard
  apply hcard.trans
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcap (sq_nonneg _)) (by norm_num)

theorem target5_le_two_rpow (n : ℕ) (hn : 2≤n) : (target5 n:ℝ) ≤ 2*(n:ℝ)^((1+beta5)/2) := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  have hn0 : (0:ℝ)<n := lt_trans zero_lt_one hn1
  have hL0 : 0<numLevels n := Nat.ceil_pos.mpr (Real.log_pos hn1)
  have hL : (1:ℝ)≤numLevels n := by exact_mod_cast hL0
  have hden : 1≤100*(numLevels n:ℝ)^4 := by
    have hpow : (1:ℝ)≤(numLevels n:ℝ)^4 := one_le_pow₀ hL
    linarith only [hpow]
  have hδ : 0≤(n:ℝ)*delta5 n := by unfold delta5; positivity
  have hceil := (Nat.ceil_lt_add_one (show 0≤(n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4) by positivity)).le
  have hquot : (n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4)≤(n:ℝ)*delta5 n := div_le_self hδ hden
  have hid : (n:ℝ)*delta5 n=(n:ℝ)^((1+beta5)/2) := by
    unfold delta5
    calc
      (n:ℝ)*(n:ℝ)^(-((1-beta5)/2)) = (n:ℝ)^(1:ℝ)*(n:ℝ)^(-((1-beta5)/2)) := by rw [Real.rpow_one]
      _ = (n:ℝ)^((1+beta5)/2) := by
        rw [←Real.rpow_add hn0]
        congr 1
        ring
  have hpow1 : (1:ℝ)≤(n:ℝ)^((1+beta5)/2) := Real.one_le_rpow hn1.le (by linarith [beta5_pos])
  change (⌈(n:ℝ)*delta5 n/(100*(numLevels n:ℝ)^4)⌉₊:ℝ)≤_
  linarith only [hceil,hquot,hpow1,hid]

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxImprovedLoss
section
set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem gaussian_fixed_gap_loss_eventually (H gap : ℝ) (hgap : 0 < gap) :
    ∀ᶠ t : ℝ in atTop,
      (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(gap*t^2/2)) ≤ (t^100)⁻¹ := by
  let C := Real.sqrt H/Real.sqrt (2*Real.pi)
  have hC : 0 ≤ C := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsmall := roundingSlack_tendsto.eventually_lt_const (div_pos hgap (by norm_num : (0:ℝ) < 204))
  filter_upwards [eventually_ge_atTop (max (2:ℝ) (2*C)),hsmall] with t ht hsmall
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have htC : 2*C ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := by linarith only [ht2]
  have hcoef : 1+Real.sqrt H*t/Real.sqrt (2*Real.pi) ≤ t^2 := by
    rw [←div_mul_eq_mul_div]
    change 1+C*t ≤ t^2
    have hh := mul_nonneg (show 0 ≤ t-2*C by linarith only [htC]) ht0.le
    nlinarith only [hh,ht2,sq_nonneg (t-1)]
  have hexp : Real.exp (-(gap*t^2/2)) ≤ Real.exp (-102*Real.log t) := by
    apply Real.exp_le_exp.mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos ht0)).mp hsmall
    nlinarith only [hh]
  have hpow : Real.exp (-102*Real.log t)=(t^102)⁻¹ := by
    rw [show -102*Real.log t=-((102:ℕ)*Real.log t) by norm_num,Real.exp_neg,Real.exp_nat_mul,Real.exp_log ht0]
  calc
    (1+Real.sqrt H*t/Real.sqrt (2*Real.pi))*Real.exp (-(gap*t^2/2)) ≤ t^2*Real.exp (-102*Real.log t) :=
      mul_le_mul hcoef hexp (Real.exp_nonneg _) (sq_nonneg _)
    _ = (t^100)⁻¹ := by rw [hpow]; field_simp <;> ring

theorem H5_eq_D5_add_two : H5=D5+2+3*eta5 := by norm_num [H5,H0,D5,beta5]

theorem section5_population_tail_identity (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)*((1+Real.sqrt H5*t5 n/Real.sqrt (2*Real.pi))*Real.exp (-(H5*t5 n^2/2)))=
      (1+Real.sqrt H5*t5 n/Real.sqrt (2*Real.pi))*Real.exp (-((3*eta5)*t5 n^2/2)) := by
  rw [←exp_D5_add_two n hn]
  calc
    Real.exp ((D5+2)*t5 n^2/2)*((1+Real.sqrt H5*t5 n/Real.sqrt (2*Real.pi))*Real.exp (-(H5*t5 n^2/2)))=
        (1+Real.sqrt H5*t5 n/Real.sqrt (2*Real.pi))*Real.exp ((D5+2)*t5 n^2/2-(H5*t5 n^2/2)) := by
      rw [Real.exp_sub,Real.exp_neg]
      ring
    _ = _ := by rw [H5_eq_D5_add_two]; congr 2 <;> ring

end
end GaussLocalMaxColoring.Main

end


-- Source module: Solutions.GaussLocalMaxGaussianSymmetry
section
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

end


-- Source module: Solutions.GaussLocalMaxCoverUnion
section
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

end


-- Source module: Solutions.GaussLocalMaxLemma43
section
set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped RealInnerProductSpace Topology
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main

/-- **Lemma 43** (Improved single-step lifting; p. 48, PDF 50). Section 5 setting (analysis
convention: exact edge constraint), any nested core sequence, any root `r`, and `n` (hence `t`)
sufficiently large. Let `1  ≤  j  ≤  ℓ` and `W ⊆ F_j` (fixed independently of `g`), and suppose
`{u_x}_{x ∈ W}` is a `(Ut, q)`-cover for some `0  <  U  ≤  √H`. Assume `p_{F_{j−1}}(x)  ≤  e^{−t²/2}`
and `P_g[M_{F_{j−1}}(x) > 1.968t]  ≤  t^{−4}Φ̄(t/2)` for every `x ∈ W`, and set
`W′ = N_{F_{j−1}}(W)`. Then `{u_y}_{y ∈ W′}` is a `((U + 1/3000)t, q − t^{−100})`-cover. -/
theorem lemma_43 :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀  ≤  n →
    ∀ (d : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
      (maxDegOn G Finset.univ : ℝ)  ≤  (n : ℝ) ^ beta5 →
      ∀ v : Fin n → Space d, ExactSDPVectors G v →
      ∀ F : ℕ → Finset (Fin n), F 0 = Finset.univ → (∀ i, F (i + 1) ⊆ F i) →
      ∀ (r : Fin n) (j : ℕ), 1  ≤  j → j  ≤  numLevels n →
      ∀ W : Finset (Fin n), W ⊆ F j →
      ∀ U q : ℝ, 0  <  U → U  ≤  Real.sqrt H5 →
      IsCover (W.image (uvec v r)) (U * t5 n) q →
      (∀ x ∈ W, pLocal G v (F (j - 1)) x  ≤  Real.exp (-(t5 n ^ 2 / 2)) ∧
        gaussProb {g : Space d |
            ((1968 / 1000 * t5 n : ℝ) : WithBot ℝ)  <  nbrMax G v (F (j - 1)) x g}  ≤ 
          (t5 n ^ 4)⁻¹ * PhiTail (t5 n / 2)) →
      IsCover ((W.biUnion (nbr G (F (j - 1)))).image (uvec v r)) ((U + 1 / 3000) * t5 n)
        (q - (t5 n ^ 100)⁻¹) := by
  classical
  obtain ⟨t₀,ht₀,hVertex⟩ := improved_cover_one_vertex_bound
  have hLoss := t5_tendsto_atTop.eventually (gaussian_fixed_gap_loss_eventually H5 (3*eta5) (by have h := eta5_pos; positivity))
  have hAll := ((t5_tendsto_atTop.eventually_ge_atTop t₀).and (hLoss.and (eventually_ge_atTop (2:ℕ))))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hAll
  refine ⟨N₀,?_⟩
  intro n hn d G hColor hDegree v hv F hF0 hNest r j hj1 hjL W hW U q hU hUH hCover hBounds
  obtain ⟨htt,hLoss,hn2⟩ := hN₀ n hn
  let t : ℝ := t5 n
  let err : ℝ := (1+Real.sqrt H5*t/Real.sqrt (2*Real.pi))*Real.exp (-(H5*t^2/2))
  have ht : 0 < t := zero_lt_one.trans_le (ht₀.trans htt)
  have hWF : W⊆F (j-1) := by
    apply hW.trans
    have hEq : (j-1)+1=j := by omega
    simpa only [hEq] using hNest (j-1)
  have hLift : IsCover ((neighborUnion G (F (j-1)) W).image (uvec v r)) ((U+1/3000)*t)
      (q-(W.card:ℝ)*err) := by
    apply finite_cover_lifting G (uvec v r) (F (j-1)) W (U*t) ((U+1/3000)*t) q err hCover
    intro x hxW
    by_cases hxpos : 0 < ‖uvec v r x‖
    · exact hVertex t htt n d G v hv (F (j-1)) r x (hWF hxW) hxpos U hU (hBounds x hxW).1 (hBounds x hxW).2
    · have hn0 : ‖uvec v r x‖=0 := le_antisymm (le_of_not_gt hxpos) (norm_nonneg _)
      have hux : uvec v r x=0 := norm_eq_zero.mp hn0
      have he : {g : Space d | ⟪g,uvec v r x⟫  ≤  -(U*t) ∧
          ∀y∈nbr G (F (j-1)) x,⟪g,uvec v r y⟫ < (U+1/3000)*t}=∅ := by
        ext g
        constructor
        · intro hg
          have hh := hg.1
          rw [hux,inner_zero_right] at hh
          nlinarith only [hh,mul_pos hU ht]
        · intro hg
          exact hg.elim
      rw [he]
      simp only [gaussProb,measureReal_empty]
      dsimp only [err]
      positivity
  have hErr : 0 ≤ err := by dsimp only [err]; positivity
  have hCardNat : W.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ W
  have hCard : (W.card:ℝ) ≤ n := by exact_mod_cast hCardNat
  have hPop := mul_le_mul_of_nonneg_right hCard hErr
  have hIdentity : (n:ℝ)*err=(1+Real.sqrt H5*t/Real.sqrt (2*Real.pi))*Real.exp (-((3*eta5)*t^2/2)) :=
    section5_population_tail_identity n (by omega)
  rw [hIdentity] at hPop
  have hTotal : (W.card:ℝ)*err ≤ (t^100)⁻¹ := hPop.trans hLoss
  unfold IsCover at hLift ⊢
  exact (sub_le_sub_left hTotal q).trans hLift

end GaussLocalMaxColoring.Main

end

open RecGaussColoring.Main GaussLocalMaxColoring.Main
theorem solution :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ (d : ℕ) (G : SimpleGraph (Fin n)), G.Colorable 3 →
      (maxDegOn G Finset.univ : ℝ) ≤ (n : ℝ) ^ beta5 →
      ∀ v : Fin n → Space d, ExactSDPVectors G v →
      ∀ F : ℕ → Finset (Fin n), F 0 = Finset.univ → (∀ i, F (i + 1) ⊆ F i) →
      ∀ (r : Fin n) (j : ℕ), 1 ≤ j → j ≤ numLevels n →
      ∀ W : Finset (Fin n), W ⊆ F j →
      ∀ U q : ℝ, 0 < U → U ≤ Real.sqrt H5 →
      IsCover (W.image (uvec v r)) (U * t5 n) q →
      (∀ x ∈ W, pLocal G v (F (j - 1)) x ≤ Real.exp (-(t5 n ^ 2 / 2)) ∧
        gaussProb {g : Space d |
            ((1968 / 1000 * t5 n : ℝ) : WithBot ℝ) < nbrMax G v (F (j - 1)) x g} ≤
          (t5 n ^ 4)⁻¹ * PhiTail (t5 n / 2)) →
      IsCover ((W.biUnion (nbr G (F (j - 1)))).image (uvec v r)) ((U + 1 / 3000) * t5 n)
        (q - (t5 n ^ 100)⁻¹) := by
  exact GaussLocalMaxColoring.Main.lemma_43
#print axioms solution
