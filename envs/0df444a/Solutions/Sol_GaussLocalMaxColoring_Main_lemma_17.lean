-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_17
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-17T15:47:45.246202+00:00
-- url     : https://prove2.me/submissions/aa3f53e5-ea9c-43fa-880a-03efe1176cf7

import Definitions.Def_GaussLocalMaxColoring_Main_Basic


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


set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main

namespace GaussLocalMaxColoring.Main
noncomputable section

theorem lemma_17 {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d)
    (hv : StrictVectorColoring G v) (F : Finset (Fin n)) (x : Fin n) (hx : x∈F) (a:ℝ) :
    pLocal G v F x =
      ∫ g,tailOver (Real.sqrt 3) (nbrMax G v F x g) ∂stdGaussian (Space d) ∧
    gaussProb {g : Space d | nbrMax G v F x g≤((a:ℝ):WithBot ℝ)} ≤
      pLocal G v F x / PhiTail (a/Real.sqrt 3) := by
  classical
  by_cases hS : (nbr G F x).Nonempty
  · letI : Nonempty ↥(nbr G F x) := ⟨⟨hS.choose,hS.choose_spec⟩⟩
    let X : Space d→ℝ := fun g => ⟪g,v x⟫
    let Z : Space d→(↥(nbr G F x)→ℝ) := fun g y => ⟪g,residual v x y⟫
    let Y : Space d→ℝ := fun g => finiteMax (Z g)
    have hX : Measurable X := by dsimp [X]; fun_prop
    have hZ : Measurable Z := by dsimp [Z]; fun_prop
    have hY : Measurable Y := finiteMax_measurable.comp hZ
    have hI : IndepFun X Y (stdGaussian (Space d)) := by
      simpa only [Function.comp_def,id_eq] using
        ((strict_residuals_independent G v hv F x).comp measurable_id finiteMax_measurable)
    have hN : (stdGaussian (Space d)).map X=gaussianReal 0 1 := by
      simpa only [X,real_inner_comm] using gaussian_inner_map (v x) (hv.1 x)
    have hc : 0<Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hevent : pLocal G v F x=(stdGaussian (Space d)).real
        {g : Space d | Y g<Real.sqrt 3*X g} := by
      rw [pLocal_eq_strict_probability G v hv F x hx]
      unfold gaussProb
      congr 1
      ext g
      change (∀ y∈nbr G F x,⟪g,v y⟫<⟪g,v x⟫) ↔
        finiteMax (Z g)<Real.sqrt 3*X g
      rw [finiteMax_lt_iff]
      constructor
      · intro h y
        exact (strict_edge_lt_iff G v hv x y (Finset.mem_filter.mp y.2).2 g).mp (h y y.2)
      · intro h y hy
        exact (strict_edge_lt_iff G v hv x y (Finset.mem_filter.mp hy).2 g).mpr (h ⟨y,hy⟩)
    have hP : pLocal G v F x=∫ g,PhiTail (Y g/Real.sqrt 3) ∂stdGaussian (Space d) := by
      rw [hevent]
      exact independent_gaussian_threshold (stdGaussian (Space d)) X Y hX hY hI hN _ hc
    have hmax : ∀g,nbrMax G v F x g=(Y g:WithBot ℝ) :=
      nbrMax_eq_coe_finiteMax G v F x
    constructor
    · rw [hP]
      apply integral_congr_ae
      filter_upwards [] with g
      rw [hmax]
      rfl
    · have hb := gaussian_tail_integral_lower_bound (stdGaussian (Space d)) Y hY
        (Real.sqrt 3) a hc
      rw [← hP] at hb
      simpa only [gaussProb,hmax,WithBot.coe_le_coe] using hb
  · have he : nbr G F x=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp : pLocal G v F x=1 := by
      rw [pLocal_eq_strict_probability G v hv F x hx]
      simp [he,gaussProb]
    constructor
    · simp [hp,nbrMax,he,tailOver]
    · simp only [nbrMax,he,Finset.sup_empty,bot_le,Set.setOf_true,gaussProb,
        probReal_univ,hp]
      exact (le_div_iff₀ (phiTail_pos _)).mpr (by simpa using phiTail_le_one (a/Real.sqrt 3))

end
end GaussLocalMaxColoring.Main

open GaussLocalMaxColoring.Main
open RecGaussColoring.Main
open MeasureTheory
open ProbabilityTheory
open scoped RealInnerProductSpace

theorem solution {n d : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n → Space d)
    (hv : StrictVectorColoring G v) (F : Finset (Fin n)) (x : Fin n) (hx : x ∈ F) (a : ℝ) :
    pLocal G v F x =
        ∫ g, tailOver (Real.sqrt 3) (nbrMax G v F x g) ∂(stdGaussian (Space d)) ∧
      gaussProb {g : Space d | nbrMax G v F x g ≤ ((a : ℝ) : WithBot ℝ)} ≤
        pLocal G v F x / PhiTail (a / Real.sqrt 3)  := GaussLocalMaxColoring.Main.lemma_17 G v hv F x hx a
