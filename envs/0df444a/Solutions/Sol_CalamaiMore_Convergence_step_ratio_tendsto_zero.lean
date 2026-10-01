-- Prove2me | solution 1 for CalamaiMore.Convergence.step_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T12:13:47.469979+00:00
-- url     : https://prove2.me/submissions/0e1b6988-e99d-4216-a958-4dbd35d6f21b

import Definitions.Def_CalamaiMore_Convergence_proj
import Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Tactic
open Set Filter Topology
open CalamaiMore.Convergence CalamaiMore.Shared

private theorem nearest_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    CalamaiMore.Convergence.nearestPoint Ω y ∈ Ω ∧ ∀ w ∈ Ω,
      ‖CalamaiMore.Convergence.nearestPoint Ω y-y‖ ≤ ‖w-y‖ := by
  have he : ∃ z ∈ Ω,∀ w ∈ Ω,‖z-y‖ ≤ ‖w-y‖ := by
    obtain ⟨z,hz,hmin⟩:=exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hv y
    refine ⟨z,hz,?_⟩
    intro w hw
    rw [norm_sub_rev z y,norm_sub_rev w y,hmin]
    exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨w,hw⟩
  unfold CalamaiMore.Convergence.nearestPoint
  rw [dif_pos he]
  exact Classical.choose_spec he

private theorem nearest_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    ∀ w ∈ Ω, inner ℝ (y-CalamaiMore.Convergence.nearestPoint Ω y)
      (w-CalamaiMore.Convergence.nearestPoint Ω y) ≤ 0 := by
  letI : Nonempty Ω := hne.to_subtype
  obtain ⟨hp,hmin⟩:=nearest_spec Ω hne hc hv y
  apply (norm_eq_iInf_iff_real_inner_le_zero hv hp).mp
  apply le_antisymm
  · apply le_ciInf
    intro w
    simpa only [norm_sub_rev] using hmin w w.property
  · exact ciInf_le (f:=fun w : Ω => ‖y-w‖) ⟨(0:ℝ),by rintro _ ⟨v,rfl⟩; exact norm_nonneg _⟩ ⟨_,hp⟩


private theorem proj_mem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (y : E) :
    proj Ω y ∈ Ω := (nearest_spec Ω hne hc hv y).1

private theorem proj_lipschitz {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω) (x y : E) :
    ‖proj Ω x-proj Ω y‖ ≤ ‖x-y‖ := by
  have h1:=nearest_inner Ω hne hc hv x (proj Ω y) (proj_mem Ω hne hc hv y)
  have h2:=nearest_inner Ω hne hc hv y (proj Ω x) (proj_mem Ω hne hc hv x)
  change inner ℝ (x-proj Ω x) (proj Ω y-proj Ω x) ≤ 0 at h1
  change inner ℝ (y-proj Ω y) (proj Ω x-proj Ω y) ≤ 0 at h2
  have hh : ‖proj Ω x-proj Ω y‖^2 ≤ inner ℝ (x-y) (proj Ω x-proj Ω y) := by
    have he : proj Ω y-proj Ω x=-(proj Ω x-proj Ω y) := by module
    rw [he,inner_neg_right] at h1
    have he' : x-y = (x-proj Ω x)+(proj Ω x-proj Ω y)-(y-proj Ω y) := by module
    conv_rhs => rw [he',inner_sub_left,inner_add_left,real_inner_self_eq_norm_sq]
    linarith
  have hb:=(real_inner_le_norm (x-y) (proj Ω x-proj Ω y))
  nlinarith [norm_nonneg (proj Ω x-proj Ω y),norm_nonneg (x-y)]

private theorem proj_self {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Ω : Set E) (hc : IsClosed Ω) (hv : Convex ℝ Ω) {x : E} (hx : x∈Ω) : proj Ω x=x := by
  have hh:=(nearest_spec Ω ⟨x,hx⟩ hc hv x).2 x hx
  simpa only [sub_self,norm_zero,norm_le_zero_iff,sub_eq_zero,proj] using hh

private theorem path_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    {x : E} (hx : x∈Ω) (a : ℝ) :
    ‖projPath f Ω x a-x‖^2 ≤ -a*inner ℝ (gradient f x) (projPath f Ω x a-x) := by
  have hh:=nearest_inner Ω ⟨x,hx⟩ hc hv (x-a • gradient f x) x hx
  change inner ℝ (x-a • gradient f x-projPath f Ω x a) (x-projPath f Ω x a) ≤ 0 at hh
  have h1 : x-a • gradient f x-projPath f Ω x a = -(projPath f Ω x a-x)-a • gradient f x := by module
  have h2 : x-projPath f Ω x a = -(projPath f Ω x a-x) := by module
  rw [h1,h2,inner_sub_left,inner_neg_left,inner_neg_right,inner_neg_right,real_inner_smul_left,real_inner_self_eq_norm_sq] at hh
  nlinarith

private theorem path_compare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    {x : E} (hx : x∈Ω) (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a≤b) :
    ‖projPath f Ω x a-x‖ ≤ ‖projPath f Ω x b-x‖ ∧
    a*‖projPath f Ω x b-x‖ ≤ b*‖projPath f Ω x a-x‖ := by
  let da:=projPath f Ω x a-x
  let db:=projPath f Ω x b-x
  have h1:=nearest_inner Ω ⟨x,hx⟩ hc hv (x-a • gradient f x)
    (projPath f Ω x b) (proj_mem Ω ⟨x,hx⟩ hc hv (x-b • gradient f x))
  have h2:=nearest_inner Ω ⟨x,hx⟩ hc hv (x-b • gradient f x)
    (projPath f Ω x a) (proj_mem Ω ⟨x,hx⟩ hc hv (x-a • gradient f x))
  change inner ℝ (x-a • gradient f x-projPath f Ω x a) (projPath f Ω x b-projPath f Ω x a) ≤ 0 at h1
  change inner ℝ (x-b • gradient f x-projPath f Ω x b) (projPath f Ω x a-projPath f Ω x b) ≤ 0 at h2
  have he1 : x-a • gradient f x-projPath f Ω x a = -da-a • gradient f x := by dsimp [da]; module
  have he2 : x-b • gradient f x-projPath f Ω x b = -db-b • gradient f x := by dsimp [db]; module
  have he3 : projPath f Ω x b-projPath f Ω x a=db-da := by dsimp [da,db]; module
  have he4 : projPath f Ω x a-projPath f Ω x b=da-db := by dsimp [da,db]; module
  have healg (u v g : E) (t : ℝ) : inner ℝ (-u-t • g) (v-u) =
      ‖u‖^2-inner ℝ u v-t*(inner ℝ g v-inner ℝ g u) := by
    simp only [inner_sub_left,inner_neg_left,real_inner_smul_left,inner_sub_right,real_inner_self_eq_norm_sq]
    ring
  rw [he1,he3,healg] at h1
  rw [he2,he4,healg,real_inner_comm da db] at h2
  have hh1:=mul_nonpos_of_nonneg_of_nonpos hb.le h1
  have hh2:=mul_nonpos_of_nonneg_of_nonpos ha.le h2
  have hinner:=mul_le_mul_of_nonneg_left (real_inner_le_norm da db) (show 0≤a+b by linarith)
  have hpoly : (‖da‖-‖db‖)*(b*‖da‖-a*‖db‖) ≤ 0 := by nlinarith
  constructor
  · change ‖da‖≤‖db‖
    by_contra! hh
    have hp : 0 < b*‖da‖-a*‖db‖ := by nlinarith [norm_nonneg db]
    exact not_lt_of_ge hpoly (mul_pos (sub_pos.mpr hh) hp)
  · change a*‖db‖≤b*‖da‖
    by_contra! hh
    have hp : ‖da‖-‖db‖<0 := by nlinarith [norm_nonneg da]
    exact not_lt_of_ge hpoly (mul_pos_of_neg_of_neg hp (sub_neg.mpr hh))

private theorem path_scale_compare {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    {x : E} (hx : x∈Ω) (a b C : ℝ) (ha : 0<a) (hb : 0<b) (hC : 1≤C) (hab : b≤C*a) :
    ‖projPath f Ω x b-x‖ ≤ C*‖projPath f Ω x a-x‖ ∧
    ‖projPath f Ω x a-x‖/a ≤ C*(‖projPath f Ω x b-x‖/b) := by
  rcases le_total a b with h | h
  · have hh:=path_compare f Ω hc hv hx a b ha hb h
    constructor
    · nlinarith [hh.2,norm_nonneg (projPath f Ω x a-x)]
    · apply (div_le_iff₀ ha).mpr
      have hmul : b*(‖projPath f Ω x b-x‖/b)=‖projPath f Ω x b-x‖ := by field_simp
      nlinarith [hh.1,mul_nonneg (sub_nonneg.mpr hab) (div_nonneg (norm_nonneg (projPath f Ω x b-x)) hb.le)]
  · have hh:=path_compare f Ω hc hv hx b a hb ha h
    constructor
    · nlinarith [hh.1,norm_nonneg (projPath f Ω x a-x)]
    · have hr : ‖projPath f Ω x a-x‖/a ≤ ‖projPath f Ω x b-x‖/b := (div_le_div_iff₀ ha hb).mpr (by nlinarith [hh.2])
      nlinarith [mul_nonneg (sub_nonneg.mpr hC) (div_nonneg (norm_nonneg (projPath f Ω x b-x)) hb.le)]


private theorem model_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hv : Convex ℝ Ω)
    (hfd : ∀ x∈Ω,DifferentiableAt ℝ f x) {x y : E} (hx : x∈Ω) (hy : y∈Ω)
    (e : ℝ) (hb : ∀ z∈Ω,‖z-x‖ ≤ ‖y-x‖ → ‖gradient f z-gradient f x‖ ≤ e) :
    f y ≤ f x+inner ℝ (gradient f x) (y-x)+e*‖y-x‖ := by
  let d:=y-x
  let F : ℝ → ℝ := fun t => f (x+t • d)-t*inner ℝ (gradient f x) d
  have hmem (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : x+t • d∈Ω := hv.add_smul_sub_mem hx hy ht
  have hd (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : HasDerivAt F
      (inner ℝ (gradient f (x+t • d)-gradient f x) d) t := by
    have hl : HasDerivAt (fun s : ℝ => x+s • d) d t := by simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hh:=(hfd _ (hmem t ht)).hasFDerivAt.comp_hasDerivAt t hl
    rw [← inner_gradient_left] at hh
    convert! hh.sub ((hasDerivAt_id t).mul_const (inner ℝ (gradient f x) d)) using 1 <;> simp [F,inner_sub_left]
  have hnorm (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      ‖inner ℝ (gradient f (x+t • d)-gradient f x) d‖ ≤ e*‖d‖ := by
    have hdist : ‖x+t • d-x‖≤‖y-x‖ := by
      simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hb _ (hmem t ht) hdist) (norm_nonneg _))
  have hh:=norm_image_sub_le_of_norm_deriv_le_segment_01' (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => hnorm t ⟨ht.1,ht.2.le⟩)
  have hh':=(le_abs_self (F 1-F 0)).trans hh
  dsimp [F,d] at hh'
  simp only [one_smul,zero_smul,add_zero,one_mul,zero_mul,sub_zero,add_sub_cancel] at hh'
  linarith

private theorem uniform_model {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hv : Convex ℝ Ω)
    (hfd : ∀ x∈Ω,DifferentiableAt ℝ f x) (huc : UniformContinuousOn (gradient f) Ω) :
    ∀ e>0,∃ d>0,∀ x∈Ω,∀ y∈Ω,‖y-x‖<d →
      f y ≤ f x+inner ℝ (gradient f x) (y-x)+e*‖y-x‖ := by
  intro e he
  obtain ⟨d,hd,hδ⟩:=Metric.uniformContinuousOn_iff.mp huc e he
  refine ⟨d,hd,?_⟩
  intro x hx y hy hxy
  apply model_bound f Ω hv hfd hx hy e
  intro z hz hzx
  simpa only [dist_eq_norm] using (hδ z hz x hx (by simpa only [dist_eq_norm] using hzx.trans_lt hxy)).le

private theorem run_feasible {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    (g1 g2 u1 u2 : ℝ) (x : ℕ → E) (a : ℕ → ℝ)
    (hrun : IsGradientProjectionRun f Ω g1 g2 u1 u2 x a) : ∀ k,x k∈Ω := by
  intro k
  cases k with
  | zero => exact hrun.1
  | succ k => rw [(hrun.2 k).2.1]; exact proj_mem Ω hne hc hv _

private theorem run_energy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    (g1 g2 u1 u2 : ℝ) (hu : 0<u1) (x : ℕ → E) (a : ℕ → ℝ)
    (hrun : IsGradientProjectionRun f Ω g1 g2 u1 u2 x a) (hbdd : BddBelow (range (fun k => f (x k)))) :
    Tendsto (fun k => -inner ℝ (gradient f (x k)) (x (k+1)-x k)) atTop (𝓝 0) := by
  have hx:=run_feasible f Ω hne hc hv g1 g2 u1 u2 x a hrun
  have hn : ∀ k,0 ≤ -inner ℝ (gradient f (x k)) (x (k+1)-x k) := by
    intro k
    have hh:=path_inner f Ω hc hv (hx k) (a k)
    rw [← (hrun.2 k).2.1] at hh
    have ha:=(hrun.2 k).1
    nlinarith [sq_nonneg ‖x (k+1)-x k‖]
  have hmono : Antitone (fun k => f (x k)) := by
    apply antitone_nat_of_succ_le
    intro k
    have hh:=mul_nonneg hu.le (hn k)
    linarith [(hrun.2 k).2.2.1]
  have hf:=tendsto_atTop_ciInf hmono hbdd
  have hlim : Tendsto (fun k => (f (x k)-f (x (k+1)))/u1) atTop (𝓝 0) := by
    have hh:=(hf.sub (hf.comp (tendsto_add_atTop_nat 1))).div_const u1
    simpa only [Function.comp_def,sub_self,zero_div] using hh
  apply squeeze_zero hn _ hlim
  intro k
  apply (le_div_iff₀ hu).mpr
  nlinarith [(hrun.2 k).2.2.1]

private theorem ratio_small {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    {x : E} (hx : x∈Ω) (a g1 g2 u C t e d : ℝ)
    (ha : 0<a) (hg2 : 0<g2) (hu : u<1) (hC : 1≤C) (hCg : 1≤C*g2)
    (ht : 0<t) (htg : t≤g1) (ht1 : t≤1) (he : 0<e) (hd : 0<d)
    (hline : g1≤a ∨ ∃ b,0<g2*b ∧ g2*b≤a ∧
      f x+u*inner ℝ (gradient f x) (projPath f Ω x b-x)<f (projPath f Ω x b))
    (hmodel : ∀ y∈Ω,‖y-x‖<d → f y≤f x+inner ℝ (gradient f x) (y-x)+
      ((1-u)*e/(2*C))*‖y-x‖)
    (henergy1 : -inner ℝ (gradient f x) (projPath f Ω x a-x)<t*e^2)
    (henergy2 : -inner ℝ (gradient f x) (projPath f Ω x a-x)<(d/C)^2) :
    ‖projPath f Ω x a-x‖/a<e := by
  let A:=‖projPath f Ω x a-x‖
  let en := -inner ℝ (gradient f x) (projPath f Ω x a-x)
  have hA : A^2≤a*en := by
    dsimp [A,en]
    nlinarith [path_inner f Ω hc hv hx a]
  have hAn : 0≤A := norm_nonneg _
  have hen : 0≤en := by nlinarith [sq_nonneg A]
  have hCp : 0<C := by linarith
  by_cases hlarge : t≤a
  · have hh1:=mul_lt_mul_of_pos_left henergy1 ha
    have hh2:=mul_le_mul_of_nonneg_right hlarge (sq_nonneg e)
    have hh3:=mul_le_mul_of_nonneg_left hh2 ha.le
    apply (div_lt_iff₀ ha).mpr
    change A<e*a
    nlinarith [mul_pos he ha]
  · have hasmall : a<1 := lt_of_lt_of_le (lt_of_not_ge hlarge) ht1
    have hAde : A<d/C := by
      have hp : 0<d/C := div_pos hd hCp
      nlinarith [mul_nonneg (sub_nonneg.mpr hasmall.le) hen]
    have hCAd : C*A<d := by
      have hh:=(lt_div_iff₀ hCp).mp hAde
      nlinarith
    obtain ⟨b,hbp,hba,hbad⟩:=hline.resolve_left (by intro hh; exact hlarge (htg.trans hh))
    have hb : 0<b := (mul_pos_iff_of_pos_left hg2).mp hbp
    have hbCa : b≤C*a := by
      have hh:=mul_le_mul_of_nonneg_left hba hCp.le
      nlinarith [mul_nonneg (sub_nonneg.mpr hCg) hb.le]
    have hcmp:=path_scale_compare f Ω hc hv hx a b C ha hb hC hbCa
    let B:=‖projPath f Ω x b-x‖
    have hBd : B<d := lt_of_le_of_lt hcmp.1 hCAd
    have hm:=hmodel (projPath f Ω x b) (proj_mem Ω ⟨x,hx⟩ hc hv _) hBd
    have hBpos : 0<B := by
      have hBn : 0≤B := norm_nonneg _
      by_contra! hn
      have hz : projPath f Ω x b=x := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn hBn))
      rw [hz,sub_self,inner_zero_right,mul_zero,add_zero] at hbad
      exact lt_irrefl _ hbad
    have hB:=path_inner f Ω hc hv hx b
    let eta := (1-u)*e/(2*C)
    have hbad' : (1-u)*(-inner ℝ (gradient f x) (projPath f Ω x b-x))<eta*B := by
      dsimp [eta,B]
      linarith
    have hu' : 0<1-u := sub_pos.mpr hu
    have hproj:=mul_le_mul_of_nonneg_left hB hu'.le
    have hbadb:=mul_lt_mul_of_pos_left hbad' hb
    have hsq : (1-u)*B^2 < b*eta*B := by
      dsimp [B] at *
      nlinarith
    have hlin : (1-u)*B<b*eta := by nlinarith
    have heta : eta*(2*C)=(1-u)*e := by dsimp [eta]; field_simp
    have hlin2:=mul_lt_mul_of_pos_right hlin (show 0<2*C by positivity)
    have hBr : B/b<e/(2*C) := by
      apply (div_lt_div_iff₀ hb (show 0<2*C by positivity)).mpr
      nlinarith
    have hcbr:=mul_lt_mul_of_pos_left hBr hCp
    have hcancel : C*(e/(2*C))=e/2 := by field_simp <;> ring
    rw [hcancel] at hcbr
    have hr:=hcmp.2
    change A/a≤C*(B/b) at hr
    change A/a<e
    linarith


private theorem ratio_limit {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Ω : Set E) (hne : Ω.Nonempty) (hc : IsClosed Ω) (hv : Convex ℝ Ω)
    (g1 g2 u1 u2 : ℝ) (hg1 : 0<g1) (hg2 : 0<g2) (hu2 : u2<1)
    (x : ℕ → E) (a : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω g1 g2 u1 u2 x a)
    (L : Filter ℕ) (S : Set E) (hS : ∀ᶠ k in L,x k∈S)
    (henergy : Tendsto (fun k => -inner ℝ (gradient f (x k)) (x (k+1)-x k)) L (𝓝 0))
    (hmodel : ∀ e>0,∃ d>0,∀ z∈S,∀ y∈Ω,‖y-z‖<d →
      f y≤f z+inner ℝ (gradient f z) (y-z)+e*‖y-z‖) :
    Tendsto (fun k => ‖x (k+1)-x k‖/a k) L (𝓝 0) := by
  have hx:=run_feasible f Ω hne hc hv g1 g2 u1 u2 x a hrun
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall fun k => hb.trans_le (div_nonneg (norm_nonneg _) (hrun.2 k).1.le)
  · intro e he
    let C:=max 1 (1/g2)
    let t:=min g1 1
    have hC : 1≤C := le_max_left _ _
    have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
    have hCg : 1≤C*g2 := (div_le_iff₀ hg2).mp (le_max_right _ _)
    have ht : 0<t := lt_min hg1 zero_lt_one
    have heta : 0<(1-u2)*e/(2*C) := div_pos (mul_pos (sub_pos.mpr hu2) he) (by positivity)
    obtain ⟨d,hd,hδ⟩:=hmodel ((1-u2)*e/(2*C)) heta
    have hthr : 0 < min (t*e^2) ((d/C)^2) := lt_min (mul_pos ht (sq_pos_of_pos he)) (sq_pos_of_pos (div_pos hd hCp))
    have hevent:=(tendsto_order.mp henergy).2 _ hthr
    filter_upwards [hevent,hS] with k hk hkS
    have hh:=ratio_small f Ω hc hv (hx k) (a k) g1 g2 u2 C t e d (hrun.2 k).1 hg2 hu2 hC hCg ht
      (min_le_left _ _) (min_le_right _ _) he hd (hrun.2 k).2.2.2 (hδ (x k) hkS)
    rw [← (hrun.2 k).2.1] at hh
    exact hh (hk.trans_le (min_le_left _ _)) (hk.trans_le (min_le_right _ _))

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (γ₁ γ₂ μ₁ μ₂ : ℝ) (hγ₁ : 0 < γ₁) (hγ₂ : 0 < γ₂)
    (hμ₁ : μ₁ ∈ Set.Ioo (0 : ℝ) 1) (hμ₂ : μ₂ ∈ Set.Ioo (0 : ℝ) 1)
    (x : ℕ → E) (α : ℕ → ℝ) (hrun : IsGradientProjectionRun f Ω γ₁ γ₂ μ₁ μ₂ x α)
    (hbdd : BddBelow (f '' Ω)) (huc : UniformContinuousOn (gradient f) Ω) :
    Filter.Tendsto (fun k => ‖x (k + 1) - x k‖ / α k) Filter.atTop (nhds 0) := by
  have hx:=run_feasible f Ω hΩne hΩc hΩcv γ₁ γ₂ μ₁ μ₂ x α hrun
  have hb : BddBelow (range (fun k => f (x k))) := by
    obtain ⟨b,hb⟩:=hbdd
    refine ⟨b,?_⟩
    rintro _ ⟨k,rfl⟩
    exact hb ⟨x k,hx k,rfl⟩
  exact ratio_limit f Ω hΩne hΩc hΩcv γ₁ γ₂ μ₁ μ₂ hγ₁ hγ₂ hμ₂.2 x α hrun atTop Ω
    (Filter.Eventually.of_forall hx) (run_energy f Ω hΩne hΩc hΩcv γ₁ γ₂ μ₁ μ₂ hμ₁.1 x α hrun hb)
    (uniform_model f Ω hΩcv hfd huc)

