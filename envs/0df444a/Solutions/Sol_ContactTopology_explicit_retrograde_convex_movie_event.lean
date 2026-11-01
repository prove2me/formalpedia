-- Prove2me | solution 1 for ContactTopology.explicit_retrograde_convex_movie_event
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T06:28:27.581559+00:00
-- url     : https://prove2.me/submissions/fb90f1cc-567e-4651-a318-3a59501283bd

import Definitions.Def_ContactTopology_RetrogradeMovie
import Definitions.Def_ContactTopology_TwoArcJetDisk
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Separation.Hausdorff


namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

def chart (z : Space) : Space :=
  ![z 0,z 0*z 1-z 2,z 0*z 2+(1-z 0^2)*z 1]
def inverse (p : Space) : Space :=
  ![p 0,p 2+p 0*p 1,p 0*p 2-(1-p 0^2)*p 1]
def level (p : Space) : ℝ := p 0*p 2-(1-p 0^2)*p 1
lemma chart_smooth : ContDiff ℝ ∞ chart := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [chart] <;> fun_prop
lemma inverse_smooth : ContDiff ℝ ∞ inverse := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [inverse] <;> fun_prop
lemma inverse_chart (z : Space) : inverse (chart z)=z := by
  ext i; fin_cases i <;> simp [inverse,chart] <;> ring
lemma chart_inverse (p : Space) : chart (inverse p)=p := by
  ext i; fin_cases i <;> simp [inverse,chart] <;> ring
lemma model_smooth : ContDiff ℝ ∞ (fun p : ℝ × Plane => model p.1 p.2) := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [model] <;> fun_prop
lemma level_smooth : ContDiff ℝ ∞ level := by unfold level; fun_prop
lemma level_model (t : ℝ) (u : Plane) : level (model t u)=t := by
  dsimp [level,model]; ring
lemma recover_model (t : ℝ) (u : Plane) :
    ![(model t u) 0,(model t u) 2+(model t u) 0*(model t u) 1]=u := by
  ext i; fin_cases i <;> simp [model] <;> ring
lemma model_injective (t : ℝ) : Injective (model t) := by
  intro u v he
  have hh := congrArg (fun p : Space => ![p 0,p 2+p 0*p 1]) he
  simpa only [recover_model] using hh

def modelVelocity (t : ℝ) (u v : Plane) : Space :=
  ![v 0,u 1*v 0+u 0*v 1,(t-2*u 0*u 1)*v 0+(1-u 0^2)*v 1]
def modelDerivative (t : ℝ) (u : Plane) : Plane →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := modelVelocity t u
      map_add' := by intro v w; ext i; fin_cases i <;> simp [modelVelocity] <;> ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp [modelVelocity] <;> ring }

lemma model_hasFDerivAt (t : ℝ) (u : Plane) : HasFDerivAt (model t) (modelDerivative t u) u := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun u : Plane => u i) (e i) u := (e i).hasFDerivAt
  rw [hasFDerivAt_pi']
  intro i
  fin_cases i
  · exact h 0
  · convert! ((h 0).mul (h 1)).sub_const t using 1 <;>
      ext v <;> simp [modelDerivative,modelVelocity,e] <;> ring
  · convert! ((h 0).mul_const t).add (((hasFDerivAt_const (1:ℝ) u).sub ((h 0).pow 2)).mul (h 1)) using 1 <;>
      ext v <;> simp [modelDerivative,modelVelocity,e] <;> ring

lemma model_fderiv (t : ℝ) (u v : Plane) :
    fderiv ℝ (model t) u v=modelVelocity t u v :=
  congrArg (fun L : Plane →L[ℝ] Space => L v) (model_hasFDerivAt t u).fderiv

lemma model_immersed (t : ℝ) (u : Plane) : Injective (fderiv ℝ (model t) u) := by
  -- The direct linear recovery works at every parameter, including the saddles.
  intro v w he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  rw [model_fderiv,model_fderiv] at h0 h1 h2
  dsimp [modelVelocity] at h0 h1 h2
  ext i
  fin_cases i
  · exact h0
  · change v 1=w 1
    by_cases hu : u 0=0
    · rw [h0] at h2
      simpa [hu] using h2
    · apply mul_left_cancel₀ hu
      rw [h0] at h1
      linarith

lemma model_pullback (t : ℝ) (u v : Plane) :
    jetForm (model t u) (fderiv ℝ (model t) u v)=
      (2*t-3*u 0*u 1)*v 0+(1-u 0^2)*v 1 := by
  rw [model_fderiv]
  dsimp [jetForm,model,modelVelocity]
  ring

lemma characteristic_tangent (t : ℝ) (u : Plane) :
    jetForm (model t u) (fderiv ℝ (model t) u (characteristic t u))=0 := by
  rw [model_pullback]
  dsimp [characteristic]
  ring

lemma characteristic_singularities (t : ℝ) (u : Plane) :
    characteristic t u=0 ↔
      (u= ![-1,-2*t/3] ∨ u= ![1,2*t/3]) := by
  constructor
  · intro he
    have h0 := congrFun he 0
    have h1 := congrFun he 1
    dsimp [characteristic] at h0 h1
    have hx : u 0= -1 ∨ u 0=1 := by
      rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (show u 0^2=1^2 by linarith)) with hx|hx
      · exact Or.inr hx
      · exact Or.inl hx
    rcases hx with hx|hx
    · rw [hx] at h1
      left; ext i; fin_cases i <;> dsimp <;> linarith
    · rw [hx] at h1
      right; ext i; fin_cases i <;> dsimp <;> linarith
  · rintro (rfl|rfl) <;> ext i <;> fin_cases i <;> norm_num [characteristic] <;> ring

lemma euler_smooth : ContDiff ℝ ∞ euler := by
  apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [euler] <;> fun_prop

def eulerLinear : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := euler
      map_add' := by intro v w; ext i; fin_cases i <;> simp [euler]
      map_smul' := by intro a v; ext i; fin_cases i <;> simp [euler] }

lemma euler_fderiv (p v : Space) : fderiv ℝ euler p v=euler v :=
  congrArg (fun L : Space →L[ℝ] Space => L v) eulerLinear.hasFDerivAt.fderiv

lemma euler_contact (p v : Space) :
    -(euler p 1)*v 0+jetForm p (fderiv ℝ euler p v)=jetForm p v := by
  rw [euler_fderiv]
  simp [euler,jetForm]
  ring

lemma euler_transverse (t : ℝ) (ht : t≠0) (u v : Plane) :
    euler (model t u)≠fderiv ℝ (model t) u v := by
  intro he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  rw [model_fderiv] at h0 h1 h2
  dsimp [euler,model,modelVelocity] at h0 h1 h2
  have he0 : v 0=0 := h0.symm
  rw [he0] at h1 h2
  apply ht
  linear_combination u 0*h2-(1-u 0^2)*h1

lemma euler_dividing (t : ℝ) (u : Plane) :
    jetForm (model t u) (euler (model t u))=dividing t u := by simp [jetForm,model,euler,dividing]

lemma weighted_rolle (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1:ℝ) 1))
    (hdh : ∀ x ∈ Ioo (-1:ℝ) 1, DifferentiableAt ℝ h x) :
    ∃ x ∈ Ioo (-1:ℝ) 1, x*h x-(1-x^2)*deriv h x=0 := by
  let g : ℝ → ℝ := fun x => h x*Real.sqrt (1-x^2)
  have hc : ContinuousOn g (Icc (-1:ℝ) 1) := by
    exact hh.mul ((by fun_prop : Continuous (fun x : ℝ => Real.sqrt (1-x^2))).continuousOn)
  obtain ⟨x,hx,hzero⟩ := exists_deriv_eq_zero (by norm_num : (-1:ℝ)<1) hc (by simp [g])
  have hp : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
  have hs : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hp).ne'
  have hd := (hdh x hx).hasDerivAt.mul
    ((Real.hasDerivAt_sqrt hp.ne').comp x ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)))
  change HasDerivAt g _ x at hd
  rw [hd.deriv] at hzero
  refine ⟨x,hx,?_⟩
  have hsquare := Real.sq_sqrt hp.le
  field_simp [hs] at hzero
  dsimp at hzero
  norm_num at hzero
  linear_combination -hzero/2+deriv h x*hsquare

theorem exceptional_slice_has_no_transverse_contact_field
    (Y : Space → Space) (O : Set Space) (hO : IsOpen O)
    (hseg : ∀ x ∈ Icc (-1:ℝ) 1, model 0 ![x,0] ∈ O)
    (hY : ContDiffOn ℝ ∞ Y O)
    (hcontact : ∀ p ∈ O, ∃ a : ℝ, ∀ v : Space,
      -(Y p 1)*v 0+jetForm p (fderiv ℝ Y p v)=a*jetForm p v) :
    ∃ x ∈ Ioo (-1:ℝ) 1, ∃ v : Plane,
      Y (model 0 ![x,0])=fderiv ℝ (model 0) ![x,0] v := by
  let line : ℝ → Space := fun x => ![x,0,0]
  have hl : ContDiff ℝ ∞ line := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> dsimp [line] <;> fun_prop
  let h : ℝ → ℝ := fun x => Y (line x) 2
  have hm (x : ℝ) : model 0 ![x,0]=line x := by simp [model,line]
  have hmem (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : line x ∈ O := by rw [← hm]; exact hseg x hx
  have hAt (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : ContDiffAt ℝ ∞ Y (line x) :=
    hY.contDiffAt (hO.mem_nhds (hmem x hx))
  have hh : ContinuousOn h (Icc (-1:ℝ) 1) :=
    (continuous_apply 2).comp_continuousOn (hY.continuousOn.comp hl.continuous.continuousOn hmem)
  have hdh (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) : DifferentiableAt ℝ h x :=
    (((contDiff_apply ℝ ℝ 2).contDiffAt.comp x ((hAt x ⟨hx.1.le,hx.2.le⟩).comp x hl.contDiffAt))).differentiableAt (by simp)
  have hder (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) : deriv h x=Y (line x) 1 := by
    have hline : HasDerivAt line (Pi.single 0 1) x := by
      apply hasDerivAt_pi.mpr
      intro i
      fin_cases i
      · exact hasDerivAt_id x
      · simpa [line] using hasDerivAt_const x (0:ℝ)
      · simpa [line] using hasDerivAt_const x (0:ℝ)
    have hdvec := ((hAt x hx).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt x hline
    have hd := (ContinuousLinearMap.proj (2:Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt x hdvec
    have hd' : deriv h x=fderiv ℝ Y (line x) (Pi.single 0 1) 2 := hd.deriv
    obtain ⟨a,ha⟩ := hcontact (line x) (hmem x hx)
    have he := ha (Pi.single 0 1)
    simp [jetForm,line] at he
    rw [hd']
    linarith
  obtain ⟨x,hx,he⟩ := weighted_rolle h hh hdh
  rw [hder x ⟨hx.1.le,hx.2.le⟩] at he
  refine ⟨x,hx,![Y (line x) 0,Y (line x) 2+x*Y (line x) 1],?_⟩
  rw [model_fderiv,hm]
  change x*Y (line x) 2-(1-x^2)*Y (line x) 1=0 at he
  have he1 : Y (line x) 1=x*(Y (line x) 2+x*Y (line x) 1) := by
    linear_combination -he
  have he2 : Y (line x) 2=(1-x^2)*(Y (line x) 2+x*Y (line x) 1) := by
    linear_combination x*he
  ext i
  fin_cases i
  · simp [modelVelocity]
  · simpa [modelVelocity] using he1
  · simpa [modelVelocity] using he2

end
end ContactTopology.RetrogradeMovie

namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function Topology
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma roots (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < inner t ∧ inner t < 1 ∧ 1 < outer t ∧ outer t < 2 ∧
      inner t^2+t*inner t=1 ∧ outer t^2-t*outer t=1 := by
  have hp : 0 < t^2+4 := by positivity
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_nonneg (t^2+4)
  have hgt : t  <  Real.sqrt (t^2+4) := by nlinarith
  have htwo : 2  <  Real.sqrt (t^2+4) := by nlinarith
  dsimp [inner,outer]
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor <;> nlinarith [hs]

lemma scalar_intervals (t x : ℝ) (ht : 0 < t) (ht1 : t < 1) (hx : |x|≤2) :
    |t*x|≤|1-x^2| ↔
      x ∈ interval t 0 ∨ x ∈ interval t 1 ∨ x ∈ interval t 2 := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  change |t*x|≤|1-x^2| ↔
    (x ∈ Icc (-2) (-outer t) ∨ x ∈ Icc (-inner t) (inner t) ∨ x ∈ Icc (outer t) 2)
  have habs : |t*x|=t*|x| := by rw [abs_mul,abs_of_pos ht]
  rw [habs]
  by_cases hsign : 0≤x
  · rw [abs_of_nonneg hsign]
    by_cases hunit : x≤1
    · have hf : 0≤1-x^2 := by nlinarith
      rw [abs_of_nonneg hf]
      constructor
      · intro he
        right; left; constructor
        · linarith
        · nlinarith
      · rintro (he|he|he)
        · exfalso; linarith [he.2]
        · nlinarith [he.2]
        · exfalso; linarith [he.1]
    · have hf : 1-x^2 < 0 := by nlinarith
      rw [abs_of_neg hf]
      constructor
      · intro he
        right; right; constructor
        · nlinarith
        · exact hxhi
      · rintro (he|he|he)
        · exfalso; linarith [he.2]
        · exfalso; linarith [he.2]
        · nlinarith [he.1]
  · have hneg : x < 0 := lt_of_not_ge hsign
    rw [abs_of_neg hneg]
    by_cases hunit : -1≤x
    · have hf : 0≤1-x^2 := by nlinarith
      rw [abs_of_nonneg hf]
      constructor
      · intro he
        right; left; constructor
        · nlinarith
        · linarith
      · rintro (he|he|he)
        · exfalso; linarith [he.2]
        · nlinarith [he.1]
        · exfalso; linarith [he.1]
    · have hf : 1-x^2 < 0 := by nlinarith
      rw [abs_of_neg hf]
      constructor
      · intro he
        left; constructor
        · exact hxlo
        · nlinarith
      · rintro (he|he|he)
        · nlinarith [he.2]
        · exfalso; linarith [he.1]
        · exfalso; linarith [he.1]

lemma interval_denominator (t x : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (j : Fin 3) (hx : x ∈ interval t j) : 1-x^2≠0 := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  fin_cases j
  · change x ∈ Icc (-2) (-outer t) at hx
    nlinarith [hx.2]
  · change x ∈ Icc (-inner t) (inner t) at hx
    nlinarith [hx.1,hx.2]
  · change x ∈ Icc (outer t) 2 at hx
    nlinarith [hx.1]

lemma graph_dividing (t x : ℝ) (hx : 1-x^2≠0) : dividing t (graph t x)=0 := by
  dsimp [graph,dividing]
  field_simp [hx]
  ring

lemma dividing_graph (t : ℝ) (ht : t≠0) (u : Plane) (hu : dividing t u=0) :
    1-u 0^2≠0 ∧ u=graph t (u 0) := by
  have he : u 0*t+(1-u 0^2)*u 1=0 := hu
  have hn : 1-u 0^2≠0 := by
    intro hn
    have hx : u 0=0 := (mul_eq_zero.mp (by simpa [hn] using he)).resolve_right ht
    simp [hx] at hn
  refine ⟨hn,?_⟩
  ext i
  fin_cases i
  · rfl
  · change u 1= -t*u 0/(1-u 0^2)
    apply (eq_div_iff hn).mpr
    nlinarith

lemma graph_in_box_iff (t x : ℝ) (ht : 0 < t) (ht1 : t < 1) (hx : 1-x^2≠0) :
    graph t x ∈ box ↔ x ∈ interval t 0 ∨ x ∈ interval t 1 ∨ x ∈ interval t 2 := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  have he : |(-t*x)/(1-x^2)|≤1 ↔ |t*x|≤|1-x^2| := by
    rw [abs_div,div_le_one (abs_pos.mpr hx)]
    simp [abs_mul]
  change (|x|≤2 ∧ |(-t*x)/(1-x^2)|≤1) ↔ _
  rw [he]
  constructor
  · intro hh; exact (scalar_intervals t x ht ht1 hh.1).mp hh.2
  · intro hh
    have hbound : |x|≤2 := by
      apply abs_le.mpr
      rcases hh with hh|hh|hh
      · change x ∈ Icc (-2) (-outer t) at hh; constructor <;> linarith [hh.1,hh.2]
      · change x ∈ Icc (-inner t) (inner t) at hh; constructor <;> linarith [hh.1,hh.2]
      · change x ∈ Icc (outer t) 2 at hh; constructor <;> linarith [hh.1,hh.2]
    exact ⟨hbound,(scalar_intervals t x ht ht1 hbound).mpr hh⟩

lemma graph_smooth (t x : ℝ) (hx : 1-x^2≠0) : ContDiffAt ℝ ∞ (graph t) x := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [graph] <;> fun_prop (disch := assumption)

lemma interval_eq (t : ℝ) (j : Fin 3) : interval t j=Icc (bounds t j).1 (bounds t j).2 := by
  fin_cases j <;> rfl

lemma physicalArc_embedding (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3) :
    IsEmbedding (physicalArc t j) := by
  have hc : Continuous (physicalArc t j) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hx : (x:ℝ) ∈ interval t j := by rw [interval_eq]; exact x.property
    exact (((model_smooth.comp (contDiff_const.prodMk contDiff_id)).contDiffAt.comp x.val
      (graph_smooth t x.val (interval_denominator t x.val ht ht1 j hx))).continuousAt.comp
      continuous_subtype_val.continuousAt)
  apply hc.isClosedEmbedding ?_ |>.isEmbedding
  intro x y he
  have hp := model_injective t he
  apply Subtype.ext
  exact congrArg (fun u : Plane => u 0) hp

lemma physical_dividing_set (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    {p : Space | ∃ u ∈ box, model t u=p ∧ jetForm p (euler p)=0}=
      range (physicalArc t 0) ∪ range (physicalArc t 1) ∪ range (physicalArc t 2) := by
  ext p
  constructor
  · rintro ⟨u,hu,rfl,hzero⟩
    rw [euler_dividing] at hzero
    obtain ⟨hn,hgraph⟩ := dividing_graph t ht.ne' u hzero
    have hintervals := (graph_in_box_iff t (u 0) ht ht1 hn).mp (by rwa [← hgraph])
    rcases hintervals with hx|hx|hx
    · left; left; refine ⟨⟨u 0,?_⟩,?_⟩
      · rwa [← interval_eq]
      · exact congrArg (model t) hgraph.symm
    · left; right; refine ⟨⟨u 0,?_⟩,?_⟩
      · rwa [← interval_eq]
      · exact congrArg (model t) hgraph.symm
    · right; refine ⟨⟨u 0,?_⟩,?_⟩
      · rwa [← interval_eq]
      · exact congrArg (model t) hgraph.symm
  · have hinc (j : Fin 3) (x : Icc (bounds t j).1 (bounds t j).2) :
        physicalArc t j x ∈ {p : Space | ∃ u ∈ box, model t u=p ∧ jetForm p (euler p)=0} := by
      have hx : x.val ∈ interval t j := by simpa only [interval_eq] using x.property
      have hn := interval_denominator t x.val ht ht1 j hx
      refine ⟨graph t x.val,?_,rfl,?_⟩
      · apply (graph_in_box_iff t x.val ht ht1 hn).mpr
        fin_cases j
        · exact Or.inl hx
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
      · exact (euler_dividing t (graph t x.val)).trans (graph_dividing t x.val hn)
    rintro ((⟨x,rfl⟩|⟨x,rfl⟩)|⟨x,rfl⟩)
    · exact hinc 0 x
    · exact hinc 1 x
    · exact hinc 2 x

lemma graph_from_zero (t : ℝ) (ht : t≠0) (x y : ℝ)
    (he : x*t+(1-x^2)*y=0) : graph t x=![x,y] :=
  (dividing_graph t ht ![x,y] he).2.symm

lemma endpoint_graphs (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3) :
    graph t (bounds t j).1=leftEnd t j ∧ graph t (bounds t j).2=rightEnd t j := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  fin_cases j
  · dsimp [bounds,leftEnd,rightEnd]
    constructor
    · apply graph_from_zero t ht.ne'; ring
    · apply graph_from_zero t ht.ne'; linear_combination hbq
  · dsimp [bounds,leftEnd,rightEnd]
    constructor
    · apply graph_from_zero t ht.ne'; linear_combination -haq
    · apply graph_from_zero t ht.ne'; linear_combination haq
  · dsimp [bounds,leftEnd,rightEnd]
    constructor
    · apply graph_from_zero t ht.ne'; linear_combination -hbq
    · apply graph_from_zero t ht.ne'; ring

lemma bounds_order (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3) :
    (bounds t j).1 < (bounds t j).2 := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  fin_cases j <;> dsimp [bounds] <;> linarith

lemma physicalArc_endpoints (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3)
    (x : Icc (bounds t j).1 (bounds t j).2) :
    (x.val=(bounds t j).1 → physicalArc t j x=model t (leftEnd t j)) ∧
    (x.val=(bounds t j).2 → physicalArc t j x=model t (rightEnd t j)) := by
  constructor
  · intro he; change model t (graph t x.val)=_; rw [he,(endpoint_graphs t ht ht1 j).1]
  · intro he; change model t (graph t x.val)=_; rw [he,(endpoint_graphs t ht ht1 j).2]

lemma physicalArc_smooth_regular (t x : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (j : Fin 3) (hx : x ∈ interval t j) :
    ContDiffAt ℝ ∞ (model t ∘ graph t) x ∧ deriv (model t ∘ graph t) x≠0 := by
  have hg := graph_smooth t x (interval_denominator t x ht ht1 j hx)
  have hm : ContDiff ℝ ∞ (model t) := model_smooth.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨hm.contDiffAt.comp x hg,?_⟩
  have hdg := (hg.differentiableAt (by simp)).hasDerivAt
  have h0 : deriv (graph t) x 0=1 :=
    (hasDerivAt_pi.mp hdg 0).unique (hasDerivAt_id x)
  intro he
  have hd := (model_hasFDerivAt t (graph t x)).comp_hasDerivAt x hdg
  have hz : fderiv ℝ (model t) (graph t x) (deriv (graph t) x)=0 := by
    rw [model_fderiv]
    change (modelDerivative t (graph t x)) (deriv (graph t) x)=0
    rw [← hd.deriv]
    exact he
  have hz' : deriv (graph t) x=0 := (model_immersed t (graph t x)) (by simpa using hz)
  have hh := congrFun hz' 0
  rw [h0] at hh
  norm_num at hh

lemma physicalArcs_disjoint (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (i j : Fin 3) (hij : i≠j) : Disjoint (range (physicalArc t i)) (range (physicalArc t j)) := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  apply Set.disjoint_left.mpr
  rintro p ⟨x,rfl⟩ ⟨y,he⟩
  have hxy : y.val=x.val := congrArg (fun p : Space => p 0) he
  have hx := x.property
  have hy := y.property
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals dsimp [bounds] at hx hy; linarith [hx.1,hx.2,hy.1,hy.2]

lemma reflect_reflect (p : Space) : reflect (reflect p)=p := by
  ext i; fin_cases i <;> simp [reflect]
lemma mirror_mirror (u : Plane) : mirror (mirror u)=u := by
  ext i; fin_cases i <;> simp [mirror]
lemma mirror_box (u : Plane) : mirror u ∈ box ↔ u ∈ box := by simp [mirror,box]
lemma negative_model (t : ℝ) (u : Plane) : model (-t) (mirror u)=reflect (model t u) := by
  ext i; fin_cases i <;> simp [model,mirror,reflect] <;> ring
lemma reflected_pairing (p : Space) :
    jetForm (reflect p) (euler (reflect p))= -jetForm p (euler p) := by
  simp [jetForm,reflect,euler]

lemma physicalZero_negative (t : ℝ) : physicalZero (-t)=reflect '' physicalZero t := by
  ext p
  constructor
  · rintro ⟨u,hu,rfl,hzero⟩
    refine ⟨model t (mirror u),?_,?_⟩
    · refine ⟨mirror u,(mirror_box u).mpr hu,rfl,?_⟩
      have hm : model t (mirror u)=reflect (model (-t) u) := by simpa using negative_model (-t) u
      rw [hm,reflected_pairing,hzero,neg_zero]
    · have hm := negative_model t (mirror u)
      simpa [mirror_mirror] using hm.symm
  · rintro ⟨p,⟨u,hu,rfl,hzero⟩,rfl⟩
    refine ⟨mirror u,(mirror_box u).mpr hu,negative_model t u,?_⟩
    rw [reflected_pairing,hzero,neg_zero]

lemma physical_dividing_set_negative (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    physicalZero (-t)=range (reflect ∘ physicalArc t 0) ∪
      range (reflect ∘ physicalArc t 1) ∪ range (reflect ∘ physicalArc t 2) := by
  rw [physicalZero_negative]
  change reflect '' {p : Space | ∃ u ∈ box, model t u=p ∧ jetForm p (euler p)=0}=_
  rw [physical_dividing_set t ht ht1]
  simp only [image_union,← range_comp]

lemma root_difference (t : ℝ) : outer t=inner t+t := by dsimp [inner,outer]; ring

lemma boundary_candidates (t x : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hx : 1-x^2≠0) (hb : graph t x ∈ boxBoundary) :
    x= -2 ∨ x= -outer t ∨ x= -inner t ∨ x=inner t ∨ x=outer t ∨ x=2 := by
  obtain ⟨ha,ha1,hout,hout2,haq,hbq⟩ := roots t ht ht1
  have he : x*t+(1-x^2)*(graph t x 1)=0 := graph_dividing t x hx
  rcases hb.2 with he2|he1
  · change |x|=2 at he2
    rcases (abs_eq (by norm_num : 0≤(2:ℝ))).mp he2 with h|h <;> aesop
  · rcases (abs_eq (by norm_num : 0≤(1:ℝ))).mp he1 with h|h
    · rw [h] at he
      have hf : (x-outer t)*(x+inner t)=0 := by
        rw [root_difference]
        linear_combination -he-haq
      rcases mul_eq_zero.mp hf with hf|hf
      · have hh : x=outer t := sub_eq_zero.mp hf; aesop
      · have hh : x= -inner t := eq_neg_of_add_eq_zero_left hf; aesop
    · rw [h] at he
      have hf : (x-inner t)*(x+outer t)=0 := by
        rw [root_difference]
        linear_combination he-haq
      rcases mul_eq_zero.mp hf with hf|hf
      · have hh : x=inner t := sub_eq_zero.mp hf; aesop
      · have hh : x= -outer t := eq_neg_of_add_eq_zero_left hf; aesop

lemma endpoints_on_boundary (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3) :
    leftEnd t j ∈ boxBoundary ∧ rightEnd t j ∈ boxBoundary := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  have hy : |2*t/3|≤1 := by rw [abs_div,abs_mul,abs_of_pos ht]; norm_num; linarith
  have hyneg : |-2*t/3|≤1 := by
    simpa only [show -2*t/3= -(2*t/3) by ring,abs_neg] using hy
  have hbpos : 0 < outer t := lt_trans (by norm_num : (0:ℝ)<1) hb
  fin_cases j
  · constructor
    · refine ⟨⟨by norm_num [leftEnd],?_⟩,Or.inl (by norm_num [leftEnd])⟩
      exact hyneg
    · refine ⟨⟨?_,by norm_num [rightEnd]⟩,Or.inr (by norm_num [rightEnd])⟩
      change |-outer t|≤2
      rw [abs_neg,abs_of_pos hbpos]
      exact hb2.le
  · constructor
    · refine ⟨⟨?_,by norm_num [leftEnd]⟩,Or.inr (by norm_num [leftEnd])⟩
      change |-inner t|≤2
      rw [abs_neg,abs_of_pos ha]
      linarith
    · refine ⟨⟨?_,by norm_num [rightEnd]⟩,Or.inr (by norm_num [rightEnd])⟩
      change |inner t|≤2
      rw [abs_of_pos ha]
      linarith
  · constructor
    · refine ⟨⟨?_,by norm_num [leftEnd]⟩,Or.inr (by norm_num [leftEnd])⟩
      change |outer t|≤2
      rw [abs_of_pos hbpos]
      exact hb2.le
    · exact ⟨⟨by norm_num [rightEnd],hy⟩,Or.inl (by norm_num [rightEnd])⟩

lemma graph_boundary_iff (t x : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (j : Fin 3) (hx : x ∈ interval t j) :
    graph t x ∈ boxBoundary ↔ x=(bounds t j).1 ∨ x=(bounds t j).2 := by
  obtain ⟨ha,ha1,hb,hb2,haq,hbq⟩ := roots t ht ht1
  constructor
  · intro hbound
    have hcan := boundary_candidates t x ht ht1 (interval_denominator t x ht ht1 j hx) hbound
    rw [interval_eq] at hx
    fin_cases j <;> dsimp [bounds] at hx ⊢
    all_goals
      rcases hcan with hc|hc|hc|hc|hc|hc
      all_goals first | exact Or.inl hc | exact Or.inr hc | (exfalso; linarith [hx.1,hx.2])
  · rintro (rfl|rfl)
    · rw [(endpoint_graphs t ht ht1 j).1]
      exact (endpoints_on_boundary t ht ht1 j).1
    · rw [(endpoint_graphs t ht ht1 j).2]
      exact (endpoints_on_boundary t ht ht1 j).2

lemma physicalArc_proper (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3)
    (x : Icc (bounds t j).1 (bounds t j).2) :
    physicalArc t j x ∈ model t '' boxBoundary ↔
      x.val=(bounds t j).1 ∨ x.val=(bounds t j).2 := by
  have hx : x.val ∈ interval t j := by simpa only [interval_eq] using x.property
  rw [← graph_boundary_iff t x.val ht ht1 j hx]
  constructor
  · rintro ⟨u,hu,he⟩
    have hh : u=graph t x.val := model_injective t he
    rwa [← hh]
  · intro hh; exact ⟨graph t x.val,hh,rfl⟩

def reflectLinear : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := reflect
      map_add' := by intro v w; ext i; fin_cases i <;> simp [reflect] <;> ring
      map_smul' := by intro a v; ext i; fin_cases i <;> simp [reflect] }

lemma reflect_smooth : ContDiff ℝ ∞ reflect := reflectLinear.contDiff
lemma reflect_embedding : IsEmbedding reflect :=
  (show LeftInverse reflect reflect from reflect_reflect).isEmbedding reflect_smooth.continuous reflect_smooth.continuous

lemma negativeArc_embedding (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3) :
    IsEmbedding (reflect ∘ physicalArc t j) := reflect_embedding.comp (physicalArc_embedding t ht ht1 j)

lemma negativeArc_smooth_regular (t x : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (j : Fin 3) (hx : x ∈ interval t j) :
    ContDiffAt ℝ ∞ (reflect ∘ model t ∘ graph t) x ∧
      deriv (reflect ∘ model t ∘ graph t) x≠0 := by
  obtain ⟨hs,hr⟩ := physicalArc_smooth_regular t x ht ht1 j hx
  refine ⟨reflect_smooth.contDiffAt.comp x hs,?_⟩
  have hd := reflectLinear.hasFDerivAt.comp_hasDerivAt x ((hs.differentiableAt (by simp)).hasDerivAt)
  intro he
  have hz : reflect (deriv (model t ∘ graph t) x)=0 := by
    change reflectLinear (deriv (model t ∘ graph t) x)=0
    rw [← hd.deriv]
    exact he
  have hh := congrArg reflect hz
  rw [reflect_reflect] at hh
  apply hr
  calc
    _ = reflect 0 := hh
    _ = 0 := by ext i; fin_cases i <;> simp [reflect]

lemma mirror_boundary (u : Plane) : mirror u ∈ boxBoundary ↔ u ∈ boxBoundary := by
  simp [mirror,boxBoundary,box]

lemma reflected_boundary (t : ℝ) (p : Space) :
    reflect p ∈ model (-t) '' boxBoundary ↔ p ∈ model t '' boxBoundary := by
  constructor
  · rintro ⟨u,hu,he⟩
    refine ⟨mirror u,(mirror_boundary u).mpr hu,?_⟩
    have hm : model t (mirror u)=reflect (model (-t) u) := by simpa using negative_model (-t) u
    rw [hm,he,reflect_reflect]
  · rintro ⟨u,hu,rfl⟩
    exact ⟨mirror u,(mirror_boundary u).mpr hu,negative_model t u⟩

lemma negativeArc_proper (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3)
    (x : Icc (bounds t j).1 (bounds t j).2) :
    (reflect ∘ physicalArc t j) x ∈ model (-t) '' boxBoundary ↔
      x.val=(bounds t j).1 ∨ x.val=(bounds t j).2 := by
  exact (reflected_boundary t _).trans (physicalArc_proper t ht ht1 j x)

lemma negativeArc_endpoints (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (j : Fin 3)
    (x : Icc (bounds t j).1 (bounds t j).2) :
    (x.val=(bounds t j).1 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (leftEnd t j))) ∧
    (x.val=(bounds t j).2 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (rightEnd t j))) := by
  constructor
  · intro he
    change reflect (physicalArc t j x)=_
    rw [(physicalArc_endpoints t ht ht1 j x).1 he]
    exact (negative_model t (leftEnd t j)).symm
  · intro he
    change reflect (physicalArc t j x)=_
    rw [(physicalArc_endpoints t ht ht1 j x).2 he]
    exact (negative_model t (rightEnd t j)).symm

lemma negativeArcs_disjoint (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (i j : Fin 3) (hij : i≠j) : Disjoint
      (range (reflect ∘ physicalArc t i)) (range (reflect ∘ physicalArc t j)) := by
  rw [range_comp,range_comp]
  exact (Set.disjoint_image_iff reflect_embedding.injective).mpr (physicalArcs_disjoint t ht ht1 i j hij)

end
end ContactTopology.RetrogradeMovie

namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma connection_hasDerivAt (x : ℝ) : HasDerivAt connection ![1,0] x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id x
  · exact hasDerivAt_const x 0

lemma connection_characteristic (x : ℝ) :
    characteristic 0 (connection x)=(1-x^2) • deriv connection x := by
  rw [(connection_hasDerivAt x).deriv]
  ext i; fin_cases i <;> simp [connection,characteristic]

lemma connection_speed_positive (x : ℝ) (hx : x ∈ Ioo (-1:ℝ) 1) : 0 < 1-x^2 := by
  nlinarith [hx.1,hx.2]

def characteristicDerivative (u : Plane) : Plane →L[ℝ] Plane :=
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  ContinuousLinearMap.pi ![(-2*u 0) • e 0,(3*u 1) • e 0+(3*u 0) • e 1]

lemma characteristic_hasFDerivAt (t : ℝ) (u : Plane) :
    HasFDerivAt (characteristic t) (characteristicDerivative u) u := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun u : Plane => u i) (e i) u := (e i).hasFDerivAt
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! (hasFDerivAt_const (1:ℝ) u).sub ((h 0).pow 2) using 1 <;>
      ext v <;> simp [characteristic,characteristicDerivative,e] <;> ring
  · convert! (((h 0).mul (h 1)).const_mul 3).sub_const (2*t) using 1 <;>
      ext v <;> simp [characteristic,characteristicDerivative,e] <;> ring

lemma characteristic_trace (t : ℝ) (u : Plane) :
    fderiv ℝ (characteristic t) u ![1,0] 0+
      fderiv ℝ (characteristic t) u ![0,1] 1=u 0 := by
  rw [(characteristic_hasFDerivAt t u).fderiv]
  simp [characteristicDerivative]
  ring

lemma saddle_linearizations (v : Plane) :
    fderiv ℝ (characteristic 0) ![-1,0] v=![2*v 0,-3*v 1] ∧
      fderiv ℝ (characteristic 0) ![1,0] v= ![-2*v 0,3*v 1] := by
  constructor
  · rw [(characteristic_hasFDerivAt 0 ![-1,0]).fderiv]
    ext i; fin_cases i <;> simp [characteristicDerivative] <;> ring
  · rw [(characteristic_hasFDerivAt 0 ![1,0]).fderiv]
    ext i; fin_cases i <;> simp [characteristicDerivative] <;> ring

lemma opposite_saddle_signs :
    fderiv ℝ (characteristic 0) ![-1,0] ![1,0] 0+
      fderiv ℝ (characteristic 0) ![-1,0] ![0,1] 1= -1 ∧
    fderiv ℝ (characteristic 0) ![1,0] ![1,0] 0+
      fderiv ℝ (characteristic 0) ![1,0] ![0,1] 1=1 := by
  constructor <;> rw [characteristic_trace] <;> rfl

end
end ContactTopology.RetrogradeMovie

namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma flow_smooth : ContDiff ℝ ∞ (fun z : ℝ × Space => flow z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [flow] <;> fun_prop

lemma flow_zero (p : Space) : flow 0 p=p := by
  ext i; fin_cases i <;> simp [flow]

lemma flow_inverse (s : ℝ) (p : Space) : flow (-s) (flow s p)=p := by
  ext i; fin_cases i <;> simp [flow,Real.exp_neg,← mul_assoc]

lemma flow_add (s r : ℝ) (p : Space) : flow (s+r) p=flow s (flow r p) := by
  ext i; fin_cases i <;> simp [flow,Real.exp_add,mul_assoc]

def flowLinear (s : ℝ) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := flow s
      map_add' := by intro v w; ext i; fin_cases i <;> simp [flow,mul_add]
      map_smul' := by intro a v; ext i; fin_cases i <;> simp [flow] <;> ring }

lemma flow_fderiv (s : ℝ) (p v : Space) : fderiv ℝ (flow s) p v=flow s v :=
  congrArg (fun L : Space →L[ℝ] Space => L v) (flowLinear s).hasFDerivAt.fderiv

lemma flow_contact (s : ℝ) (p v : Space) :
    jetForm (flow s p) (fderiv ℝ (flow s) p v)=Real.exp s*jetForm p v := by
  rw [flow_fderiv]
  dsimp [flow,jetForm]
  ring

lemma flow_velocity (s : ℝ) (p : Space) :
    HasDerivAt (fun r => flow r p) (euler (flow s p)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_const s (p 0)
  · exact (Real.hasDerivAt_exp s).mul_const (p 1)
  · exact (Real.hasDerivAt_exp s).mul_const (p 2)

lemma flow_model (s t : ℝ) (u : Plane) :
    flow s (model t u)=model (Real.exp s*t) ![u 0,Real.exp s*u 1] := by
  ext i; fin_cases i <;> simp [flow,model] <;> ring

lemma flow_level (s : ℝ) (p : Space) : level (flow s p)=Real.exp s*level p := by
  dsimp [level,flow]
  ring

end
end ContactTopology.RetrogradeMovie

namespace ContactTopology.RetrogradeMovie
open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma model_embedding (t : ℝ) : IsEmbedding (model t) := by
  have hl : LeftInverse (fun p : Space => ![p 0,p 2+p 0*p 1]) (model t) := recover_model t
  apply hl.isEmbedding
  · apply continuous_pi; intro i; fin_cases i <;> dsimp <;> fun_prop
  · exact (model_smooth.comp (contDiff_const.prodMk contDiff_id)).continuous

theorem explicit_retrograde_event :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => model p.1 p.2) ∧
    (∀ t : ℝ, IsEmbedding (model t) ∧ ∀ u : Plane, Injective (fderiv ℝ (model t) u)) ∧
    (∀ t : ℝ, ∀ u v : Plane, jetForm (model t u) (fderiv ℝ (model t) u v)=
      (2*t-3*u 0*u 1)*v 0+(1-u 0^2)*v 1) ∧
    ContDiff ℝ ∞ euler ∧
    (∀ p v : Space, -(euler p 1)*v 0+jetForm p (fderiv ℝ euler p v)=jetForm p v) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => flow z.1 z.2) ∧
    (∀ p : Space, flow 0 p=p) ∧
    (∀ s r : ℝ, ∀ p : Space, flow (s+r) p=flow s (flow r p)) ∧
    (∀ s : ℝ, ∀ p : Space, flow (-s) (flow s p)=p) ∧
    (∀ s : ℝ, ∀ p v : Space,
      jetForm (flow s p) (fderiv ℝ (flow s) p v)=Real.exp s*jetForm p v) ∧
    (∀ s : ℝ, ∀ p : Space, HasDerivAt (fun r => flow r p) (euler (flow s p)) s) ∧
    (∀ t : ℝ, t≠0 → ∀ u v : Plane, euler (model t u)≠fderiv ℝ (model t) u v) ∧
    (∀ (Y : Space → Space) (O : Set Space), IsOpen O →
      (∀ x ∈ Icc (-1:ℝ) 1, model 0 ![x,0] ∈ O) → ContDiffOn ℝ ∞ Y O →
      (∀ p ∈ O, ∃ a : ℝ, ∀ v : Space,
        -(Y p 1)*v 0+jetForm p (fderiv ℝ Y p v)=a*jetForm p v) →
      ∃ x ∈ Ioo (-1:ℝ) 1, ∃ v : Plane,
        Y (model 0 ![x,0])=fderiv ℝ (model 0) ![x,0] v) ∧
    (∀ t : ℝ, ∀ u : Plane, characteristic t u=0 ↔
      u= ![-1,-2*t/3] ∨ u= ![1,2*t/3]) ∧
    (∀ v : Plane, fderiv ℝ (characteristic 0) ![-1,0] v=![2*v 0,-3*v 1] ∧
      fderiv ℝ (characteristic 0) ![1,0] v= ![-2*v 0,3*v 1]) ∧
    (∀ x : ℝ, HasDerivAt connection ![1,0] x ∧
      characteristic 0 (connection x)=(1-x^2) • deriv connection x) ∧
    (∀ x ∈ Ioo (-1:ℝ) 1, 0 < 1-x^2) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      (0 < inner t ∧ inner t < 1 ∧ 1 < outer t ∧ outer t < 2 ∧
        inner t^2+t*inner t=1 ∧ outer t^2-t*outer t=1) ∧
      physicalZero t=range (physicalArc t 0) ∪ range (physicalArc t 1) ∪ range (physicalArc t 2) ∧
      physicalZero (-t)=range (reflect ∘ physicalArc t 0) ∪
        range (reflect ∘ physicalArc t 1) ∪ range (reflect ∘ physicalArc t 2) ∧
      (∀ j : Fin 3, (bounds t j).1 < (bounds t j).2 ∧
        IsEmbedding (physicalArc t j) ∧ IsEmbedding (reflect ∘ physicalArc t j) ∧
        (∀ x ∈ interval t j,
          (ContDiffAt ℝ ∞ (model t ∘ graph t) x ∧ deriv (model t ∘ graph t) x≠0) ∧
          (ContDiffAt ℝ ∞ (reflect ∘ model t ∘ graph t) x ∧
            deriv (reflect ∘ model t ∘ graph t) x≠0)) ∧
        ∀ x : Icc (bounds t j).1 (bounds t j).2,
          (physicalArc t j x ∈ model t '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((reflect ∘ physicalArc t j) x ∈ model (-t) '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((x.val=(bounds t j).1 → physicalArc t j x=model t (leftEnd t j)) ∧
            (x.val=(bounds t j).2 → physicalArc t j x=model t (rightEnd t j))) ∧
          ((x.val=(bounds t j).1 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (leftEnd t j))) ∧
            (x.val=(bounds t j).2 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (rightEnd t j))))) ∧
      ∀ i j : Fin 3, i≠j →
        Disjoint (range (physicalArc t i)) (range (physicalArc t j)) ∧
        Disjoint (range (reflect ∘ physicalArc t i)) (range (reflect ∘ physicalArc t j)) := by
  refine ⟨model_smooth,fun t => ⟨model_embedding t,model_immersed t⟩,model_pullback,
    euler_smooth,euler_contact,flow_smooth,flow_zero,flow_add,flow_inverse,flow_contact,flow_velocity,
    euler_transverse,exceptional_slice_has_no_transverse_contact_field,
    characteristic_singularities,saddle_linearizations,
    fun x => ⟨connection_hasDerivAt x,connection_characteristic x⟩,connection_speed_positive,?_⟩
  intro t ht ht1
  refine ⟨roots t ht ht1,physical_dividing_set t ht ht1,physical_dividing_set_negative t ht ht1,?_,?_⟩
  · intro j
    refine ⟨bounds_order t ht ht1 j,physicalArc_embedding t ht ht1 j,negativeArc_embedding t ht ht1 j,?_,?_⟩
    · intro x hx
      exact ⟨physicalArc_smooth_regular t x ht ht1 j hx,negativeArc_smooth_regular t x ht ht1 j hx⟩
    · intro x
      exact ⟨physicalArc_proper t ht ht1 j x,negativeArc_proper t ht ht1 j x,
        physicalArc_endpoints t ht ht1 j x,negativeArc_endpoints t ht ht1 j x⟩
  · intro i j hij
    exact ⟨physicalArcs_disjoint t ht ht1 i j hij,negativeArcs_disjoint t ht ht1 i j hij⟩

end
end ContactTopology.RetrogradeMovie

open BirkhoffGlobalSection ContactTopology.TwoArcDisk ContactTopology.RetrogradeMovie Set Function Topology
open scoped ContDiff
theorem solution :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => model p.1 p.2) ∧
    (∀ t : ℝ, IsEmbedding (model t) ∧ ∀ u : Plane, Injective (fderiv ℝ (model t) u)) ∧
    (∀ t : ℝ, ∀ u v : Plane, jetForm (model t u) (fderiv ℝ (model t) u v)=
      (2*t-3*u 0*u 1)*v 0+(1-u 0^2)*v 1) ∧
    ContDiff ℝ ∞ euler ∧
    (∀ p v : Space, -(euler p 1)*v 0+jetForm p (fderiv ℝ euler p v)=jetForm p v) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => flow z.1 z.2) ∧
    (∀ p : Space, flow 0 p=p) ∧
    (∀ s r : ℝ, ∀ p : Space, flow (s+r) p=flow s (flow r p)) ∧
    (∀ s : ℝ, ∀ p : Space, flow (-s) (flow s p)=p) ∧
    (∀ s : ℝ, ∀ p v : Space,
      jetForm (flow s p) (fderiv ℝ (flow s) p v)=Real.exp s*jetForm p v) ∧
    (∀ s : ℝ, ∀ p : Space, HasDerivAt (fun r => flow r p) (euler (flow s p)) s) ∧
    (∀ t : ℝ, t≠0 → ∀ u v : Plane, euler (model t u)≠fderiv ℝ (model t) u v) ∧
    (∀ (Y : Space → Space) (O : Set Space), IsOpen O →
      (∀ x ∈ Icc (-1:ℝ) 1, model 0 ![x,0] ∈ O) → ContDiffOn ℝ ∞ Y O →
      (∀ p ∈ O, ∃ a : ℝ, ∀ v : Space,
        -(Y p 1)*v 0+jetForm p (fderiv ℝ Y p v)=a*jetForm p v) →
      ∃ x ∈ Ioo (-1:ℝ) 1, ∃ v : Plane,
        Y (model 0 ![x,0])=fderiv ℝ (model 0) ![x,0] v) ∧
    (∀ t : ℝ, ∀ u : Plane, characteristic t u=0 ↔
      u= ![-1,-2*t/3] ∨ u= ![1,2*t/3]) ∧
    (∀ v : Plane, fderiv ℝ (characteristic 0) ![-1,0] v=![2*v 0,-3*v 1] ∧
      fderiv ℝ (characteristic 0) ![1,0] v= ![-2*v 0,3*v 1]) ∧
    (∀ x : ℝ, HasDerivAt connection ![1,0] x ∧
      characteristic 0 (connection x)=(1-x^2) • deriv connection x) ∧
    (∀ x ∈ Ioo (-1:ℝ) 1, 0 < 1-x^2) ∧
    ∀ t : ℝ, 0 < t → t < 1 →
      (0 < inner t ∧ inner t < 1 ∧ 1 < outer t ∧ outer t < 2 ∧
        inner t^2+t*inner t=1 ∧ outer t^2-t*outer t=1) ∧
      physicalZero t=range (physicalArc t 0) ∪ range (physicalArc t 1) ∪ range (physicalArc t 2) ∧
      physicalZero (-t)=range (reflect ∘ physicalArc t 0) ∪
        range (reflect ∘ physicalArc t 1) ∪ range (reflect ∘ physicalArc t 2) ∧
      (∀ j : Fin 3, (bounds t j).1 < (bounds t j).2 ∧
        IsEmbedding (physicalArc t j) ∧ IsEmbedding (reflect ∘ physicalArc t j) ∧
        (∀ x ∈ interval t j,
          (ContDiffAt ℝ ∞ (model t ∘ graph t) x ∧ deriv (model t ∘ graph t) x≠0) ∧
          (ContDiffAt ℝ ∞ (reflect ∘ model t ∘ graph t) x ∧
            deriv (reflect ∘ model t ∘ graph t) x≠0)) ∧
        ∀ x : Icc (bounds t j).1 (bounds t j).2,
          (physicalArc t j x ∈ model t '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((reflect ∘ physicalArc t j) x ∈ model (-t) '' boxBoundary ↔
            x.val=(bounds t j).1 ∨ x.val=(bounds t j).2) ∧
          ((x.val=(bounds t j).1 → physicalArc t j x=model t (leftEnd t j)) ∧
            (x.val=(bounds t j).2 → physicalArc t j x=model t (rightEnd t j))) ∧
          ((x.val=(bounds t j).1 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (leftEnd t j))) ∧
            (x.val=(bounds t j).2 → (reflect ∘ physicalArc t j) x=model (-t) (mirror (rightEnd t j))))) ∧
      ∀ i j : Fin 3, i≠j →
        Disjoint (range (physicalArc t i)) (range (physicalArc t j)) ∧
        Disjoint (range (reflect ∘ physicalArc t i)) (range (reflect ∘ physicalArc t j)) := by
  exact ContactTopology.RetrogradeMovie.explicit_retrograde_event
