-- Prove2me | solution 1 for ContactTopology.explicit_two_arc_convex_disk_in_standard_contact_space
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T05:38:16.293116+00:00
-- url     : https://prove2.me/submissions/653209c9-40ca-422d-8446-0ecc97057178

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_ContactTopology_TwoArcJetDisk
import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Theorems.Thm_SmoothJetExtension_compact_first_jet_extension






namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

def coefficients (y : Space) : Space :=
  ![beta ![y 0,y 1] 0,beta ![y 0,y 1] 1,dividing ![y 0,y 1]]
def pairing (a v : Space) : ℝ := a 0*v 0+a 1*v 1+a 2*v 2
def surface (x : Plane) : Space := ![x 0,x 1,0]
def field (_ : Space) : Space := ![0,0,1]
def gradient (x : Plane) : Plane := ![2*x 0-x 0*radiusSq x,-2*x 1-x 1*radiusSq x]

lemma dividing_smooth : ContDiff ℝ ∞ dividing := by unfold dividing radiusSq; fun_prop
lemma beta_smooth : ContDiff ℝ ∞ beta := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [beta,dividing,radiusSq] <;> fun_prop
lemma coefficients_smooth : ContDiff ℝ ∞ coefficients := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coefficients,beta,dividing,radiusSq] <;> fun_prop

lemma dividing_derivative (x w : Plane) :
    fderiv ℝ dividing x w=gradient x 0*w 0+gradient x 1*w 1 := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun x : Plane => x i) (e i) x := (e i).hasFDerivAt
  have hR := ((h 0).pow 2).add ((h 1).pow 2)
  have hd := (((h 0).pow 2).sub ((h 1).pow 2)).sub
    (((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).add (hR.pow 2)).mul_const ((4:ℝ)⁻¹))
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L w) hd.fderiv
  change fderiv ℝ dividing x w=_ at he
  rw [he]
  simp [e,gradient,radiusSq]
  ring

lemma beta_derivative (x w : Plane) :
    fderiv ℝ beta x w =
      ![-2*w 1-w 1*radiusSq x-x 1*(2*x 0*w 0+2*x 1*w 1)-
          2*(gradient x 0*w 0+gradient x 1*w 1)*x 1-2*dividing x*w 1,
        -2*w 0+w 0*radiusSq x+x 0*(2*x 0*w 0+2*x 1*w 1)+
          2*(gradient x 0*w 0+gradient x 1*w 1)*x 0+2*dividing x*w 0] := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun x : Plane => x i) (e i) x := (e i).hasFDerivAt
  have hR := ((h 0).pow 2).add ((h 1).pow 2)
  have hf := dividing_smooth.differentiable (by simp) |>.differentiableAt.hasFDerivAt (x := x)
  have h0 := ((((h 1).const_mul (-2)).sub ((h 1).mul hR)).sub
    ((hf.const_mul 2).mul (h 1)))
  have h1 := ((((h 0).const_mul (-2)).add ((h 0).mul hR)).add
    ((hf.const_mul 2).mul (h 0)))
  change HasFDerivAt (fun q => beta q 0) _ x at h0
  change HasFDerivAt (fun q => beta q 1) _ x at h1
  have hd : HasFDerivAt beta (ContinuousLinearMap.pi
      ![fderiv ℝ (fun q => beta q 0) x,fderiv ℝ (fun q => beta q 1) x]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,e,dividing_derivative,radiusSq]
  all_goals ring

/-- Actual invariant-contact determinant, with no positivity certificate input. -/
lemma contact_determinant (x : Plane) :
    beta x 0*fderiv ℝ dividing x (Pi.single 1 1)-
      beta x 1*fderiv ℝ dividing x (Pi.single 0 1)+
      dividing x*(fderiv ℝ beta x (Pi.single 0 1) 1-
        fderiv ℝ beta x (Pi.single 1 1) 0)=3*radiusSq x+4*dividing x^2 := by
  simp only [dividing_derivative,beta_derivative]
  dsimp [beta,gradient,dividing,radiusSq]
  norm_num
  ring

lemma contact_positive (x : Plane) :
    0 < beta x 0*fderiv ℝ dividing x (Pi.single 1 1)-
      beta x 1*fderiv ℝ dividing x (Pi.single 0 1)+
      dividing x*(fderiv ℝ beta x (Pi.single 0 1) 1-
        fderiv ℝ beta x (Pi.single 1 1) 0) := by
  rw [contact_determinant]
  by_cases h : x=0
  · subst x
    norm_num [dividing,radiusSq]
  · have hr : 0 < radiusSq x := by
      by_contra hn
      have he : x=0 := by
        ext i
        fin_cases i <;> dsimp [radiusSq] at hn ⊢ <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]
      exact h he
    nlinarith [sq_nonneg (dividing x)]

lemma surface_derivative (x w : Plane) : fderiv ℝ surface x w=![w 0,w 1,0] := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hs : HasFDerivAt surface (ContinuousLinearMap.pi ![e 0,e 1,0]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (e 0).hasFDerivAt
    · exact (e 1).hasFDerivAt
    · exact hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) x
  rw [hs.fderiv]
  ext i
  fin_cases i <;> simp [e]

lemma boundary_legendrian (x : Plane) (hx : x ∈ unitCircle) :
    pairing (coefficients (surface x)) (fderiv ℝ surface x (circleTangent x))=0 := by
  rw [surface_derivative]
  change radiusSq x=1 at hx
  have he : pairing (coefficients (surface x)) ![-x 1,x 0,0]=
      -2*(radiusSq x-1)*(radiusSq x^2/4-radiusSq x/4-x 0^2+x 1^2) := by
    dsimp [pairing,coefficients,surface,beta,dividing,radiusSq]
    ring
  change pairing (coefficients (surface x)) ![-x 1,x 0,0]=0
  rw [he,hx]
  ring

lemma field_dividing (x : Plane) :
    pairing (coefficients (surface x)) (field (surface x))=0 ↔ dividing x=0 := by
  simp [pairing,coefficients,surface,field,dividing,radiusSq]

lemma field_transverse (x w : Plane) : field (surface x) ≠ fderiv ℝ surface x w := by
  rw [surface_derivative]
  intro he
  have hp := congrArg (fun y : Space => y 2) he
  change (1:ℝ)=0 at hp
  norm_num at hp

end
end ContactTopology.TwoArcDisk


namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma arc_radicands_positive (t : ℝ) (ht : t ∈ Icc (-1/2:ℝ) (1/2)) :
    0 < 3-8*t^2 ∧ 0 < arcRadicand t := by
  have ht2 : t^2≤1/4 := by nlinarith [ht.1,ht.2,mul_nonneg (show 0≤t+1/2 by linarith [ht.1]) (show 0≤1/2-t by linarith [ht.2])]
  have hp : 0 < 3-8*t^2 := by nlinarith
  have hs := Real.sq_sqrt hp.le
  have hn := Real.sqrt_nonneg (3-8*t^2)
  have hlt : Real.sqrt (3-8*t^2)<7/4 := by nlinarith [sq_nonneg t]
  refine ⟨hp,?_⟩
  dsimp [arcRadicand]
  linarith

lemma arc_in_disk_and_dividing (σ t : ℝ) (hσ : σ^2=1)
    (ht : t ∈ Icc (-1/2:ℝ) (1/2)) : radiusSq (arc σ t)≤1 ∧ dividing (arc σ t)=0 := by
  have hp := arc_radicands_positive t ht
  have ht2 : t^2≤1/4 := by nlinarith [ht.1,ht.2,mul_nonneg (show 0≤t+1/2 by linarith [ht.1]) (show 0≤1/2-t by linarith [ht.2])]
  have hw := Real.sq_sqrt hp.1.le
  have hw0 := Real.sqrt_nonneg (3-8*t^2)
  have hw1 : 1≤Real.sqrt (3-8*t^2) := by nlinarith
  have hx := Real.sq_sqrt hp.2.le
  have hx2 : (arc σ t) 0^2=arcRadicand t := by
    change (σ*Real.sqrt (arcRadicand t))^2=arcRadicand t
    rw [mul_pow,hσ,one_mul,hx]
  have hr : radiusSq (arc σ t)=2-Real.sqrt (3-8*t^2) := by
    unfold radiusSq
    rw [hx2]
    change arcRadicand t+t^2=_
    unfold arcRadicand
    ring
  refine ⟨by rw [hr]; linarith,?_⟩
  unfold dividing
  rw [hx2,hr]
  change arcRadicand t-t^2-(1+(2-Real.sqrt (3-8*t^2))^2)/4=0
  dsimp [arcRadicand]
  nlinarith

lemma dividing_first_ne_zero (x : Plane) (hf : dividing x=0) : x 0≠0 := by
  intro hx
  unfold dividing at hf
  rw [hx] at hf
  nlinarith [sq_nonneg (x 1),sq_nonneg (radiusSq x)]

lemma dividing_regular_on_disk (x : Plane) (hx : radiusSq x≤1) (hf : dividing x=0) :
    fderiv ℝ dividing x (Pi.single 0 1)≠0 := by
  rw [dividing_derivative]
  simp only [Pi.single_eq_same,Pi.single_eq_of_ne (by decide : (1:Fin 2)≠0),mul_one,mul_zero,add_zero]
  have hg : gradient x 0=x 0*(2-radiusSq x) := by simp [gradient]; ring
  rw [hg]
  exact mul_ne_zero (dividing_first_ne_zero x hf) (by linarith)

lemma dividing_is_two_arcs (x : Plane) (hx : radiusSq x≤1) : dividing x=0 ↔
    ∃ t ∈ Icc (-1/2:ℝ) (1/2), x=arc 1 t ∨ x=arc (-1) t := by
  constructor
  · intro hf
    have hR : 0≤radiusSq x := by unfold radiusSq; positivity
    have he : 4*(x 0^2-x 1^2)=1+radiusSq x^2 := by
      unfold dividing at hf
      linarith
    have ht2 : x 1^2≤1/4 := by
      have hq := sq_nonneg (radiusSq x-1)
      have hsum : x 0^2+x 1^2=radiusSq x := rfl
      nlinarith
    have ht : x 1 ∈ Icc (-1/2:ℝ) (1/2) := by constructor <;> nlinarith [sq_nonneg (x 1+1/2),sq_nonneg (x 1-1/2)]
    have hw : Real.sqrt (3-8*x 1^2)=2-radiusSq x := by
      have heq : 3-8*x 1^2=(2-radiusSq x)^2 := by
        have hsum : x 0^2+x 1^2=radiusSq x := rfl
        nlinarith
      rw [heq,Real.sqrt_sq (by linarith)]
    have hg : arcRadicand (x 1)=x 0^2 := by
      unfold arcRadicand
      rw [hw]
      unfold radiusSq
      ring
    have hs : Real.sqrt (arcRadicand (x 1))=|x 0| := by rw [hg,Real.sqrt_sq_eq_abs]
    refine ⟨x 1,ht,?_⟩
    by_cases hu : 0≤x 0
    · left
      ext i
      fin_cases i <;> simp [arc,hs,abs_of_nonneg hu]
    · right
      ext i
      fin_cases i <;> simp [arc,hs,abs_of_neg (lt_of_not_ge hu)]
  · rintro ⟨t,ht,rfl|rfl⟩
    · exact (arc_in_disk_and_dividing 1 t (by norm_num) ht).2
    · exact (arc_in_disk_and_dividing (-1) t (by norm_num) ht).2

lemma arc_smooth (σ t : ℝ) (ht : t ∈ Icc (-1/2:ℝ) (1/2)) : ContDiffAt ℝ ∞ (arc σ) t := by
  have hp := arc_radicands_positive t ht
  have hi : ContDiff ℝ ∞ (fun t : ℝ => 3-8*t^2) := by fun_prop
  have hw : ContDiffAt ℝ ∞ (fun t : ℝ => Real.sqrt (3-8*t^2)) t :=
    (Real.contDiffAt_sqrt hp.1.ne').comp t hi.contDiffAt
  have hg : ContDiffAt ℝ ∞ arcRadicand t :=
    ((contDiffAt_const.sub (contDiffAt_id.pow 2)).sub hw)
  have ha : ContDiffAt ℝ ∞ (fun t : ℝ => Real.sqrt (arcRadicand t)) t :=
    (Real.contDiffAt_sqrt hp.2.ne').comp t hg
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_const.mul ha
  · exact contDiffAt_id

lemma arc_regular (σ t : ℝ) (ht : t ∈ Icc (-1/2:ℝ) (1/2)) :
    deriv (arc σ) t≠0 := by
  intro he
  have hd := (arc_smooth σ t ht).differentiableAt (by simp) |>.hasDerivAt
  have hc := ((ContinuousLinearMap.proj (R := ℝ) (i := (1:Fin 2))).hasFDerivAt.comp_hasDerivAt t hd).deriv
  change deriv (fun t : ℝ => t) t=(deriv (arc σ) t) 1 at hc
  have hid : deriv (fun t : ℝ => t) t=1 := (hasDerivAt_id t).deriv
  rw [hid,he] at hc
  norm_num at hc

lemma arc_embedding (σ : ℝ) : IsEmbedding (fun t : Icc (-1/2:ℝ) (1/2) => arc σ t.val) := by
  have hc : Continuous (fun t : Icc (-1/2:ℝ) (1/2) => arc σ t.val) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact ((arc_smooth σ t.val t.property).continuousAt.comp continuous_subtype_val.continuousAt)
  apply hc.isClosedEmbedding ?_ |>.isEmbedding
  intro t s he
  apply Subtype.ext
  exact congrArg (fun x : Plane => x 1) he

lemma arcs_disjoint : Disjoint
    (range (fun t : Icc (-1/2:ℝ) (1/2) => arc 1 t.val))
    (range (fun t : Icc (-1/2:ℝ) (1/2) => arc (-1) t.val)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨t,rfl⟩ ⟨s,he⟩
  have ht := Real.sqrt_pos.mpr (arc_radicands_positive t.val t.property).2
  have hs := Real.sqrt_pos.mpr (arc_radicands_positive s.val s.property).2
  have hp := congrArg (fun x : Plane => x 0) he
  change -1*Real.sqrt (arcRadicand s.val)=1*Real.sqrt (arcRadicand t.val) at hp
  nlinarith

lemma dividing_boundary_squares (x : Plane) (hx : radiusSq x=1) :
    dividing x=0 ↔ x 0^2=3/4 ∧ x 1^2=1/4 := by
  have hs : x 0^2+x 1^2=1 := hx
  unfold dividing
  rw [hx]
  constructor
  · intro hf
    constructor <;> nlinarith
  · rintro ⟨hu,hv⟩
    rw [hu,hv]
    norm_num

lemma arc_meets_boundary_only_at_endpoints (σ t : ℝ) (hσ : σ^2=1)
    (ht : t ∈ Icc (-1/2:ℝ) (1/2)) :
    radiusSq (arc σ t)=1 ↔ t= -1/2 ∨ t=1/2 := by
  have hg := arc_in_disk_and_dividing σ t hσ ht
  constructor
  · intro hr
    have hs := ((dividing_boundary_squares _ hr).mp hg.2).2
    change t^2=1/4 at hs
    have he : (t+1/2)*(t-1/2)=0 := by nlinarith
    rcases mul_eq_zero.mp he with he|he
    · left; linarith
    · right; linarith
  · intro he
    have ht2 : t^2=1/4 := by rcases he with rfl|rfl <;> norm_num
    have hf : 4*((arc σ t) 0^2-t^2)=1+radiusSq (arc σ t)^2 := by
      have hf := hg.2
      unfold dividing at hf
      change (arc σ t) 0^2-t^2-(1+radiusSq (arc σ t)^2)/4=0 at hf
      linarith
    have hsum : (arc σ t) 0^2+t^2=radiusSq (arc σ t) := rfl
    have hprod : (radiusSq (arc σ t)-1)*(radiusSq (arc σ t)-3)=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with hh|hh <;> linarith [hg.1]

lemma coefficients_field_invariant (y : Space) (t : ℝ) :
    coefficients (y+t • field y)=coefficients y := by
  ext i
  fin_cases i <;> simp [coefficients,field,beta,dividing,radiusSq]

lemma field_strict_contact (y v : Space) :
    pairing (fderiv ℝ coefficients y (field y)) v+
      pairing (coefficients y) (fderiv ℝ field y v)=0 := by
  have hline : HasDerivAt (fun t : ℝ => y+t • field y) (field y) 0 := by
    convert! ((hasDerivAt_const (0:ℝ) y).add
      ((hasDerivAt_id (0:ℝ)).smul_const (field y))) using 1 <;> simp
  have hc : HasDerivAt (fun t : ℝ => coefficients (y+t • field y))
      (fderiv ℝ coefficients y (field y)) 0 := by
    have hs : HasFDerivAt coefficients (fderiv ℝ coefficients y) (y+(0:ℝ) • field y) := by
      simpa only [zero_smul,add_zero] using
        ((coefficients_smooth.differentiable (by simp)).differentiableAt (x := y)).hasFDerivAt
    exact hs.comp_hasDerivAt 0 hline
  have he : (fun t : ℝ => coefficients (y+t • field y))=(fun _ : ℝ => coefficients y) :=
    funext (coefficients_field_invariant y)
  rw [he] at hc
  have hz : fderiv ℝ coefficients y (field y)=0 := hc.unique (hasDerivAt_const (0:ℝ) (coefficients y))
  have hf : fderiv ℝ field y=0 := by
    exact (hasFDerivAt_const (𝕜 := ℝ) (![0,0,1] : Space) y).fderiv
  rw [hz,hf]
  simp [pairing]

lemma surface_embedding : IsEmbedding surface := by
  let recover : Space → Plane := fun y => ![y 0,y 1]
  have hl : LeftInverse recover surface := by
    intro x
    ext i
    fin_cases i <;> rfl
  exact hl.isEmbedding (by change Continuous (fun y : Space => ![y 0,y 1]); fun_prop)
    (by change Continuous (fun x : Plane => ![x 0,x 1,0]); fun_prop)

lemma surface_immersion (x : Plane) : Injective (fderiv ℝ surface x) := by
  intro v w he
  have hh : (![v 0,v 1,0] : Space)=![w 0,w 1,0] := by
    simpa only [surface_derivative] using he
  ext i
  fin_cases i
  · exact congrArg (fun y : Space => y 0) hh
  · exact congrArg (fun y : Space => y 1) hh

end
end ContactTopology.TwoArcDisk

namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma coefficients_derivative (y w : Space) : fderiv ℝ coefficients y w=
    ![fderiv ℝ beta ![y 0,y 1] ![w 0,w 1] 0,
      fderiv ℝ beta ![y 0,y 1] ![w 0,w 1] 1,
      fderiv ℝ dividing ![y 0,y 1] ![w 0,w 1]] := by
  let e (i : Fin 3) : Space →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let B : Space →L[ℝ] Plane := ContinuousLinearMap.pi ![e 0,e 1]
  have hb : HasFDerivAt (fun y : Space => (![y 0,y 1] : Plane)) B y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (e 0).hasFDerivAt
    · exact (e 1).hasFDerivAt
  have hβ := ((beta_smooth.differentiable (by simp)).differentiableAt (x := (![y 0,y 1] : Plane))).hasFDerivAt.comp y hb
  have hf := ((dividing_smooth.differentiable (by simp)).differentiableAt (x := (![y 0,y 1] : Plane))).hasFDerivAt.comp y hb
  have h0 := (ContinuousLinearMap.proj (R := ℝ) (i := (0:Fin 2))).hasFDerivAt.comp y hβ
  have h1 := (ContinuousLinearMap.proj (R := ℝ) (i := (1:Fin 2))).hasFDerivAt.comp y hβ
  change HasFDerivAt (fun y => coefficients y 0) _ y at h0
  change HasFDerivAt (fun y => coefficients y 1) _ y at h1
  change HasFDerivAt (fun y => coefficients y 2) _ y at hf
  have hd : HasFDerivAt coefficients (ContinuousLinearMap.pi
      ![fderiv ℝ (fun y => coefficients y 0) y,
        fderiv ℝ (fun y => coefficients y 1) y,
        fderiv ℝ (fun y => coefficients y 2) y]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
    · exact hf.differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  have hBw : B w=![w 0,w 1] := by ext i; fin_cases i <;> simp [B,e]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,hf.fderiv,hBw]

/-- The actual three-dimensional coefficient formula for α∧dα. -/
lemma contact_volume (y : Space) :
    coefficients y 0*(fderiv ℝ coefficients y (Pi.single 1 1) 2-
        fderiv ℝ coefficients y (Pi.single 2 1) 1)+
      coefficients y 1*(fderiv ℝ coefficients y (Pi.single 2 1) 0-
        fderiv ℝ coefficients y (Pi.single 0 1) 2)+
      coefficients y 2*(fderiv ℝ coefficients y (Pi.single 0 1) 1-
        fderiv ℝ coefficients y (Pi.single 1 1) 0)=
      3*radiusSq ![y 0,y 1]+4*dividing ![y 0,y 1] ^2 := by
  rw [← contact_determinant ![y 0,y 1]]
  simp [coefficients_derivative,coefficients,dividing_derivative,beta_derivative,
    beta,gradient,dividing,radiusSq]
  ring

lemma contact_volume_positive (y : Space) :
    0 < coefficients y 0*(fderiv ℝ coefficients y (Pi.single 1 1) 2-
        fderiv ℝ coefficients y (Pi.single 2 1) 1)+
      coefficients y 1*(fderiv ℝ coefficients y (Pi.single 2 1) 0-
        fderiv ℝ coefficients y (Pi.single 0 1) 2)+
      coefficients y 2*(fderiv ℝ coefficients y (Pi.single 0 1) 1-
        fderiv ℝ coefficients y (Pi.single 1 1) 0) := by
  rw [contact_volume,← contact_determinant]
  exact contact_positive _

end
end ContactTopology.TwoArcDisk


namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma jetHeight_smooth : ContDiff ℝ ∞ jetHeight := by unfold jetHeight; fun_prop
lemma jetMomentum_smooth : ContDiff ℝ ∞ jetMomentum := by unfold jetMomentum; fun_prop
lemma jetDisk_smooth : ContDiff ℝ ∞ jetDisk := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ (0:Fin 2)
  · exact jetMomentum_smooth
  · exact jetHeight_smooth

lemma jetHeight_derivative (x w : Plane) : fderiv ℝ jetHeight x w=
    (jetMomentum x+beta x 0)*w 0+beta x 1*w 1 := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun x : Plane => x i) (e i) x := (e i).hasFDerivAt
  have ha := ((((((h 0).pow 4).const_mul 15).add
    ((((h 0).pow 2).mul ((h 1).pow 2)).const_mul 10)).sub
    (((h 0).pow 2).const_mul 90)).add (((h 1).pow 4).const_mul 3)).add
    (((h 1).pow 2).const_mul 10)
  have ha' := ha.add (hasFDerivAt_const (𝕜 := ℝ) (75:ℝ) x)
  have hd := ((((h 0).neg).mul (h 1)).mul ha').mul_const ((30:ℝ)⁻¹)
  have hd' := hd.congr_of_eventuallyEq (f₁ := jetHeight)
    (Filter.Eventually.of_forall (fun y => by dsimp [jetHeight]; ring))
  rw [hd'.fderiv]
  simp [e,jetMomentum,beta,dividing,radiusSq]
  ring

lemma jetMomentum_derivative (x w : Plane) : fderiv ℝ jetMomentum x w=
    momentumU x*w 0+momentumV x*w 1 := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h (i : Fin 2) : HasFDerivAt (fun x : Plane => x i) (e i) x := (e i).hasFDerivAt
  have ha := ((((((h 0).pow 4).const_mul 45).add
    ((((h 0).pow 2).mul ((h 1).pow 2)).const_mul 30)).sub
    (((h 0).pow 2).const_mul 180)).add (((h 1).pow 4).const_mul 9)).add
    (((h 1).pow 2).const_mul 20)
  have ha' := ha.add (hasFDerivAt_const (𝕜 := ℝ) (15:ℝ) x)
  have hd := (((h 1).neg).mul ha').mul_const ((15:ℝ)⁻¹)
  have hd' := hd.congr_of_eventuallyEq (f₁ := jetMomentum)
    (Filter.Eventually.of_forall (fun y => by dsimp [jetMomentum]; ring))
  rw [hd'.fderiv]
  simp [e,momentumU,momentumV,radiusSq]
  ring

lemma jetDisk_derivative (x w : Plane) : fderiv ℝ jetDisk x w=
    ![w 0,momentumU x*w 0+momentumV x*w 1,
      (jetMomentum x+beta x 0)*w 0+beta x 1*w 1] := by
  let e (i : Fin 2) : Plane →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hd : HasFDerivAt jetDisk (ContinuousLinearMap.pi
      ![e 0,fderiv ℝ jetMomentum x,fderiv ℝ jetHeight x]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (e 0).hasFDerivAt
    · exact (jetMomentum_smooth.differentiable (by simp) x).hasFDerivAt
    · exact (jetHeight_smooth.differentiable (by simp) x).hasFDerivAt
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [e,jetHeight_derivative,jetMomentum_derivative]

lemma jetDisk_contact (x w : Plane) : jetForm (jetDisk x) (fderiv ℝ jetDisk x w)=
    beta x 0*w 0+beta x 1*w 1 := by
  rw [jetDisk_derivative]
  simp [jetDisk,jetForm]
  ring

lemma beta_second_factor (x : Plane) : beta x 1=
    -x 0*((1-radiusSq x)*(5-radiusSq x)+8*x 1^2)/2 := by
  dsimp [beta,dividing,radiusSq]
  ring

lemma vertical_nonzero (x : Plane) (hx : radiusSq x≤1) : momentumV x≠0 ∨ beta x 1≠0 := by
  by_cases hu : x 0=0
  · left
    intro he
    dsimp [momentumV,radiusSq] at he
    rw [hu] at he
    nlinarith [sq_nonneg (x 1),sq_nonneg (x 1^2)]
  · by_cases hb : beta x 1=0
    · left
      have hK : (1-radiusSq x)*(5-radiusSq x)+8*x 1^2=0 := by
        rw [beta_second_factor] at hb
        rcases (div_eq_zero_iff).mp hb with he|he
        · exact (mul_eq_zero.mp he).resolve_left (neg_ne_zero.mpr hu)
        · norm_num at he
      have hp : 0≤(1-radiusSq x)*(5-radiusSq x) := mul_nonneg (by linarith) (by linarith)
      have hv : x 1=0 := by nlinarith [sq_nonneg (x 1)]
      have hR : radiusSq x=1 := by
        rw [hv] at hK
        nlinarith
      have hu2 : x 0^2=1 := by simpa [radiusSq,hv] using hR
      intro he
      dsimp [momentumV] at he
      rw [hR,hv,hu2] at he
      norm_num at he
    · exact Or.inr hb

lemma jetDisk_immersion (x : Plane) (hx : radiusSq x≤1) :
    Injective (fderiv ℝ jetDisk x) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  rw [jetDisk_derivative] at hw
  have hu : w 0=0 := congrArg (fun p : Space => p 0) hw
  have hp : momentumV x*w 1=0 := by
    have hh := congrArg (fun p : Space => p 1) hw
    simpa [hu] using hh
  have hz : beta x 1*w 1=0 := by
    have hh := congrArg (fun p : Space => p 2) hw
    simpa [hu] using hh
  have hv : w 1=0 := by
    rcases vertical_nonzero x hx with h|h
    · exact (mul_eq_zero.mp hp).resolve_left h
    · exact (mul_eq_zero.mp hz).resolve_left h
  ext i
  fin_cases i <;> simp [hu,hv]

lemma slice_interior_disk (a v w t : ℝ) (hv : a^2+v^2≤1) (hw : a^2+w^2≤1)
    (ht : t ∈ Ioo v w) : a^2+t^2<1 := by
  by_cases h : 0≤t
  · have hp : 0 < (w-t)*(w+t) := mul_pos (by linarith [ht.2]) (by linarith [ht.2])
    nlinarith
  · have hp : 0 < (t-v)*(-v-t) := mul_pos (by linarith [ht.1]) (by linarith [ht.1])
    nlinarith

lemma height_slice_derivative (a t : ℝ) (ha : a≠0) :
    HasDerivAt (fun t : ℝ => jetHeight ![a,t]/a)
      (-((1-(a^2+t^2))*(5-(a^2+t^2))+8*t^2)/2) t := by
  have hc : HasDerivAt (fun t : ℝ => (![a,t] : Plane)) (![0,1] : Plane) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const t a
    · exact hasDerivAt_id t
  have hd := ((jetHeight_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hc).div_const a
  apply hd.congr_deriv
  rw [jetHeight_derivative]
  simp [beta_second_factor,radiusSq]
  field_simp [ha]
  ring

lemma height_slice_strict (a v w : ℝ) (ha : a≠0) (hv : a^2+v^2≤1)
    (hw : a^2+w^2≤1) (hvw : v<w) : jetHeight ![a,w]/a<jetHeight ![a,v]/a := by
  have hm : StrictAntiOn (fun t : ℝ => jetHeight ![a,t]/a) (Icc v w) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (by unfold jetHeight; fun_prop)
    intro t ht
    rw [interior_Icc] at ht
    rw [(height_slice_derivative a t ha).deriv]
    have hi := slice_interior_disk a v w t hv hw ht
    have hp : 0 < (1-(a^2+t^2))*(5-(a^2+t^2)) := mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg t]
  exact hm ⟨le_rfl,hvw.le⟩ ⟨hvw.le,le_rfl⟩ hvw

lemma momentum_zero_slice_strict : StrictAnti (fun t : ℝ => jetMomentum ![0,t]) := by
  apply strictAnti_of_deriv_neg
  intro t
  have hc : HasDerivAt (fun t : ℝ => (![0,t] : Plane)) (![0,1] : Plane) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_const t 0
    · exact hasDerivAt_id t
  have hd := (jetMomentum_smooth.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t hc
  change HasDerivAt (fun t : ℝ => jetMomentum ![0,t]) _ t at hd
  rw [hd.deriv,jetMomentum_derivative]
  simp [momentumV,radiusSq]
  nlinarith [sq_nonneg t,sq_nonneg (t^2)]

lemma jetDisk_injective : InjOn jetDisk {x | radiusSq x≤1} := by
  intro x hx y hy he
  change radiusSq x≤1 at hx
  change radiusSq y≤1 at hy
  have hu : x 0=y 0 := congrArg (fun p : Space => p 0) he
  have hz : jetHeight x=jetHeight y := congrArg (fun p : Space => p 2) he
  have hp : jetMomentum x=jetMomentum y := congrArg (fun p : Space => p 1) he
  have hxform : (![x 0,x 1] : Plane)=x := by ext i; fin_cases i <;> rfl
  have hyform : (![x 0,y 1] : Plane)=y := by ext i; fin_cases i; exact hu; rfl
  have hv : x 1=y 1 := by
    by_cases ha : x 0=0
    · have hxx : (![0,x 1] : Plane)=x := by rw [← ha]; exact hxform
      have hyy : (![0,y 1] : Plane)=y := by rw [← ha]; exact hyform
      apply momentum_zero_slice_strict.injective
      change jetMomentum ![0,x 1]=jetMomentum ![0,y 1]
      rw [hxx,hyy]
      exact hp
    · have hxd : x 0^2+x 1^2≤1 := hx
      have hyd : x 0^2+y 1^2≤1 := by simpa only [radiusSq,← hu] using hy
      have hEq : jetHeight ![x 0,x 1]/x 0=jetHeight ![x 0,y 1]/x 0 := by rw [hxform,hyform,hz]
      rcases lt_trichotomy (x 1) (y 1) with h|h|h
      · exact False.elim ((ne_of_lt (height_slice_strict _ _ _ ha hxd hyd h)) hEq.symm)
      · exact h
      · exact False.elim ((ne_of_lt (height_slice_strict _ _ _ ha hyd hxd h)) hEq)
  ext i
  fin_cases i
  · exact hu
  · exact hv

lemma disk_compact : IsCompact {x : Plane | radiusSq x≤1} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by unfold radiusSq; fun_prop) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 1)).subset
    intro x hx
    change x 0^2+x 1^2≤1 at hx
    rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_one_iff_abs_le_one _).mp
    fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

lemma jetDisk_embedding : IsEmbedding (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) := by
  letI : CompactSpace {x : Plane // radiusSq x≤1} := isCompact_iff_compactSpace.mp disk_compact
  have hc : Continuous (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) :=
    jetDisk_smooth.continuous.comp continuous_subtype_val
  have hi : Injective (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) :=
    fun x y he => Subtype.ext (jetDisk_injective x.property y.property he)
  exact hc.isClosedEmbedding hi |>.isEmbedding

lemma jetDisk_boundary_legendrian (x : Plane) (hx : x ∈ unitCircle) :
    jetForm (jetDisk x) (fderiv ℝ jetDisk x (circleTangent x))=0 := by
  rw [jetDisk_contact]
  have h := boundary_legendrian x hx
  rw [surface_derivative] at h
  simpa [pairing,coefficients,surface,beta,dividing,radiusSq,circleTangent] using h

end
end ContactTopology.TwoArcDisk


namespace ContactTopology.TwoArcDisk
open Set Function Filter Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
lemma smooth_local_inverse_on_open {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (F : E → V) (hF : ContDiff ℝ ∞ F)
    (U : Set E) (hU : IsOpen U) (hinj : ∀ p ∈ U, Injective (fderiv ℝ F p))
    (p : E) (hp : p ∈ U) (hdim : Module.finrank ℝ E = Module.finrank ℝ V) :
    ∃ R : V → E, ∃ W : Set V, IsOpen W ∧ F p ∈ W ∧ ContDiffOn ℝ ∞ R W ∧
      R (F p) = p ∧ (∀ᶠ x in 𝓝 p, R (F x) = x) ∧
      ∀ y ∈ W, F (R y) = y ∧ R y ∈ U := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let A : E ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj p hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hinj p hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] V) p := (hF.differentiable (by simp) p).hasFDerivAt
  let e := hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp)
  have he : (e : E → V) = F := hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp)
  have hpe : p ∈ e.source := hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hFp : F p ∈ e.target := hF.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  have hbase : e.symm (F p) = p := by
    have hh := e.left_inv hpe
    rwa [he] at hh
  let W := e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W := e.isOpen_inter_preimage_symm hU
  refine ⟨e.symm,W,hW,⟨hFp,?_⟩,?_,hbase,?_,?_⟩
  · change e.symm (F p) ∈ U
    rwa [hbase]
  · intro y hy
    let B : E ≃L[ℝ] V := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
      ⟨hinj _ hy.2,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (hinj _ hy.2)⟩).toContinuousLinearEquiv
    have hdf : HasFDerivAt (e : E → V) (B : E →L[ℝ] V) (e.symm y) := by
      rw [he]
      exact (hF.differentiable (by simp) _).hasFDerivAt
    have hfe : ContDiffAt ℝ ∞ (e : E → V) (e.symm y) := by rw [he]; exact hF.contDiffAt
    exact (e.contDiffAt_symm hy.1 hdf hfe).contDiffWithinAt
  · filter_upwards [e.open_source.mem_nhds hpe] with x hx
    have hh := e.left_inv hx
    rwa [he] at hh
  · intro y hy
    refine ⟨?_,hy.2⟩
    have hh := e.right_inv hy.1
    rwa [he] at hh

lemma compact_injective_neighborhood {X Y : Type*} [MetricSpace X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) (A : Set X) (hA : IsCompact A) (hi : InjOn f A)
    (hloc : ∀ p ∈ A, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧ InjOn f U) :
    ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ InjOn f U := by
  let good : Set (X × X) := {p | f p.1=f p.2 → p.1=p.2}
  have hsub : A ×ˢ A ⊆ interior good := by
    rintro ⟨p,q⟩ ⟨hp,hq⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases he : p=q
    · subst q
      obtain ⟨U,hU,hpU,hUi⟩ := hloc p hp
      apply mem_of_superset ((hU.prod hU).mem_nhds (show (p,p) ∈ U ×ˢ U from ⟨hpU,hpU⟩))
      intro z hz
      exact hUi hz.1 hz.2
    · have hV : IsOpen {z : X × X | f z.1 ≠ f z.2} := isOpen_ne_fun (hf.comp continuous_fst) (hf.comp continuous_snd)
      apply mem_of_superset (hV.mem_nhds (show f p ≠ f q from fun h => he (hi hp hq h)))
      intro z hz h
      exact False.elim (hz h)
  obtain ⟨δ,hδ,hδsub⟩ := (hA.prod hA).exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨Metric.thickening (δ/2) A,Metric.isOpen_thickening,Metric.self_subset_thickening (by linarith) A,?_⟩
  intro p hp q hq he
  obtain ⟨a,ha,hpa⟩ := Metric.mem_thickening_iff.mp hp
  obtain ⟨b,hb,hqb⟩ := Metric.mem_thickening_iff.mp hq
  have hd : dist (p,q) (a,b) < δ := by
    rw [Prod.dist_eq]
    exact max_lt (by linarith) (by linarith)
  have hm : (p,q) ∈ Metric.cthickening δ (A ×ˢ A) :=
    Metric.thickening_subset_cthickening _ _ (Metric.mem_thickening_iff.mpr ⟨(a,b),⟨ha,hb⟩,hd⟩)
  exact (interior_subset (hδsub hm)) he

lemma smooth_inverse_on_injective_open {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (f : E → V) (hf : ContDiff ℝ ∞ f) (U : Set E) (hU : IsOpen U) (hi : InjOn f U)
    (hD : ∀ p ∈ U, Injective (fderiv ℝ f p)) (hdim : Module.finrank ℝ E=Module.finrank ℝ V) :
    ∃ R : V → E, ∃ O : Set V, IsOpen O ∧ O=f '' U ∧ ContDiffOn ℝ ∞ R O ∧
      (∀ y ∈ O, f (R y)=y ∧ R y ∈ U) ∧ (∀ p ∈ U, R (f p)=p) := by
  classical
  let R : V → E := fun y => if h : y ∈ f '' U then Classical.choose h else 0
  have hR (y : V) (hy : y ∈ f '' U) : R y ∈ U ∧ f (R y)=y := by
    simpa only [R,dif_pos hy] using Classical.choose_spec hy
  have hlocal (y : V) (hy : y ∈ f '' U) :
      ∃ P : V → E, ∃ W : Set V, IsOpen W ∧ y ∈ W ∧ ContDiffOn ℝ ∞ P W ∧
        ∀ z ∈ W, f (P z)=z ∧ P z ∈ U := by
    obtain ⟨P,W,hW,hpW,hP,hbase,hnear,hright⟩ :=
      smooth_local_inverse_on_open f hf U hU hD (R y) (hR y hy).1 hdim
    rw [(hR y hy).2] at hpW
    exact ⟨P,W,hW,hpW,hP,hright⟩
  have hO : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨P,W,hW,hyW,hP,hright⟩ := hlocal y hy
    apply mem_of_superset (hW.mem_nhds hyW)
    intro z hz
    exact ⟨P z,(hright z hz).2,(hright z hz).1⟩
  have hRs : ContDiffOn ℝ ∞ R (f '' U) := by
    intro y hy
    obtain ⟨P,W,hW,hyW,hP,hright⟩ := hlocal y hy
    have he : P =ᶠ[𝓝 y] R := by
      filter_upwards [hW.mem_nhds hyW] with z hz
      have hzO : z ∈ f '' U := ⟨P z,(hright z hz).2,(hright z hz).1⟩
      exact hi (hright z hz).2 (hR z hzO).1 ((hright z hz).1.trans (hR z hzO).2.symm)
    exact ((hP.contDiffAt (hW.mem_nhds hyW)).congr_of_eventuallyEq he.symm).contDiffWithinAt
  refine ⟨R,f '' U,hO,rfl,hRs,(fun y hy => ⟨(hR y hy).2,(hR y hy).1⟩),?_⟩
  intro p hp
  have hy : f p ∈ f '' U := ⟨p,hp,rfl⟩
  exact hi (hR (f p) hy).1 hp (hR (f p) hy).2

end
end ContactTopology.TwoArcDisk


namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function Filter Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

def jetTube (p : Space) : Space :=
  let x : Plane := ![p 0,p 1]
  ![p 0,jetMomentum x-p 2*beta x 1,jetHeight x+p 2*momentumV x]
lemma jetTube_smooth : ContDiff ℝ ∞ jetTube := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [jetTube,jetMomentum,jetHeight,beta,dividing,radiusSq,momentumV] <;> fun_prop
lemma jetTube_at_zero (x : Plane) : jetTube (surface x)=jetDisk x := by
  have he : (![x 0,x 1] : Plane)=x := by ext i; fin_cases i <;> rfl
  simp [jetTube,surface,jetDisk,he]
lemma jetTube_derivative_at_zero (x : Plane) (w : Space) :
    fderiv ℝ jetTube (surface x) w=
      ![w 0,momentumU x*w 0+momentumV x*w 1-beta x 1*w 2,
        (jetMomentum x+beta x 0)*w 0+beta x 1*w 1+momentumV x*w 2] := by
  let e (i : Fin 3) : Space →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let B : Space →L[ℝ] Plane := ContinuousLinearMap.pi ![e 0,e 1]
  have hb : HasFDerivAt (fun p : Space => (![p 0,p 1] : Plane)) B (surface x) := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (e 0).hasFDerivAt
    · exact (e 1).hasFDerivAt
  have hP := (jetMomentum_smooth.differentiable (by simp) _).hasFDerivAt.comp (surface x) hb
  have hZ := (jetHeight_smooth.differentiable (by simp) _).hasFDerivAt.comp (surface x) hb
  have hβ := (beta_smooth.differentiable (by simp) _).hasFDerivAt.comp (surface x) hb
  have hv : ContDiff ℝ ∞ momentumV := by unfold momentumV radiusSq; fun_prop
  have hV := (hv.differentiable (by simp) _).hasFDerivAt.comp (surface x) hb
  have hβ1 := (ContinuousLinearMap.proj (R := ℝ) (i := (1:Fin 2))).hasFDerivAt.comp (surface x) hβ
  have h1 := hP.sub ((e 2).hasFDerivAt.mul hβ1)
  have h2 := hZ.add ((e 2).hasFDerivAt.mul hV)
  change HasFDerivAt (𝕜 := ℝ) (fun p => jetTube p 1) _ (surface x) at h1
  change HasFDerivAt (𝕜 := ℝ) (fun p => jetTube p 2) _ (surface x) at h2
  have hd : HasFDerivAt jetTube (ContinuousLinearMap.pi
      ![e 0,fderiv ℝ (fun p => jetTube p 1) (surface x),
        fderiv ℝ (fun p => jetTube p 2) (surface x)]) (surface x) := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (e 0).hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
    · exact h2.differentiableAt.hasFDerivAt
  have hxy : (![x 0,x 1] : Plane)=x := by ext i; fin_cases i <;> rfl
  have hBw : B w=![w 0,w 1] := by ext i; fin_cases i <;> simp [B,e]
  rw [hd.fderiv]
  ext i
  fin_cases i
  · simp [e]
  · change fderiv ℝ (fun p => jetTube p 1) (surface x) w=_
    rw [h1.fderiv]
    simp [e,hBw,surface,hxy,jetMomentum_derivative,jetHeight_derivative]
  · change fderiv ℝ (fun p => jetTube p 2) (surface x) w=_
    rw [h2.fderiv]
    simp [e,hBw,surface,hxy,jetMomentum_derivative,jetHeight_derivative]

lemma jetTube_derivative_injective (x : Plane) (hx : radiusSq x≤1) :
    Injective (fderiv ℝ jetTube (surface x)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro w hw
  rw [jetTube_derivative_at_zero] at hw
  have hu : w 0=0 := congrArg (fun p : Space => p 0) hw
  have hp : momentumV x*w 1-beta x 1*w 2=0 := by
    have hh := congrArg (fun p : Space => p 1) hw
    simpa [hu] using hh
  have hz : beta x 1*w 1+momentumV x*w 2=0 := by
    have hh := congrArg (fun p : Space => p 2) hw
    simpa [hu] using hh
  have hdet : 0 < momentumV x^2+beta x 1^2 := by
    rcases vertical_nonzero x hx with h|h
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (beta x 1)]
    · nlinarith [sq_pos_of_ne_zero h,sq_nonneg (momentumV x)]
  have hv : w 1=0 := by
    have hh : (momentumV x^2+beta x 1^2)*w 1=0 := by
      linear_combination momentumV x*hp+beta x 1*hz
    exact (mul_eq_zero.mp hh).resolve_left hdet.ne'
  have ht : w 2=0 := by
    have hh : (momentumV x^2+beta x 1^2)*w 2=0 := by
      linear_combination -beta x 1*hp+momentumV x*hz
    exact (mul_eq_zero.mp hh).resolve_left hdet.ne'
  ext i
  fin_cases i <;> simp [hu,hv,ht]

lemma jetTube_locally_injective (x : Plane) (hx : radiusSq x≤1) :
    ∃ U : Set Space, IsOpen U ∧ surface x ∈ U ∧ InjOn jetTube U := by
  let A : Space ≃L[ℝ] Space :=
    (LinearEquiv.ofBijective (fderiv ℝ jetTube (surface x)).toLinearMap
      ⟨jetTube_derivative_injective x hx,
        (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
          (jetTube_derivative_injective x hx)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt jetTube (A : Space →L[ℝ] Space) (surface x) :=
    (jetTube_smooth.differentiable (by simp) _).hasFDerivAt
  let e := jetTube_smooth.contDiffAt.toOpenPartialHomeomorph jetTube hd (by simp)
  have he : (e : Space → Space)=jetTube :=
    jetTube_smooth.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp)
  have hp : surface x ∈ e.source :=
    jetTube_smooth.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e.source,e.open_source,hp,?_⟩
  intro p hp q hq hpq
  calc p=e.symm (e p) := (e.left_inv hp).symm
       _=e.symm (e q) := congrArg e.symm (by rw [he]; exact hpq)
       _=q := e.left_inv hq

theorem exists_jetDisk_inverse_collar : ∃ U O : Set Space, ∃ R : Space → Space,
    IsOpen U ∧ IsOpen O ∧ surface '' {x : Plane | radiusSq x≤1} ⊆ U ∧
    O=jetTube '' U ∧ ContDiffOn ℝ ∞ R O ∧
    (∀ y ∈ O, jetTube (R y)=y ∧ R y ∈ U) ∧ (∀ p ∈ U, R (jetTube p)=p) := by
  let A : Set Space := surface '' {x : Plane | radiusSq x≤1}
  have hs : Continuous surface := by change Continuous (fun x : Plane => (![x 0,x 1,0] : Space)); fun_prop
  have hA : IsCompact A := disk_compact.image hs
  have hi : InjOn jetTube A := by
    rintro p ⟨x,hx,rfl⟩ q ⟨y,hy,rfl⟩ he
    rw [jetTube_at_zero,jetTube_at_zero] at he
    exact congrArg surface (jetDisk_injective hx hy he)
  obtain ⟨U,hU,hAU,hUi⟩ := compact_injective_neighborhood jetTube jetTube_smooth.continuous A hA hi (by
    rintro p ⟨x,hx,rfl⟩
    exact jetTube_locally_injective x hx)
  let V : Set Space := (fun p => fderiv ℝ jetTube p) ⁻¹'
    range ((↑) : (Space ≃L[ℝ] Space) → Space →L[ℝ] Space)
  have hDf : Continuous (fun p => fderiv ℝ jetTube p) :=
    (show ContDiff ℝ ∞ (fun p => fderiv ℝ jetTube p) from jetTube_smooth.fderiv_right (by simp)).continuous
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage hDf
  let W : Set Space := U ∩ V
  have hW : IsOpen W := hU.inter hV
  have hAW : A ⊆ W := by
    rintro p hp
    obtain ⟨x,hx,rfl⟩ := hp
    refine ⟨hAU ⟨x,hx,rfl⟩,?_⟩
    let L : Space ≃L[ℝ] Space :=
      (LinearEquiv.ofBijective (fderiv ℝ jetTube (surface x)).toLinearMap
        ⟨jetTube_derivative_injective x hx,
          (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
            (jetTube_derivative_injective x hx)⟩).toContinuousLinearEquiv
    exact ⟨L,rfl⟩
  have hWi : InjOn jetTube W := hUi.mono inter_subset_left
  have hWD : ∀ p ∈ W, Injective (fderiv ℝ jetTube p) := by
    intro p hp
    obtain ⟨L,hL⟩ := hp.2
    change (L : Space →L[ℝ] Space)=fderiv ℝ jetTube p at hL
    rw [← hL]
    exact L.injective
  obtain ⟨R,O,hO,hOeq,hRs,hRight,hLeft⟩ :=
    smooth_inverse_on_injective_open jetTube jetTube_smooth W hW hWi hWD rfl
  exact ⟨W,O,R,hW,hO,hAW,hOeq,hRs,hRight,hLeft⟩

theorem exists_jetDisk_hamiltonian : ∃ H : Space → ℝ,
    ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
    ∀ x : Plane, radiusSq x≤1 → H (jetDisk x)=dividing x ∧
      ∀ w : Plane, fderiv ℝ H (jetDisk x) (fderiv ℝ jetDisk x w)=fderiv ℝ dividing x w := by
  obtain ⟨U,O,R,hU,hO,hDU,hOeq,hR,hRight,hLeft⟩ := exists_jetDisk_inverse_collar
  let g : Space → ℝ := fun y => dividing ![R y 0,R y 1]
  have hg : ContDiffOn ℝ ∞ g O := by
    apply dividing_smooth.comp_contDiffOn
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · exact (contDiff_apply ℝ ℝ (0:Fin 3)).comp_contDiffOn hR
    · exact (contDiff_apply ℝ ℝ (1:Fin 3)).comp_contDiffOn hR
  let C : Set Space := jetDisk '' {x : Plane | radiusSq x≤1}
  have hC : IsCompact C := disk_compact.image jetDisk_smooth.continuous
  have hCO : C ⊆ O := by
    rintro y ⟨x,hx,rfl⟩
    rw [hOeq]
    exact ⟨surface x,hDU ⟨x,hx,rfl⟩,jetTube_at_zero x⟩
  obtain ⟨H,hH,hHc,hjet⟩ := SmoothJetExtension.compact_first_jet_extension C hC g (fderiv ℝ g)
    (by intro p hp; exact ⟨O,hO,hCO hp,g,hg,fun q hq => ⟨rfl,rfl⟩⟩)
  refine ⟨H,hH,hHc,?_⟩
  intro x hx
  have hpU : surface x ∈ U := hDU ⟨x,hx,rfl⟩
  have hloc : (g ∘ jetDisk)=ᶠ[𝓝 x] dividing := by
    have hs : Continuous surface := by change Continuous (fun x : Plane => (![x 0,x 1,0] : Space)); fun_prop
    filter_upwards [hs.continuousAt.preimage_mem_nhds (hU.mem_nhds hpU)] with y hy
    change dividing ![R (jetDisk y) 0,R (jetDisk y) 1]=dividing y
    rw [← jetTube_at_zero y,hLeft _ hy]
    have he : (![surface y 0,surface y 1] : Plane)=y := by ext i; fin_cases i <;> rfl
    rw [he]
  have hJ := hjet (jetDisk x) ⟨x,hx,rfl⟩
  refine ⟨hJ.1.trans hloc.eq_of_nhds,?_⟩
  intro w
  have hd := hloc.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x ((hg.contDiffAt (hO.mem_nhds (hCO ⟨x,hx,rfl⟩))).differentiableAt (by simp))
    (jetDisk_smooth.differentiable (by simp) x)] at hd
  rw [hJ.2]
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L w) hd

end
end ContactTopology.TwoArcDisk


namespace ContactTopology.TwoArcHamiltonian
open Set Function GrayStability
open scoped ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev V := Fin 3 → ℝ
def dot (a v : V) : ℝ := a 0*v 0+a 1*v 1+a 2*v 2

def cross (a b : V) : V :=
  ![a 1*b 2-a 2*b 1,a 2*b 0-a 0*b 2,a 0*b 1-a 1*b 0]

def covector : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ)

lemma covector_apply (a v : V) : covector a v = dot a v := by
  simp [covector,dot]

lemma vector_expansion (v : V) :
    v = v 0 • Pi.single 0 1+v 1 • Pi.single 1 1+v 2 • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp

def curlLinear (D : V →L[ℝ] V) : V :=
  ![D (Pi.single 1 1) 2-D (Pi.single 2 1) 1,
    D (Pi.single 2 1) 0-D (Pi.single 0 1) 2,
    D (Pi.single 0 1) 1-D (Pi.single 1 1) 0]

lemma exterior_cross (D : V →L[ℝ] V) (u v : V) :
    dot (D u) v-dot (D v) u = dot (curlLinear D) (cross u v) := by
  have hu : D u = u 0 • D (Pi.single 0 1)+u 1 • D (Pi.single 1 1)+u 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion u]
    simp only [map_add,map_smul]
  have hv : D v = v 0 • D (Pi.single 0 1)+v 1 • D (Pi.single 1 1)+v 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion v]
    simp only [map_add,map_smul]
  rw [hu,hv]
  simp [dot,curlLinear,cross]
  ring

lemma moser_algebra (a b c v : V) (h : dot a c ≠ 0) :
    dot a ((dot a c)⁻¹ • cross a b) = 0 ∧
    dot b v+dot c (cross ((dot a c)⁻¹ • cross a b) v) =
      (dot c b/dot a c)*dot a v := by
  constructor
  · simp [dot,cross]
    ring
  · have hp : dot c (cross ((dot a c)⁻¹ • cross a b) v) =
        (dot a c)⁻¹*(dot c b*dot a v-dot a c*dot b v) := by
      simp [dot,cross]
      ring
    rw [hp,div_eq_mul_inv]
    calc
      dot b v+(dot a c)⁻¹*(dot c b*dot a v-dot a c*dot b v) =
          (1-(dot a c)⁻¹*dot a c)*dot b v+(dot c b*(dot a c)⁻¹)*dot a v := by ring
      _ = _ := by rw [inv_mul_cancel₀ h]; ring


def hamiltonianAlgebra (a c : V) (H : ℝ) (g : V) : V :=
  (dot a c)⁻¹ • (H • c+cross a g)

lemma hamiltonian_algebra (a c g v : V) (H : ℝ) (hQ : dot a c ≠ 0) :
    dot a (hamiltonianAlgebra a c H g) = H ∧
    dot g v+dot c (cross (hamiltonianAlgebra a c H g) v) =
      (dot c g/dot a c)*dot a v := by
  have hα : dot a (hamiltonianAlgebra a c H g) = (dot a c)⁻¹*(H*dot a c) := by
    simp [hamiltonianAlgebra,dot,cross,Matrix.vecHead,Matrix.vecTail]
    ring
  refine ⟨?_,?_⟩
  · rw [hα]
    calc (dot a c)⁻¹*(H*dot a c) = H*((dot a c)⁻¹*dot a c) := by ring
      _ = H := by rw [inv_mul_cancel₀ hQ,mul_one]
  · have he : dot c (cross (hamiltonianAlgebra a c H g) v) =
        dot c (cross ((dot a c)⁻¹ • cross a g) v) := by
      simp [hamiltonianAlgebra,dot,cross,Matrix.vecHead,Matrix.vecTail]
      ring
    rw [he]
    exact (moser_algebra a g c v hQ).2

/-- For H=h(z)u(x,y), the contact field has normal velocity exactly h(z).
Its horizontal part is the characteristic field times h'(z). -/
def gradient3 (H : V → ℝ) (y : V) : V :=
  ![fderiv ℝ H y (Pi.single 0 1),fderiv ℝ H y (Pi.single 1 1),fderiv ℝ H y (Pi.single 2 1)]

lemma gradient3_pair (H : V → ℝ) (y v : V) : dot (gradient3 H y) v = fderiv ℝ H y v := by
  have he : fderiv ℝ H y v = v 0*fderiv ℝ H y (Pi.single 0 1)+
      v 1*fderiv ℝ H y (Pi.single 1 1)+v 2*fderiv ℝ H y (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion v]
    simp
  rw [he]
  simp [dot,gradient3]
  ring

def hamiltonianField (a : V → V) (H : V → ℝ) (y : V) : V :=
  hamiltonianAlgebra (a y) (curlLinear (fderiv ℝ a y)) (H y) (gradient3 H y)

lemma cross_contDiff (f g : V → V) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun y => cross (f y) (g y)) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross] <;> fun_prop

lemma hamiltonianField_contDiff (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (hamiltonianField a H) := by
  have hda : ContDiff ℝ ∞ (fderiv ℝ a) := ha.fderiv_right (by simp)
  have hdH : ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ (fun y => curlLinear (fderiv ℝ a y)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [curlLinear] <;> fun_prop
  have hg : ContDiff ℝ ∞ (gradient3 H) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [gradient3] <;> fun_prop
  have hq : ContDiff ℝ ∞ (fun y => dot (a y) (curlLinear (fderiv ℝ a y))) := by
    unfold dot
    fun_prop
  exact (hq.inv hQ).smul ((hH.smul hc).add (cross_contDiff a (gradient3 H) ha hg))

/-- Cartan's identity is checked in the ambient coefficient formulation,
including the derivative of the nonzero Hamiltonian. -/
theorem hamiltonianField_lie (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) (y v : V) :
    lieDerivOneForm (hamiltonianField a H) (fun z => covector (a z)) y v =
      (dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/
        dot (a y) (curlLinear (fderiv ℝ a y)))*covector (a y) v := by
  let α : OneForm 3 := fun z => covector (a z)
  let X := hamiltonianField a H
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  have hX : ContDiff ℝ ∞ X := hamiltonianField_contDiff a H ha hH hQ
  have hD : ∀ r w, fderiv ℝ α y r w = dot (fderiv ℝ a y r) w := by
    intro r w
    have hd := covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt α _ y at hd
    rw [hd.fderiv]
    exact covector_apply _ _
  have hp : (fun z => α z (X z)) = H := by
    ext z
    exact (hamiltonian_algebra (a z) (curlLinear (fderiv ℝ a z)) (gradient3 H z) (0:V) (H z) (hQ z)).1
  have hd := (hα.differentiable (by simp) y).hasFDerivAt.clm_apply
    (hX.differentiable (by simp) y).hasFDerivAt
  have hval := congrArg (fun L : V →L[ℝ] ℝ => L v) hd.fderiv
  rw [hp] at hval
  change fderiv ℝ H y v = α y (fderiv ℝ X y v)+fderiv ℝ α y v (X y) at hval
  rw [hD] at hval
  have hm := (hamiltonian_algebra (a y) (curlLinear (fderiv ℝ a y))
    (gradient3 H y) v (H y) (hQ y)).2
  rw [gradient3_pair,← exterior_cross] at hm
  change fderiv ℝ H y v+(dot (fderiv ℝ a y (X y)) v-dot (fderiv ℝ a y v) (X y)) = _ at hm
  change fderiv ℝ α y (X y) v+α y (fderiv ℝ X y v) = _
  rw [hD,covector_apply (a y) v]
  linarith


end
end ContactTopology.TwoArcHamiltonian

namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function GrayStability
open ContactTopology.TwoArcHamiltonian
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma jetCoefficients_smooth : ContDiff ℝ ∞ jetCoefficients := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [jetCoefficients] <;> fun_prop
lemma jetCoefficients_derivative (y v : Space) : fderiv ℝ jetCoefficients y v=![-v 1,0,0] := by
  let e : Space →L[ℝ] ℝ := ContinuousLinearMap.proj 1
  have hd : HasFDerivAt jetCoefficients (ContinuousLinearMap.pi ![-e,0,0]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact e.hasFDerivAt.neg
    · exact hasFDerivAt_const (𝕜 := ℝ) (0:ℝ) y
    · exact hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) y
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [e]
lemma jet_volume (y : Space) : dot (jetCoefficients y) (curlLinear (fderiv ℝ jetCoefficients y))=1 := by
  simp [curlLinear,jetCoefficients_derivative,jetCoefficients,dot]
lemma jetContactField_eq (H : Space → ℝ) : jetContactField H=hamiltonianField jetCoefficients H := by
  funext y
  simp [jetContactField,hamiltonianField,hamiltonianAlgebra,
    curlLinear,jetCoefficients_derivative,jetCoefficients,cross,dot,gradient3]
  ring
lemma jetContactField_formula (H : Space → ℝ) (y : Space) : jetContactField H y=
    ![-gradient3 H y 1,gradient3 H y 0+y 1*gradient3 H y 2,H y-y 1*gradient3 H y 1] := rfl

lemma jetContactField_value (H : Space → ℝ) (y : Space) : jetForm y (jetContactField H y)=H y := by
  rw [jetContactField_formula]
  dsimp [jetForm]
  ring
lemma jetContactField_smooth (H : Space → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (jetContactField H) := by
  rw [jetContactField_eq]
  exact hamiltonianField_contDiff jetCoefficients H jetCoefficients_smooth hH (by intro y; rw [jet_volume]; norm_num)
lemma jetContactField_lie (H : Space → ℝ) (hH : ContDiff ℝ ∞ H) (y v : Space) :
    lieDerivOneForm (jetContactField H) (fun z => covector (jetCoefficients z)) y v=
      gradient3 H y 2*jetForm y v := by
  have he := hamiltonianField_lie jetCoefficients H jetCoefficients_smooth hH
    (by intro z; rw [jet_volume]; norm_num) y v
  simpa [jetContactField_eq,jet_volume,curlLinear,jetCoefficients_derivative,
    covector_apply,dot,jetCoefficients,jetForm,sub_eq_add_neg,add_comm] using he

lemma jetContactField_coordinate_lie (H : Space → ℝ) (hH : ContDiff ℝ ∞ H) (y v : Space) :
    -(jetContactField H y 1)*v 0+jetForm y (fderiv ℝ (jetContactField H) y v)=
      fderiv ℝ H y (Pi.single 2 1)*jetForm y v := by
  have hd := covector.hasFDerivAt.comp y (jetCoefficients_smooth.differentiable (by simp) y).hasFDerivAt
  change HasFDerivAt (𝕜 := ℝ) (fun z => covector (jetCoefficients z)) _ y at hd
  have hleft : fderiv ℝ (fun z => covector (jetCoefficients z)) y (jetContactField H y) v=
      -(jetContactField H y 1)*v 0 := by
    rw [hd.fderiv]
    simp [covector_apply,dot,jetCoefficients_derivative]
  have ha (z w : Space) : covector (jetCoefficients z) w=jetForm z w := by
    simp [covector_apply,dot,jetCoefficients,jetForm]
    ring
  have he := jetContactField_lie H hH y v
  unfold lieDerivOneForm at he
  rw [hleft,ha] at he
  simpa [gradient3,Matrix.vecHead,Matrix.vecTail] using he

lemma beta_curl (x : Plane) : fderiv ℝ beta x (Pi.single 0 1) 1-
    fderiv ℝ beta x (Pi.single 1 1) 0=momentumV x := by
  simp [beta_derivative,beta,gradient,dividing,radiusSq,momentumV]
  ring

lemma jetContactField_transverse (H : Space → ℝ) (x : Plane)
    (hval : H (jetDisk x)=dividing x)
    (hder : ∀ w : Plane, fderiv ℝ H (jetDisk x) (fderiv ℝ jetDisk x w)=fderiv ℝ dividing x w)
    (w : Plane) : jetContactField H (jetDisk x)≠fderiv ℝ jetDisk x w := by
  intro he
  let g : Space := gradient3 H (jetDisk x)
  have h0 : -g 1=w 0 := by
    have hh := congrArg (fun y : Space => y 0) he
    simpa only [jetContactField_formula,jetDisk_derivative,Matrix.cons_val_zero] using hh
  have h1 : g 0+jetMomentum x*g 2=momentumU x*w 0+momentumV x*w 1 := by
    have hh := congrArg (fun y : Space => y 1) he
    simpa [jetContactField_formula,jetDisk_derivative,jetDisk,g] using hh
  have hv : dividing x=beta x 0*w 0+beta x 1*w 1 := by
    rw [← hval,← jetContactField_value H (jetDisk x),he,jetDisk_contact]
  have hdu : g 0+g 1*momentumU x+g 2*(jetMomentum x+beta x 0)=gradient x 0 := by
    have hh := hder (Pi.single 0 1)
    rw [← gradient3_pair] at hh
    simpa [jetDisk_derivative,dividing_derivative,dot,g] using hh
  have hdv : g 1*momentumV x+g 2*beta x 1=gradient x 1 := by
    have hh := hder (Pi.single 1 1)
    rw [← gradient3_pair] at hh
    simpa [jetDisk_derivative,dividing_derivative,dot,g] using hh
  have hfu : gradient x 0=momentumV x*w 1+g 2*beta x 0 := by
    linear_combination -hdu+h1-momentumU x*h0
  have hfv : gradient x 1= -momentumV x*w 0+g 2*beta x 1 := by
    linear_combination -hdv-momentumV x*h0
  have hzero : beta x 0*gradient x 1-beta x 1*gradient x 0+dividing x*momentumV x=0 := by
    rw [hfu,hfv,hv]
    ring
  have hpos : 0 < beta x 0*gradient x 1-beta x 1*gradient x 0+dividing x*momentumV x := by
    simpa [dividing_derivative,beta_curl] using contact_positive x
  rw [hzero] at hpos
  norm_num at hpos

/-- The explicit Legendrian-boundary disk is actually convex in standard
contact three-space, with its entire two-arc dividing set constructed. -/
theorem exists_actual_jet_convex_disk_field : ∃ H : Space → ℝ,
    ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
    ContDiff ℝ ∞ (jetContactField H) ∧
    (∀ y v, lieDerivOneForm (jetContactField H) (fun z => covector (jetCoefficients z)) y v=
      gradient3 H y 2*jetForm y v) ∧
    ∀ x : Plane, radiusSq x≤1 →
      (∀ w : Plane, jetContactField H (jetDisk x)≠fderiv ℝ jetDisk x w) ∧
      jetForm (jetDisk x) (jetContactField H (jetDisk x))=dividing x := by
  obtain ⟨H,hH,hHc,hjet⟩ := exists_jetDisk_hamiltonian
  refine ⟨H,hH,hHc,jetContactField_smooth H hH,jetContactField_lie H hH,?_⟩
  intro x hx
  exact ⟨jetContactField_transverse H x (hjet x hx).1 (hjet x hx).2,
    (jetContactField_value H (jetDisk x)).trans (hjet x hx).1⟩

end
end ContactTopology.TwoArcDisk

namespace ContactTopology.TwoArcDisk
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma jetDividingArc_embedding (σ : ℝ) (hσ : σ^2=1) : IsEmbedding (jetDividingArc σ) := by
  have hc : Continuous (jetDividingArc σ) := jetDisk_smooth.continuous.comp (arc_embedding σ).continuous
  apply hc.isClosedEmbedding ?_ |>.isEmbedding
  intro t s he
  have hp := jetDisk_injective (arc_in_disk_and_dividing σ t.val hσ t.property).1
    (arc_in_disk_and_dividing σ s.val hσ s.property).1 he
  apply Subtype.ext
  exact congrArg (fun x : Plane => x 1) hp

lemma jetDividingArc_smooth_regular (σ t : ℝ) (hσ : σ^2=1) (ht : t ∈ Icc (-1/2:ℝ) (1/2)) :
    ContDiffAt ℝ ∞ (jetDisk ∘ arc σ) t ∧ deriv (jetDisk ∘ arc σ) t≠0 := by
  have hs := jetDisk_smooth.contDiffAt.comp t (arc_smooth σ t ht)
  refine ⟨hs,?_⟩
  intro he
  have hd := (jetDisk_smooth.differentiable (by simp) (arc σ t)).hasFDerivAt.comp_hasDerivAt t
    ((arc_smooth σ t ht).differentiableAt (by simp)).hasDerivAt
  have hz : fderiv ℝ jetDisk (arc σ t) (deriv (arc σ) t)=0 := by rw [← hd.deriv]; exact he
  have hi := jetDisk_immersion _ (arc_in_disk_and_dividing σ t hσ ht).1
  exact arc_regular σ t ht (hi (by simpa using hz))

lemma jetDividingArc_proper (σ : ℝ) (hσ : σ^2=1) (t : Icc (-1/2:ℝ) (1/2)) :
    jetDividingArc σ t ∈ jetDisk '' unitCircle ↔ t.val= -1/2 ∨ t.val=1/2 := by
  rw [← arc_meets_boundary_only_at_endpoints σ t.val hσ t.property]
  constructor
  · rintro ⟨x,hx,he⟩
    have hxd : radiusSq x≤1 := le_of_eq hx
    have hi := jetDisk_injective hxd (arc_in_disk_and_dividing σ t.val hσ t.property).1 he
    rw [← hi]
    exact hx
  · intro ht
    exact ⟨arc σ t.val,ht,rfl⟩

lemma jetDividingArcs_disjoint : Disjoint (range (jetDividingArc 1)) (range (jetDividingArc (-1))) := by
  apply Set.disjoint_left.mpr
  rintro y ⟨t,rfl⟩ ⟨s,he⟩
  have hp := jetDisk_injective (arc_in_disk_and_dividing (-1) s.val (by norm_num) s.property).1
    (arc_in_disk_and_dividing 1 t.val (by norm_num) t.property).1 he
  exact (Set.disjoint_left.mp arcs_disjoint) ⟨t,rfl⟩ ⟨s,hp⟩

theorem actual_jet_convex_disk_with_two_dividing_arcs :
    ContDiff ℝ ∞ jetDisk ∧
    IsEmbedding (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) ∧
    (∀ x : Plane, radiusSq x≤1 → Injective (fderiv ℝ jetDisk x)) ∧
    (∀ x ∈ unitCircle, jetForm (jetDisk x) (fderiv ℝ jetDisk x (circleTangent x))=0) ∧
    (∀ σ : ℝ, σ^2=1 → IsEmbedding (jetDividingArc σ) ∧
      (∀ t ∈ Icc (-1/2:ℝ) (1/2), ContDiffAt ℝ ∞ (jetDisk ∘ arc σ) t ∧
        deriv (jetDisk ∘ arc σ) t≠0) ∧
      (∀ t : Icc (-1/2:ℝ) (1/2), jetDividingArc σ t ∈ jetDisk '' unitCircle ↔
        t.val= -1/2 ∨ t.val=1/2)) ∧
    Disjoint (range (jetDividingArc 1)) (range (jetDividingArc (-1))) ∧
    ∃ H : Space → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ContDiff ℝ ∞ (jetContactField H) ∧
      (∀ y v, -(jetContactField H y 1)*v 0+jetForm y (fderiv ℝ (jetContactField H) y v)=
        fderiv ℝ H y (Pi.single 2 1)*jetForm y v) ∧
      (∀ x : Plane, radiusSq x≤1 →
        (∀ w : Plane, jetContactField H (jetDisk x)≠fderiv ℝ jetDisk x w) ∧
        jetForm (jetDisk x) (jetContactField H (jetDisk x))=dividing x) ∧
      {y : Space | ∃ x : Plane, radiusSq x≤1 ∧ jetDisk x=y ∧ jetForm y (jetContactField H y)=0}=
        range (jetDividingArc 1) ∪ range (jetDividingArc (-1)) := by
  obtain ⟨H,hH,hHc,hX,hLie,hfield⟩ := exists_actual_jet_convex_disk_field
  refine ⟨jetDisk_smooth,jetDisk_embedding,jetDisk_immersion,jetDisk_boundary_legendrian,
    (fun σ hσ => ⟨jetDividingArc_embedding σ hσ,
      (fun t ht => jetDividingArc_smooth_regular σ t hσ ht),jetDividingArc_proper σ hσ⟩),
    jetDividingArcs_disjoint,H,hH,hHc,hX,jetContactField_coordinate_lie H hH,hfield,?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl,hz⟩
    rw [(hfield x hx).2] at hz
    obtain ⟨t,ht,he|he⟩ := (dividing_is_two_arcs x hx).mp hz
    · exact Or.inl ⟨⟨t,ht⟩,congrArg jetDisk he.symm⟩
    · exact Or.inr ⟨⟨t,ht⟩,congrArg jetDisk he.symm⟩
  · rintro (⟨t,rfl⟩|⟨t,rfl⟩)
    · have hg := arc_in_disk_and_dividing 1 t.val (by norm_num) t.property
      exact ⟨arc 1 t.val,hg.1,rfl,((hfield _ hg.1).2).trans hg.2⟩
    · have hg := arc_in_disk_and_dividing (-1) t.val (by norm_num) t.property
      exact ⟨arc (-1) t.val,hg.1,rfl,((hfield _ hg.1).2).trans hg.2⟩

end
end ContactTopology.TwoArcDisk

open BirkhoffGlobalSection ContactTopology.TwoArcDisk Set Function Topology
open scoped ContDiff
theorem solution :
    ContDiff ℝ ∞ jetDisk ∧
    IsEmbedding (fun x : {x : Plane // radiusSq x≤1} => jetDisk x.val) ∧
    (∀ x : Plane, radiusSq x≤1 → Injective (fderiv ℝ jetDisk x)) ∧
    (∀ x ∈ unitCircle, jetForm (jetDisk x) (fderiv ℝ jetDisk x (circleTangent x))=0) ∧
    (∀ σ : ℝ, σ^2=1 → IsEmbedding (jetDividingArc σ) ∧
      (∀ t ∈ Icc (-1/2:ℝ) (1/2), ContDiffAt ℝ ∞ (jetDisk ∘ arc σ) t ∧
        deriv (jetDisk ∘ arc σ) t≠0) ∧
      (∀ t : Icc (-1/2:ℝ) (1/2), jetDividingArc σ t ∈ jetDisk '' unitCircle ↔
        t.val= -1/2 ∨ t.val=1/2)) ∧
    Disjoint (range (jetDividingArc 1)) (range (jetDividingArc (-1))) ∧
    ∃ H : Space → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      ContDiff ℝ ∞ (jetContactField H) ∧
      (∀ y v, -(jetContactField H y 1)*v 0+jetForm y (fderiv ℝ (jetContactField H) y v)=
        fderiv ℝ H y (Pi.single 2 1)*jetForm y v) ∧
      (∀ x : Plane, radiusSq x≤1 →
        (∀ w : Plane, jetContactField H (jetDisk x)≠fderiv ℝ jetDisk x w) ∧
        jetForm (jetDisk x) (jetContactField H (jetDisk x))=dividing x) ∧
      {y : Space | ∃ x : Plane, radiusSq x≤1 ∧ jetDisk x=y ∧ jetForm y (jetContactField H y)=0}=
        range (jetDividingArc 1) ∪ range (jetDividingArc (-1)) := by
  exact ContactTopology.TwoArcDisk.actual_jet_convex_disk_with_two_dividing_arcs
