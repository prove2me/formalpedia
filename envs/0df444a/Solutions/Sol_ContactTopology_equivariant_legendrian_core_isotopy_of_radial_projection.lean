-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_isotopy_of_radial_projection
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:43:22.576149+00:00
-- url     : https://prove2.me/submissions/ae4edc88-5a95-43c2-96b7-b5913688775f

import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.ContinuousInverse
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood


namespace ContactTopology.CoreProjection
open BirkhoffGlobalSection Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section


noncomputable def circleCurve (u : Plane) (s : ℝ) : Plane :=
  Real.cos s • u + Real.sin s • circleTangent u

lemma circleCurve_zero (u : Plane) : circleCurve u 0 = u := by simp [circleCurve]

lemma circleCurve_mem (u : Plane) (hu : u ∈ unitCircle) (s : ℝ) : circleCurve u s ∈ unitCircle := by
  have he : planeNormSq (circleCurve u s) =
      (Real.cos s ^ 2 + Real.sin s ^ 2) * planeNormSq u := by
    simp only [circleCurve, circleTangent, planeNormSq, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  change planeNormSq (circleCurve u s) = 1
  rw [he, Real.cos_sq_add_sin_sq, one_mul]
  exact hu

lemma circleCurve_hasDerivAt (u : Plane) : HasDerivAt (circleCurve u) (circleTangent u) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos 0).mul_const (u i)).add
    ((Real.hasDerivAt_sin 0).mul_const (circleTangent u i))
  change HasDerivAt (fun s => Real.cos s * u i + Real.sin s * circleTangent u i)
    (circleTangent u i) 0
  convert! h using 1 <;>
    simp only [Real.sin_zero, Real.cos_zero, neg_zero, zero_mul, one_mul, zero_add]


lemma circleCurve_hasDerivAt_all (u : Plane) (s : ℝ) :
    HasDerivAt (circleCurve u) (circleTangent (circleCurve u s)) s := by
  apply hasDerivAt_pi.mpr
  intro i
  have h := ((Real.hasDerivAt_cos s).mul_const (u i)).add
    ((Real.hasDerivAt_sin s).mul_const (circleTangent u i))
  change HasDerivAt (fun r => Real.cos r * u i + Real.sin r * circleTangent u i)
    (circleTangent (circleCurve u s) i) s
  convert! h using 1
  fin_cases i <;> simp [circleTangent, circleCurve] <;> ring

lemma fderiv_circle_tangent_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Plane → E) (u : Plane) (hu : u ∈ unitCircle)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (he : EqOn f g unitCircle) :
    fderiv ℝ f u (circleTangent u) = fderiv ℝ g u (circleTangent u) := by
  have hf' : DifferentiableAt ℝ f (circleCurve u 0) := by rwa [circleCurve_zero]
  have hg' : DifferentiableAt ℝ g (circleCurve u 0) := by rwa [circleCurve_zero]
  have hff := hf'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  have hgg := hg'.hasFDerivAt.comp_hasDerivAt 0 (circleCurve_hasDerivAt u)
  rw [circleCurve_zero] at hff hgg
  have heq : (fun s => f (circleCurve u s)) = (fun s => g (circleCurve u s)) := by
    funext s
    exact he (circleCurve_mem u hu s)
  change HasDerivAt (fun s => f (circleCurve u s)) (fderiv ℝ f u (circleTangent u)) 0 at hff
  rw [heq] at hff
  exact hff.unique hgg



def core (u : Plane) : Phase := ![u 0,u 1,0,0]
def planeIn : Plane →L[ℝ] (Fin 3 → ℝ) := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ),ContinuousLinearMap.proj 1,0]
@[simp] lemma planeIn_apply (u : Plane) : planeIn u=![u 0,u 1,0] := by ext i; fin_cases i <;> simp [planeIn]

lemma core_mem (u : Plane) (hu : u ∈ unitCircle) : core u ∈ unitThreeSphere := by
  have hs : u 0^2+u 1^2=1 := hu
  change u 0^2+u 1^2+(0^2+0^2)=1
  simpa using hs

lemma core_neg (u : Plane) : core (-u)= -core u := by ext i; fin_cases i <;> simp [core]
def qMap : Phase →L[ℝ] Plane := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ),ContinuousLinearMap.proj 1]
@[simp] lemma qMap_apply (p : Phase) : qMap p=![p 0,p 1] := by ext i; fin_cases i <;> simp [qMap]

def fiberScale (s : ℝ) : Phase →L[ℝ] Phase := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ),ContinuousLinearMap.proj 1,
    s • ContinuousLinearMap.proj 2,s • ContinuousLinearMap.proj 3]
@[simp] lemma fiberScale_apply (s : ℝ) (p : Phase) : fiberScale s p=![p 0,p 1,s*p 2,s*p 3] := by
  ext i
  fin_cases i <;> simp [fiberScale]

lemma fiberScale_contact (s : ℝ) (p v : Phase) :
    phaseRadialContact (fiberScale s p) (fiberScale s v)=s*phaseRadialContact p v := by
  simp [phaseRadialContact,phaseSymplecticForm]
  ring

lemma contact_scaled (a b : ℝ) (p v : Phase) :
    phaseRadialContact (a • p) (a • v+b • p)=a^2*phaseRadialContact p v := by
  simp [phaseRadialContact,phaseSymplecticForm]
  ring

def radialCoefficient (f : Plane → Phase) (u : Plane) : ℝ := f u 0*u 0+f u 1*u 1

lemma radial_projection (p : Phase) (u : Plane) (hu : u ∈ unitCircle)
    (hdet : p 0*u 1-p 1*u 0=0) :
    qMap p=(p 0*u 0+p 1*u 1) • u := by
  have hs : u 0^2+u 1^2=1 := hu
  ext i
  fin_cases i <;> simp [qMap]
  · nlinarith [congrArg (fun z : ℝ => z*u 1) hdet,congrArg (fun z : ℝ => z*p 0) hs]
  · nlinarith [congrArg (fun z : ℝ => z*u 0) hdet,congrArg (fun z : ℝ => z*p 1) hs]

def recover (p : Phase) : Plane := (Real.sqrt (planeNormSq (qMap p)))⁻¹ • qMap p

lemma recover_scaled (p : Phase) (u : Plane) (hu : u ∈ unitCircle)
    (a : ℝ) (ha : 0 < a) (hq : qMap p=a • u) : recover p=u := by
  have hn : planeNormSq (qMap p)=a^2 := by
    rw [hq]
    change (a*u 0)^2+(a*u 1)^2=a^2
    have hs : u 0^2+u 1^2=1 := hu
    nlinarith [congrArg (fun z : ℝ => a^2*z) hs]
  unfold recover
  rw [hn,Real.sqrt_sq ha.le,hq,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]

lemma recover_contDiffAt (p : Phase) (hp : 0 < planeNormSq (qMap p)) :
    ContDiffAt ℝ ∞ recover p := by
  have hsq : ContDiff ℝ ∞ (fun p : Phase => planeNormSq (qMap p)) := by
    unfold planeNormSq
    fun_prop
  exact ((hsq.contDiffAt.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul qMap.contDiff.contDiffAt

def radius (f : Plane → Phase) (t : ℝ) (u : Plane) : ℝ :=
  (f u 0)^2+(f u 1)^2+(1-t)^2*((f u 2)^2+(f u 3)^2)+(planeNormSq u-1)^2

def weight (f : Plane → Phase) (t : ℝ) (u : Plane) : ℝ := (Real.sqrt (radius f t u))⁻¹
def contraction (f : Plane → Phase) (t : ℝ) (u : Plane) : Phase :=
  weight f t u • fiberScale (1-t) (f u)

lemma radius_positive (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u) (t : ℝ) (u : Plane) :
    0 < radius f t u := by
  have hp : 0 ≤ (1-t)^2*((f u 2)^2+(f u 3)^2) :=
    mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  by_contra hn
  have hr : radius f t u ≤ 0 := not_lt.mp hn
  have hz : planeNormSq u-1=0 := by
    unfold radius at hr
    nlinarith [sq_nonneg (f u 0),sq_nonneg (f u 1),sq_nonneg (planeNormSq u-1)]
  have h0 : f u 0=0 := by unfold radius at hr; nlinarith [sq_nonneg (f u 1),sq_nonneg (planeNormSq u-1)]
  have h1 : f u 1=0 := by unfold radius at hr; nlinarith [sq_nonneg (f u 0),sq_nonneg (planeNormSq u-1)]
  have hh := hq u (by change planeNormSq u=1; linarith)
  simp [radialCoefficient,h0,h1] at hh

lemma radius_contDiff (f : Plane → Phase) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => radius f p.1 p.2) := by
  unfold radius planeNormSq
  fun_prop

lemma weight_contDiff (f : Plane → Phase) (hf : ContDiff ℝ ∞ f)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => weight f p.1 p.2) :=
  ((radius_contDiff f hf).sqrt (fun p => (radius_positive f hq p.1 p.2).ne')).inv
    (fun p => (Real.sqrt_pos.mpr (radius_positive f hq p.1 p.2)).ne')

lemma weight_positive (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u) (t : ℝ) (u : Plane) : 0 < weight f t u :=
  inv_pos.mpr (Real.sqrt_pos.mpr (radius_positive f hq t u))

lemma contraction_contDiff (f : Plane → Phase) (hf : ContDiff ℝ ∞ f)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u) :
    ContDiff ℝ ∞ (fun p : ℝ × Plane => contraction f p.1 p.2) := by
  have hraw : ContDiff ℝ ∞ (fun p : ℝ × Plane => fiberScale (1-p.1) (f p.2)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> change ContDiff ℝ ∞ _ <;> dsimp [fiberScale] <;> fun_prop
  exact (weight_contDiff f hf hq).smul hraw


lemma contraction_sphere (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u) (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    contraction f t u ∈ unitThreeSphere := by
  have hu' : planeNormSq u=1 := hu
  have hr := radius_positive f hq t u
  have he : zNormSq (contraction f t u)+wNormSq (contraction f t u)=
      (weight f t u)^2*radius f t u := by
    simp [contraction,zNormSq,wNormSq,radius,hu']
    ring
  change zNormSq (contraction f t u)+wNormSq (contraction f t u)=1
  rw [he]
  simp only [weight,inv_pow,Real.sq_sqrt hr.le,inv_mul_cancel₀ hr.ne']

lemma contraction_start (f : Plane → Phase) (hsphere : ∀ u ∈ unitCircle, f u ∈ unitThreeSphere)
    (u : Plane) (hu : u ∈ unitCircle) : contraction f 0 u=f u := by
  have hu' : planeNormSq u=1 := hu
  have hs : (f u 0)^2+(f u 1)^2+((f u 2)^2+(f u 3)^2)=1 := hsphere u hu
  have hr : radius f 0 u=1 := by simpa [radius,hu'] using hs
  ext i
  fin_cases i <;> simp [contraction,weight,hr]

lemma contraction_q (f : Plane → Phase)
    (hdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    qMap (contraction f t u)=(weight f t u*radialCoefficient f u) • u := by
  have hp := radial_projection (f u) u hu (hdet u hu)
  change qMap (f u)=radialCoefficient f u • u at hp
  unfold contraction
  rw [map_smul]
  have hf : qMap (fiberScale (1-t) (f u))=qMap (f u) := by ext i; fin_cases i <;> simp
  rw [hf,hp,smul_smul]

lemma contraction_recover (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u)
    (hdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) : recover (contraction f t u)=u :=
  recover_scaled _ u hu _ (mul_pos (weight_positive f hq t u) (hq u hu)) (contraction_q f hdet t u hu)

lemma contraction_finish (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u)
    (hdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0)
    (u : Plane) (hu : u ∈ unitCircle) : contraction f 1 u=core u := by
  let a := radialCoefficient f u
  have ha : 0 < a := hq u hu
  have hp := radial_projection (f u) u hu (hdet u hu)
  have h0 : f u 0=a*u 0 := congrFun hp 0
  have h1 : f u 1=a*u 1 := congrFun hp 1
  have hu' : planeNormSq u=1 := hu
  have hs : u 0^2+u 1^2=1 := hu
  have hr : radius f 1 u=a^2 := by
    simp [radius,hu',h0,h1]
    nlinarith [congrArg (fun z : ℝ => a^2*z) hs]
  ext i
  fin_cases i <;> simp [contraction,weight,hr,Real.sqrt_sq ha.le,core,h0,h1,ha.ne']

lemma contraction_odd (f : Plane → Phase)
    (hodd : ∀ u ∈ unitCircle, f (-u)= -f u)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) : contraction f t (-u)= -contraction f t u := by
  have he : radius f t (-u)=radius f t u := by simp [radius,hodd u hu,planeNormSq]
  simp only [contraction,weight,he,hodd u hu,map_neg,smul_neg]

lemma contraction_injOn (f : Plane → Phase)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u)
    (hdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0) (t : ℝ) :
    InjOn (contraction f t) unitCircle := by
  intro u hu v hv he
  have hh := congrArg recover he
  simpa only [contraction_recover f hq hdet t u hu,contraction_recover f hq hdet t v hv] using hh

lemma contraction_derivative_ne (f : Plane → Phase) (hf : ContDiff ℝ ∞ f)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u)
    (hdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (contraction f t) u (circleTangent u) ≠ 0 := by
  have hk : ContDiff ℝ ∞ (contraction f t) :=
    (contraction_contDiff f hf hq).comp (contDiff_const.prodMk contDiff_id)
  have hn : 0 < planeNormSq (qMap (contraction f t u)) := by
    rw [contraction_q f hdet t u hu]
    have ha := mul_pos (weight_positive f hq t u) (hq u hu)
    have hs : u 0^2+u 1^2=1 := hu
    dsimp [planeNormSq]
    nlinarith [congrArg (fun z : ℝ => (weight f t u*radialCoefficient f u)^2*z) hs,
      sq_pos_of_pos ha]
  have hR := recover_contDiffAt (contraction f t u) hn
  have hh := fderiv_circle_tangent_eq (recover ∘ contraction f t) id u hu
    ((hR.differentiableAt (by simp)).comp u (hk.differentiable (by simp) u))
    differentiableAt_id (fun v hv => contraction_recover f hq hdet t v hv)
  rw [fderiv_comp u (hR.differentiableAt (by simp)) (hk.differentiable (by simp) u)] at hh
  intro hz
  have hJ : circleTangent u=0 := by simpa [hz] using hh.symm
  have h0 : u 0=0 := by simpa [circleTangent] using congrFun hJ 1
  have h1 : u 1=0 := by simpa [circleTangent] using congrFun hJ 0
  have hs : u 0^2+u 1^2=1 := hu
  simp [h0,h1] at hs

lemma contraction_contact (f : Plane → Phase) (hf : ContDiff ℝ ∞ f)
    (hq : ∀ u ∈ unitCircle, 0 < radialCoefficient f u)
    (hc : ∀ u ∈ unitCircle, phaseRadialContact (f u) (fderiv ℝ f u (circleTangent u))=0)
    (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    phaseRadialContact (contraction f t u) (fderiv ℝ (contraction f t) u (circleTangent u))=0 := by
  have hw : ContDiff ℝ ∞ (weight f t) :=
    (weight_contDiff f hf hq).comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ (fun v => fiberScale (1-t) (f v)) := (fiberScale (1-t)).contDiff.comp hf
  have hd := (hw.differentiable (by simp) u).hasFDerivAt.smul
    (hg.differentiable (by simp) u).hasFDerivAt
  change HasFDerivAt (contraction f t) _ u at hd
  rw [hd.fderiv]
  change phaseRadialContact (weight f t u • fiberScale (1-t) (f u))
    (weight f t u • fderiv ℝ (fun v => fiberScale (1-t) (f v)) u (circleTangent u)+
      fderiv ℝ (weight f t) u (circleTangent u) • fiberScale (1-t) (f u))=0
  rw [contact_scaled]
  have he : fderiv ℝ (fun v => fiberScale (1-t) (f v)) u =
      (fiberScale (1-t)).comp (fderiv ℝ f u) :=
    ((fiberScale (1-t)).hasFDerivAt.comp u (hf.differentiable (by simp) u).hasFDerivAt).fderiv
  rw [he]
  change (weight f t u)^2*phaseRadialContact (fiberScale (1-t) (f u))
    (fiberScale (1-t) (fderiv ℝ f u (circleTangent u)))=0
  rw [fiberScale_contact,hc u hu,mul_zero,mul_zero]



end
end ContactTopology.CoreProjection


open BirkhoffGlobalSection Set Function
open scoped ContDiff


theorem solution
    (F : EquivariantSphereContactomorphism)
    (hq : ∀ u ∈ unitCircle,
      (F.toFun ![u 0,u 1,0,0]) 0*u 1-(F.toFun ![u 0,u 1,0,0]) 1*u 0=0 ∧
      0 < (F.toFun ![u 0,u 1,0,0]) 0*u 0+(F.toFun ![u 0,u 1,0,0]) 1*u 1) :
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = ![u 0,u 1,0,0])
 := by
  obtain ⟨C,R,r,N,hC,hr,hpos,hN,hDN,hSphere,hstart,hEmb,hInv,hpb,hRight,hDivide,hLeg⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let f : Plane → Phase := C ∘ ContactTopology.CoreProjection.planeIn
  have hf : ContDiff ℝ ∞ f := hC.comp ContactTopology.CoreProjection.planeIn.contDiff
  have hboundary (u : Plane) (hu : u ∈ unitCircle) : f u=F.toFun (ContactTopology.CoreProjection.core u) := by
    change C (ContactTopology.CoreProjection.planeIn u)=_
    rw [ContactTopology.CoreProjection.planeIn_apply,hstart]
    congr 1
    have hs : u 0^2+u 1^2=1 := hu
    have hd : 1+u 0^2+u 1^2=2 := by linarith
    ext i
    fin_cases i <;> simp [ContactTopology.CoreProjection.core,hd] <;> linarith
  have hqpos : ∀ u ∈ unitCircle, 0 < ContactTopology.CoreProjection.radialCoefficient f u := by
    intro u hu
    simpa only [ContactTopology.CoreProjection.radialCoefficient,hboundary u hu,
      ContactTopology.CoreProjection.core] using (hq u hu).2
  have hqdet : ∀ u ∈ unitCircle, f u 0*u 1-f u 1*u 0=0 := by
    intro u hu
    simpa only [hboundary u hu,ContactTopology.CoreProjection.core] using (hq u hu).1
  have hfsphere : ∀ u ∈ unitCircle, f u ∈ unitThreeSphere := fun u _ => hSphere _
  have hfodd : ∀ u ∈ unitCircle, f (-u)= -f u := by
    intro u hu
    have hn : -u ∈ unitCircle := by simpa [unitCircle,planeNormSq] using hu
    rw [hboundary (-u) hn,hboundary u hu,ContactTopology.CoreProjection.core_neg,
      F.antipodal _ (ContactTopology.CoreProjection.core_mem u hu)]
  have hfcontact : ∀ u ∈ unitCircle, phaseRadialContact (f u) (fderiv ℝ f u (circleTangent u))=0 := by
    intro u hu
    rw [show fderiv ℝ f u = _ from fderiv_comp u (hC.differentiable (by simp) _)
      ContactTopology.CoreProjection.planeIn.differentiableAt]
    rw [ContinuousLinearMap.fderiv]
    change phaseRadialContact (C (ContactTopology.CoreProjection.planeIn u))
      (fderiv ℝ C (ContactTopology.CoreProjection.planeIn u)
        (ContactTopology.CoreProjection.planeIn (circleTangent u)))=0
    simpa [circleTangent] using hLeg u hu
  let k : ℝ × Plane → Phase := fun p => ContactTopology.CoreProjection.contraction f p.1 p.2
  have hk : ContDiff ℝ ∞ k := ContactTopology.CoreProjection.contraction_contDiff f hf hqpos
  have hslice (t : ℝ) (u : Plane) :
      fderiv ℝ k (t,u) (0,circleTangent u) =
        fderiv ℝ (ContactTopology.CoreProjection.contraction f t) u (circleTangent u) := by
    have hd := (hk.differentiable (by simp) (t,u)).hasFDerivAt.comp u
      ((hasFDerivAt_const (𝕜 := ℝ) t u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u))
    exact (congrArg (fun D : Plane →L[ℝ] Phase => D (circleTangent u)) hd.fderiv).symm
  refine ⟨k,hk,fun t u hu => ContactTopology.CoreProjection.contraction_sphere f hqpos t u hu,?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨t,u⟩ htu ⟨s,v⟩ hsv he
    have ht : t=s := congrArg Prod.fst he
    have hv : k (t,u)=k (s,v) := congrArg Prod.snd he
    apply Prod.ext ht
    apply ContactTopology.CoreProjection.contraction_injOn f hqpos hqdet t htu.2 hsv.2
    simpa only [← ht] using hv
  · rintro ⟨t,u⟩ htu
    rw [hslice]
    exact ContactTopology.CoreProjection.contraction_derivative_ne f hf hqpos hqdet t u htu.2
  · intro t u hu
    rw [hslice]
    exact ContactTopology.CoreProjection.contraction_contact f hf hqpos hfcontact t u hu
  · intro t u hu
    exact ContactTopology.CoreProjection.contraction_odd f hfodd t u hu
  · intro u hu
    change ContactTopology.CoreProjection.contraction f 0 u=_
    rw [ContactTopology.CoreProjection.contraction_start f hfsphere u hu,hboundary u hu]
    rfl
  · intro u hu
    exact ContactTopology.CoreProjection.contraction_finish f hqpos hqdet u hu
