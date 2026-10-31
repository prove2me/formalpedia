-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_orientation_reversal
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:47:46.303245+00:00
-- url     : https://prove2.me/submissions/3932f064-08de-430f-ba91-867516a2a857

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



def rotation (t : ℝ) : Phase →L[ℝ] Phase := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ),
    Real.cos (Real.pi*t) • ContinuousLinearMap.proj 1-Real.sin (Real.pi*t) • ContinuousLinearMap.proj 3,
    ContinuousLinearMap.proj 2,
    Real.sin (Real.pi*t) • ContinuousLinearMap.proj 1+Real.cos (Real.pi*t) • ContinuousLinearMap.proj 3]

@[simp] lemma rotation_apply (t : ℝ) (p : Phase) : rotation t p=
    ![p 0,Real.cos (Real.pi*t)*p 1-Real.sin (Real.pi*t)*p 3,p 2,
      Real.sin (Real.pi*t)*p 1+Real.cos (Real.pi*t)*p 3] := by
  ext i
  fin_cases i <;> simp [rotation]

lemma rotation_contDiff : ContDiff ℝ ∞ (fun p : ℝ × Phase => rotation p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> change ContDiff ℝ ∞ _ <;> dsimp [rotation] <;> fun_prop

lemma rotation_inverse (t : ℝ) (p : Phase) : rotation (-t) (rotation t p)=p := by
  have hs := Real.cos_sq_add_sin_sq (Real.pi*t)
  have he : Real.pi*(-t)= -(Real.pi*t) := by ring
  ext i
  fin_cases i <;> simp [he] <;> nlinarith [congrArg (fun z : ℝ => z*p 1) hs,
    congrArg (fun z : ℝ => z*p 3) hs]

lemma rotation_sphere (t : ℝ) (p : Phase) (hp : p ∈ unitThreeSphere) : rotation t p ∈ unitThreeSphere := by
  have hs := Real.cos_sq_add_sin_sq (Real.pi*t)
  have he : zNormSq (rotation t p)+wNormSq (rotation t p)=
      zNormSq p+wNormSq p := by
    simp [zNormSq,wNormSq]
    nlinarith [congrArg (fun z : ℝ => z*(p 1^2+p 3^2)) hs]
  exact he.trans hp

def rotatingCore (t : ℝ) : Plane →L[ℝ] Phase := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ),Real.cos (Real.pi*t) • ContinuousLinearMap.proj 1,
    0,Real.sin (Real.pi*t) • ContinuousLinearMap.proj 1]

lemma rotatingCore_eq (t : ℝ) (u : Plane) : rotatingCore t u=rotation t (core u) := by
  ext i
  fin_cases i <;> simp [rotatingCore,core]

lemma rotatingCore_tangent (t : ℝ) (u : Plane) :
    phaseDot (rotatingCore t u) (rotatingCore t (circleTangent u))=0 ∧
    phaseRadialContact (rotatingCore t u) (rotatingCore t (circleTangent u))=0 := by
  have hs := Real.cos_sq_add_sin_sq (Real.pi*t)
  constructor
  · simp [rotatingCore,phaseDot,circleTangent]
    nlinarith [congrArg (fun z : ℝ => z*(u 0*u 1)) hs]
  · simp [rotatingCore,phaseRadialContact,phaseSymplecticForm,circleTangent]
    ring

lemma global_core_extension (F : EquivariantSphereContactomorphism) :
    ∃ D : Plane → Phase, ContDiff ℝ ∞ D ∧ (∀ u, D u ∈ unitThreeSphere) ∧
      ∀ u ∈ unitCircle, D u=core u := by
  obtain ⟨C,R,r,N,hC,hr,hpos,hN,hDN,hSphere,hstart,hEmb,hInv,hpb,hRight,hDivide,hLeg⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let f : Plane → Phase := C ∘ planeIn
  have hf : ContDiff ℝ ∞ f := hC.comp planeIn.contDiff
  have hb (u : Plane) (hu : u ∈ unitCircle) : f u=F.toFun (core u) := by
    change C (planeIn u)=_
    rw [planeIn_apply,hstart]
    congr 1
    have hs : u 0^2+u 1^2=1 := hu
    have hd : 1+u 0^2+u 1^2=2 := by linarith
    ext i
    fin_cases i <;> simp [core,hd] <;> linarith
  let D : Plane → Phase := F.invFun ∘ f
  have hD : ContDiff ℝ ∞ D := by
    apply contDiff_iff_contDiffAt.mpr
    intro u
    exact (F.inv_smooth _ (hSphere _)).comp u hf.contDiffAt
  refine ⟨D,hD,fun u => F.inv_maps_sphere (hSphere _),?_⟩
  intro u hu
  change F.invFun (f u)=core u
  rw [hb u hu,F.left_inv _ (core_mem u hu)]

def reversalRecover (F : EquivariantSphereContactomorphism) (t : ℝ) (p : Phase) : Plane :=
  qMap (rotation (-t) (F.invFun p))

lemma reversalRecover_contDiffAt (F : EquivariantSphereContactomorphism) (t : ℝ)
    (p : Phase) (hp : p ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (reversalRecover F t) p :=
  qMap.contDiff.contDiffAt.comp p ((rotation (-t)).contDiff.contDiffAt.comp p (F.inv_smooth p hp))

lemma reversalRecover_value (F : EquivariantSphereContactomorphism) (t : ℝ)
    (u : Plane) (hu : u ∈ unitCircle) :
    reversalRecover F t (F.toFun (rotatingCore t u))=u := by
  change qMap (rotation (-t) (F.invFun (F.toFun (rotatingCore t u))))=u
  rw [F.left_inv _ (by rw [rotatingCore_eq]; exact rotation_sphere t _ (core_mem u hu)),
    rotatingCore_eq,rotation_inverse]
  ext i
  fin_cases i <;> simp [core]



end
end ContactTopology.CoreProjection


open BirkhoffGlobalSection Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false


theorem solution
    (F : EquivariantSphereContactomorphism) :
      ∃ k : ℝ × Plane → Phase, ContDiff ℝ ∞ k ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,u) ∈ unitThreeSphere) ∧
        InjOn (fun p : ℝ × Plane => (p.1,k p)) (Icc (0:ℝ) 1 ×ˢ unitCircle) ∧
        (∀ p ∈ (Icc (0:ℝ) 1 ×ˢ unitCircle), fderiv ℝ k p (0,circleTangent p.2) ≠ 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle,
          phaseRadialContact (k (t,u)) (fderiv ℝ k (t,u) (0,circleTangent u)) = 0) ∧
        (∀ t : ℝ, ∀ u ∈ unitCircle, k (t,-u) = -k (t,u)) ∧
        (∀ u ∈ unitCircle, k (0,u) = F.toFun ![u 0,u 1,0,0]) ∧
        (∀ u ∈ unitCircle, k (1,u) = F.toFun ![u 0,-u 1,0,0])
 := by
  obtain ⟨D,hD,hDsphere,hDboundary⟩ := ContactTopology.CoreProjection.global_core_extension F
  let S : ℝ × Plane → Phase := fun p => ContactTopology.CoreProjection.rotation p.1 (D p.2)
  have hS : ContDiff ℝ ∞ S := ContactTopology.CoreProjection.rotation_contDiff.comp
    (f := fun p : ℝ × Plane => (p.1,D p.2))
    (contDiff_fst.prodMk (hD.comp contDiff_snd))
  have hSphere (p : ℝ × Plane) : S p ∈ unitThreeSphere :=
    ContactTopology.CoreProjection.rotation_sphere p.1 _ (hDsphere p.2)
  let k : ℝ × Plane → Phase := F.toFun ∘ S
  have hk : ContDiff ℝ ∞ k := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact (F.smooth _ (hSphere p)).comp p hS.contDiffAt
  have hb (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
      k (t,u)=F.toFun (ContactTopology.CoreProjection.rotatingCore t u) := by
    change F.toFun (ContactTopology.CoreProjection.rotation t (D u))=_
    rw [hDboundary u hu,ContactTopology.CoreProjection.rotatingCore_eq]
  have hksphere (t : ℝ) (u : Plane) : k (t,u) ∈ unitThreeSphere := F.maps_sphere (hSphere (t,u))
  have hks (t : ℝ) : ContDiff ℝ ∞ (fun u => k (t,u)) := hk.comp (contDiff_const.prodMk contDiff_id)
  have hslice (t : ℝ) (u : Plane) : fderiv ℝ k (t,u) (0,circleTangent u)=
      fderiv ℝ (fun v => k (t,v)) u (circleTangent u) := by
    have hd := (hk.differentiable (by simp) (t,u)).hasFDerivAt.comp u
      ((hasFDerivAt_const (𝕜 := ℝ) t u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u))
    exact (congrArg (fun L : Plane →L[ℝ] Phase => L (circleTangent u)) hd.fderiv).symm
  have hRecover (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
      ContactTopology.CoreProjection.reversalRecover F t (k (t,u))=u := by
    rw [hb t u hu]
    exact ContactTopology.CoreProjection.reversalRecover_value F t u hu
  have hDer (t : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
      fderiv ℝ (fun v => k (t,v)) u (circleTangent u) ≠ 0 := by
    have hR := ContactTopology.CoreProjection.reversalRecover_contDiffAt F t _ (hksphere t u)
    have hh := ContactTopology.CoreProjection.fderiv_circle_tangent_eq
      (ContactTopology.CoreProjection.reversalRecover F t ∘ (fun v => k (t,v))) id u hu
      ((hR.differentiableAt (by simp)).comp u ((hks t).differentiable (by simp) u))
      differentiableAt_id (fun v hv => hRecover t v hv)
    rw [fderiv_comp u (hR.differentiableAt (by simp)) ((hks t).differentiable (by simp) u)] at hh
    intro hz
    have hJ : circleTangent u=0 := by simpa [hz] using hh.symm
    have h0 : u 0=0 := by simpa [circleTangent] using congrFun hJ 1
    have h1 : u 1=0 := by simpa [circleTangent] using congrFun hJ 0
    have hs : u 0^2+u 1^2=1 := hu
    simp [h0,h1] at hs
  refine ⟨k,hk,fun t u _ => hksphere t u,?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨t,u⟩ htu ⟨s,v⟩ hsv he
    have ht : t=s := congrArg Prod.fst he
    have hv : k (t,u)=k (s,v) := congrArg Prod.snd he
    apply Prod.ext ht
    have hh := congrArg (ContactTopology.CoreProjection.reversalRecover F t) hv
    simpa only [← ht,hRecover t u htu.2,hRecover t v hsv.2] using hh
  · rintro ⟨t,u⟩ htu
    rw [hslice]
    exact hDer t u htu.2
  · intro t u hu
    let E := ContactTopology.CoreProjection.rotatingCore t
    have he : E u ∈ unitThreeSphere := by
      rw [show E u = ContactTopology.CoreProjection.rotation t (ContactTopology.CoreProjection.core u) from
        ContactTopology.CoreProjection.rotatingCore_eq t u]
      exact ContactTopology.CoreProjection.rotation_sphere t _ (ContactTopology.CoreProjection.core_mem u hu)
    have hF := (F.smooth _ he).differentiableAt (by simp)
    have hfe := hF.comp u E.differentiableAt
    have hd := ContactTopology.CoreProjection.fderiv_circle_tangent_eq
      (fun v => k (t,v)) (F.toFun ∘ E) u hu ((hks t).differentiable (by simp) u) hfe
      (fun v hv => hb t v hv)
    rw [hslice,hd,fderiv_comp u hF E.differentiableAt,ContinuousLinearMap.fderiv]
    change phaseRadialContact (k (t,u)) (fderiv ℝ F.toFun (E u) (E (circleTangent u)))=0
    rw [hb t u hu]
    obtain ⟨a,ha,hcontact⟩ := F.contact _ he
    rw [hcontact _ (ContactTopology.CoreProjection.rotatingCore_tangent t u).1,
      (ContactTopology.CoreProjection.rotatingCore_tangent t u).2,mul_zero]
  · intro t u hu
    have hn : -u ∈ unitCircle := by simpa [unitCircle,planeNormSq] using hu
    rw [hb t (-u) hn,hb t u hu,map_neg]
    apply F.antipodal
    rw [ContactTopology.CoreProjection.rotatingCore_eq]
    exact ContactTopology.CoreProjection.rotation_sphere t _ (ContactTopology.CoreProjection.core_mem u hu)
  · intro u hu
    rw [hb 0 u hu]
    congr 1
    ext i
    fin_cases i <;> simp [ContactTopology.CoreProjection.rotatingCore]
  · intro u hu
    rw [hb 1 u hu]
    congr 1
    ext i
    fin_cases i <;> simp [ContactTopology.CoreProjection.rotatingCore]
