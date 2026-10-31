-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_relative_rational_numbers
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T18:54:16.293128+00:00
-- url     : https://prove2.me/submissions/1927577a-0c21-4b08-a427-d4cb3b8f5c11

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_ContactTopology_AntipodalSphereQuotients
import Definitions.Def_ContactTopology_RelativeRationalInvariants
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Hausdorff
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactCalculus_exterior_pairing_pullback


namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def disk (u : Plane) : Phase :=
  ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
    (1-planeNormSq u)/(1+planeNormSq u),0]

lemma denominator_pos (u : Plane) : 0 < 1+planeNormSq u := by
  dsimp [planeNormSq]
  nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]

lemma disk_contDiff : ContDiff ℝ ∞ disk := by
  have hn : ContDiff ℝ ∞ planeNormSq := by unfold planeNormSq; fun_prop
  have hi : ContDiff ℝ ∞ (fun u : Plane => (1+planeNormSq u)⁻¹) :=
    (contDiff_const.add hn).inv (fun u => (denominator_pos u).ne')
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [disk] <;> (try simp only [div_eq_mul_inv]) <;> fun_prop

lemma disk_sphere (u : Plane) : disk u ∈ unitThreeSphere := by
  have hd := (denominator_pos u).ne'
  change (2*u 0/(1+planeNormSq u))^2+(2*u 1/(1+planeNormSq u))^2+
    (((1-planeNormSq u)/(1+planeNormSq u))^2+0^2)=1
  field_simp [hd]
  dsimp [planeNormSq]
  ring

lemma disk_boundary (u : Plane) (hu : u ∈ unitCircle) : disk u=![u 0,u 1,0,0] := by
  change planeNormSq u=1 at hu
  ext i
  fin_cases i <;> simp [disk,hu] <;> ring

lemma disk_upper (u : Plane) (hu : planeNormSq u ≤ 1) : 0 ≤ disk u 2 := by
  exact div_nonneg (sub_nonneg.mpr hu) (denominator_pos u).le

lemma disk_upper_strict (u : Plane) (hu : planeNormSq u < 1) : 0 < disk u 2 :=
  div_pos (sub_pos.mpr hu) (denominator_pos u)

lemma disk_recovery_denominator (u : Plane) : 1+disk u 2=2/(1+planeNormSq u) := by
  change 1+(1-planeNormSq u)/(1+planeNormSq u)=_
  field_simp [(denominator_pos u).ne']
  ring

lemma disk_recovery (u : Plane) :
    ![disk u 0/(1+disk u 2),disk u 1/(1+disk u 2)]=u := by
  rw [disk_recovery_denominator]
  ext i
  fin_cases i <;> dsimp [disk] <;> field_simp [(denominator_pos u).ne'] <;> ring

def inverse (y : Phase) : Plane := ![y 0/(1+y 2),y 1/(1+y 2)]

lemma inverse_contDiffAt (u : Plane) : ContDiffAt ℝ ∞ inverse (disk u) := by
  have hd : 0 < 1+disk u 2 := by rw [disk_recovery_denominator]; exact div_pos (by norm_num) (denominator_pos u)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [inverse] <;>
    exact ((contDiff_apply ℝ ℝ _).contDiffAt).div
      ((contDiffAt_const.add (contDiff_apply ℝ ℝ 2).contDiffAt)) hd.ne'

lemma disk_injective : Injective disk := by
  intro u v he
  have hh := congrArg inverse he
  simpa only [inverse,disk_recovery] using hh

lemma disk_derivative_injective (u : Plane) : Injective (fderiv ℝ disk u) := by
  have heq : inverse ∘ disk=id := funext disk_recovery
  have hd := congrArg (fun f : Plane → Plane => fderiv ℝ f u) heq
  rw [fderiv_comp u ((inverse_contDiffAt u).differentiableAt (by simp)) (disk_contDiff.differentiable (by simp) u)] at hd
  intro v w he
  have hh := congrArg (fderiv ℝ inverse (disk u)) he
  have he' := congrArg (fun L : Plane →L[ℝ] Plane => L v) hd
  have he'' := congrArg (fun L : Plane →L[ℝ] Plane => L w) hd
  simpa using he'.symm.trans (hh.trans he'')

lemma disk_antipodal_fibers (u v : Plane) (hu : planeNormSq u ≤ 1) (hv : planeNormSq v ≤ 1) :
    disk u= -disk v ↔ planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v := by
  constructor
  · intro he
    have hz := congrFun he 2
    change disk u 2= -disk v 2 at hz
    have hzu : disk u 2=0 := by linarith [disk_upper u hu,disk_upper v hv]
    have hzv : disk v 2=0 := by linarith [disk_upper u hu,disk_upper v hv]
    have hnu : planeNormSq u=1 := by
      have hn := (div_eq_iff (denominator_pos u).ne').mp hzu
      linarith
    have hnv : planeNormSq v=1 := by
      have hn := (div_eq_iff (denominator_pos v).ne').mp hzv
      linarith
    refine ⟨hnu,hnv,?_⟩
    rw [disk_boundary u hnu,disk_boundary v hnv] at he
    ext i
    fin_cases i
    · exact congrFun he 0
    · exact congrFun he 1
  · rintro ⟨hnu,hnv,he⟩
    rw [disk_boundary u hnu,disk_boundary v hnv,he]
    ext i
    fin_cases i <;> simp

def imageDisk (F : EquivariantSphereContactomorphism) : Plane → Phase := F.toFun ∘ disk

lemma imageDisk_contDiff (F : EquivariantSphereContactomorphism) : ContDiff ℝ ∞ (imageDisk F) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  exact (F.smooth _ (disk_sphere u)).comp u disk_contDiff.contDiffAt

lemma imageDisk_injective (F : EquivariantSphereContactomorphism) : Injective (imageDisk F) := by
  intro u v he
  apply disk_injective
  have hh := congrArg F.invFun he
  simpa only [imageDisk,Function.comp_apply,F.left_inv _ (disk_sphere u),F.left_inv _ (disk_sphere v)] using hh

lemma imageDisk_boundary (F : EquivariantSphereContactomorphism) (u : Plane) (hu : u ∈ unitCircle) :
    imageDisk F u=F.toFun ![u 0,u 1,0,0] := by
  change F.toFun (disk u)=_
  rw [disk_boundary u hu]

lemma imageDisk_sphere (F : EquivariantSphereContactomorphism) (u : Plane) :
    imageDisk F u ∈ unitThreeSphere := F.maps_sphere (disk_sphere u)

lemma imageDisk_derivative_injective (F : EquivariantSphereContactomorphism) (u : Plane) :
    Injective (fderiv ℝ (imageDisk F) u) := by
  have heq : F.invFun ∘ imageDisk F=disk := funext (fun v => F.left_inv _ (disk_sphere v))
  have hd := congrArg (fun f : Plane → Phase => fderiv ℝ f u) heq
  rw [fderiv_comp u ((F.inv_smooth _ (imageDisk_sphere F u)).differentiableAt (by simp))
    ((imageDisk_contDiff F).differentiable (by simp) u)] at hd
  intro v w hvw
  apply disk_derivative_injective u
  rw [← hd]
  change fderiv ℝ F.invFun (imageDisk F u) (fderiv ℝ (imageDisk F) u v)=
    fderiv ℝ F.invFun (imageDisk F u) (fderiv ℝ (imageDisk F) u w)
  rw [hvw]

lemma imageDisk_antipodal_fibers (F : EquivariantSphereContactomorphism)
    (u v : Plane) (hu : planeNormSq u ≤ 1) (hv : planeNormSq v ≤ 1) :
    imageDisk F u= -imageDisk F v ↔ planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v := by
  constructor
  · intro he
    apply (disk_antipodal_fibers u v hu hv).mp
    have hneg : -disk v ∈ unitThreeSphere := by
      simpa [unitThreeSphere,zNormSq,wNormSq] using disk_sphere v
    have hh := congrArg F.invFun he
    change F.invFun (F.toFun (disk u))=F.invFun (-F.toFun (disk v)) at hh
    rw [F.left_inv _ (disk_sphere u),← F.antipodal _ (disk_sphere v),F.left_inv _ hneg] at hh
    exact hh
  · intro h
    have hh := (disk_antipodal_fibers u v hu hv).mpr h
    change F.toFun (disk u)= -F.toFun (disk v)
    rw [hh,F.antipodal _ (disk_sphere v)]

end
end ContactTopology.CoreDisk

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection
lemma normalize_unit {y : Phase} (hy : y ∈ unitThreeSphere) : radialNormalize y = y := by
  change zNormSq y+wNormSq y = 1 at hy
  simp [radialNormalize,hy]
end BirkhoffGlobalSection.HopfTransport

namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

lemma sphere_dot_self {y : Phase} (hy : y ∈ unitThreeSphere) : phaseDot y y = 1 := by
  change zNormSq y + wNormSq y = 1 at hy
  simp [zNormSq,wNormSq,phaseDot] at hy ⊢
  nlinarith

lemma dot_hasDerivAt {q g : ℝ → Phase} {v b : Phase} {t : ℝ}
    (hq : HasDerivAt q v t) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => phaseDot (q s) (g s)) (phaseDot v (g t) + phaseDot (q t) b) t := by
  have h := fun i => hasDerivAt_pi.mp hq i
  have k := fun i => hasDerivAt_pi.mp hg i
  have hd := ((((h 0).mul (k 0)).add ((h 1).mul (k 1))).add ((h 2).mul (k 2))).add ((h 3).mul (k 3))
  apply hd.congr_deriv
  simp only [phaseDot]
  ring

lemma dot_self_hasDerivAt {q : ℝ → Phase} {v : Phase} {t : ℝ} (hq : HasDerivAt q v t) :
    HasDerivAt (fun s => phaseDot (q s) (q s)) (2 * phaseDot (q t) v) t := by
  apply (dot_hasDerivAt hq hq).congr_deriv
  simp [phaseDot]
  ring

lemma sphere_line_norm_positive (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) (s : ℝ) :
    0 < zNormSq (y+s•v) + wNormSq (y+s•v) := by
  have hy' := sphere_dot_self hy
  have hvv : 0 ≤ phaseDot v v := by
    simp only [phaseDot]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2),sq_nonneg (v 3)]
  have he : zNormSq (y+s•v) + wNormSq (y+s•v) = 1 + s^2 * phaseDot v v := by
    simp [zNormSq,wNormSq,phaseDot] at hy' hv ⊢
    linear_combination hy' + (2*s)*hv
  rw [he]
  nlinarith [sq_nonneg s,mul_nonneg (sq_nonneg s) hvv]

lemma sphere_curve_hasDerivAt (y v : Phase) (hy : y ∈ unitThreeSphere)
    (hv : phaseDot y v = 0) :
    HasDerivAt (fun s : ℝ => radialNormalize (y+s•v)) v 0 := by
  have hc : HasDerivAt (fun s : ℝ => y+s•v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> simp
  have hq : HasDerivAt (fun s : ℝ => zNormSq (y+s•v)+wNormSq (y+s•v)) 0 0 := by
    convert! dot_self_hasDerivAt hc using 1
    · ext s
      simp [zNormSq,wNormSq,phaseDot,pow_two,add_assoc]
    · simp [hv]
  have hQ : zNormSq y + wNormSq y = 1 := hy
  have hs := hq.sqrt (by simp [hQ])
  have hi := hs.inv (by simp [hQ])
  have hd := hi.smul hc
  convert! hd using 1 <;> simp [radialNormalize,hQ]

lemma sphere_tangent_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f g : Phase → E) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (heq : EqOn f g unitThreeSphere) : fderiv ℝ f y v = fderiv ℝ g y v := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hgy : DifferentiableAt ℝ g (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hg
  have hdf := hfy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hdg := hgy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hfun : f ∘ (fun s : ℝ => radialNormalize (y+s•v)) = g ∘ (fun s : ℝ => radialNormalize (y+s•v)) := by
    funext s
    exact heq (x := radialNormalize (y+s•v))
      (radial_normalization_contact_identity _ (sphere_line_norm_positive y v hy hv s)).2.1
  rw [hfun] at hdf
  have he := hdf.unique hdg
  simpa [normalize_unit hy] using he

lemma sphere_map_fderiv_tangent (f : Phase → Phase) (y v : Phase)
    (hy : y ∈ unitThreeSphere) (hv : phaseDot y v = 0)
    (hf : DifferentiableAt ℝ f y) (hmap : MapsTo f unitThreeSphere unitThreeSphere) :
    phaseDot (f y) (fderiv ℝ f y v) = 0 := by
  have hc := sphere_curve_hasDerivAt y v hy hv
  have hfy : DifferentiableAt ℝ f (radialNormalize (y+(0:ℝ)•v)) := by simpa [normalize_unit hy] using hf
  have hd := dot_self_hasDerivAt (hfy.hasFDerivAt.comp_hasDerivAt 0 hc)
  have heq : (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) = fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self (hmap (radial_normalization_contact_identity _
      (sphere_line_norm_positive y v hy hv s)).2.1)
  change HasDerivAt (fun s : ℝ => phaseDot (f (radialNormalize (y+s•v))) (f (radialNormalize (y+s•v)))) _ 0 at hd
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp [normalize_unit hy] at he
  linarith

end
end BirkhoffGlobalSection.HopfTransport

namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def frameA (y : Phase) : Phase := ![-y 1,y 0,y 3,-y 2]
def frameB (y : Phase) : Phase := ![y 3,-y 2,y 1,-y 0]

lemma frameA_contDiff : ContDiff ℝ ∞ frameA := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [frameA] <;> fun_prop
lemma frameB_contDiff : ContDiff ℝ ∞ frameB := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [frameB] <;> fun_prop

lemma frame_identities (y : Phase) :
    phaseDot y (frameA y)=0 ∧ phaseDot y (frameB y)=0 ∧
    phaseRadialContact y (frameA y)=0 ∧ phaseRadialContact y (frameB y)=0 ∧
    phaseDot (frameA y) (frameA y)=phaseDot y y ∧
    phaseDot (frameB y) (frameB y)=phaseDot y y ∧
    phaseDot (frameA y) (frameB y)=0 ∧
    2*phaseRadialContact (frameA y) (frameB y)=phaseDot y y := by
  dsimp [frameA,frameB,phaseDot,phaseRadialContact,phaseSymplecticForm]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> ring

lemma frame_reconstruction (y v : Phase) :
    phaseDot y y • v = phaseDot y v • y+
      phaseDot (frameA y) v • frameA y+phaseDot (frameB y) v • frameB y+
      (2*phaseRadialContact y v) • ![y 2,y 3,-y 0,-y 1] := by
  ext i
  fin_cases i <;> simp [frameA,frameB,phaseDot,phaseRadialContact,phaseSymplecticForm,
    Matrix.vecHead,Matrix.vecTail] <;> ring

lemma contact_frame_spans (y v : Phase) (hy : y ∈ unitThreeSphere)
    (ht : phaseDot y v=0) (hc : phaseRadialContact y v=0) :
    v=phaseDot (frameA y) v • frameA y+phaseDot (frameB y) v • frameB y := by
  simpa only [sphere_dot_self hy,ht,hc,mul_zero,zero_smul,one_smul,zero_add,add_zero]
    using frame_reconstruction y v

lemma contact_frame_independent (y : Phase) (hy : y ∈ unitThreeSphere)
    (a b : ℝ) (h : a • frameA y+b • frameB y=0) : a=0 ∧ b=0 := by
  have hs := sphere_dot_self hy
  have hh : a^2+b^2=0 := by
    have he := congrArg (fun z => phaseDot z z) h
    have halg : phaseDot (a • frameA y+b • frameB y) (a • frameA y+b • frameB y)=
        (a^2+b^2)*phaseDot y y := by
      simp [frameA,frameB,phaseDot]
      ring
    rw [halg,hs] at he
    simpa [phaseDot] using he
  constructor <;> nlinarith [sq_nonneg a,sq_nonneg b]

lemma sphere_derivative_left_inverse (F : EquivariantSphereContactomorphism)
    (y v : Phase) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v=0) :
    fderiv ℝ F.invFun (F.toFun y) (fderiv ℝ F.toFun y v)=v := by
  have hf := (F.smooth y hy).differentiableAt (by simp)
  have hi := (F.inv_smooth _ (F.maps_sphere hy)).differentiableAt (by simp)
  have he := sphere_tangent_fderiv_eq (F.invFun ∘ F.toFun) id y v hy hv
    (hi.comp y hf) differentiableAt_id F.left_inv
  rw [fderiv_comp y hi hf] at he
  simpa using he

def pushVector (F : EquivariantSphereContactomorphism) (y v : Phase) : Phase :=
  fderiv ℝ F.toFun y v

lemma pushVector_smooth (F : EquivariantSphereContactomorphism)
    (V : Phase → Phase) (hV : ContDiff ℝ ∞ V) :
    ContDiff ℝ ∞ (fun u : Plane => pushVector F (disk u) (V (disk u))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  exact (((F.smooth _ (disk_sphere u)).fderiv_right (by simp)).comp u
    disk_contDiff.contDiffAt).clm_apply ((hV.comp disk_contDiff).contDiffAt)

lemma pushed_frame_contact (F : EquivariantSphereContactomorphism) (y : Phase)
    (hy : y ∈ unitThreeSphere) :
    phaseDot (F.toFun y) (pushVector F y (frameA y))=0 ∧
    phaseDot (F.toFun y) (pushVector F y (frameB y))=0 ∧
    phaseRadialContact (F.toFun y) (pushVector F y (frameA y))=0 ∧
    phaseRadialContact (F.toFun y) (pushVector F y (frameB y))=0 := by
  obtain ⟨a,ha,hF⟩ := F.contact y hy
  have hh := frame_identities y
  refine ⟨sphere_map_fderiv_tangent F.toFun y _ hy hh.1
    ((F.smooth y hy).differentiableAt (by simp)) F.maps_sphere,
    sphere_map_fderiv_tangent F.toFun y _ hy hh.2.1
    ((F.smooth y hy).differentiableAt (by simp)) F.maps_sphere,?_,?_⟩
  · change phaseRadialContact _ (fderiv ℝ F.toFun y _)=0
    rw [hF _ hh.1,hh.2.2.1,mul_zero]
  · change phaseRadialContact _ (fderiv ℝ F.toFun y _)=0
    rw [hF _ hh.2.1,hh.2.2.2.1,mul_zero]

lemma pushed_frame_independent (F : EquivariantSphereContactomorphism)
    (y : Phase) (hy : y ∈ unitThreeSphere) (a b : ℝ)
    (h : a • pushVector F y (frameA y)+b • pushVector F y (frameB y)=0) :
    a=0 ∧ b=0 := by
  apply contact_frame_independent y hy a b
  have hh := congrArg (fderiv ℝ F.invFun (F.toFun y)) h
  simp only [map_add,map_smul,map_zero,pushVector] at hh
  rw [sphere_derivative_left_inverse F y _ hy (frame_identities y).1,
    sphere_derivative_left_inverse F y _ hy (frame_identities y).2.1] at hh
  exact hh

def boundaryCore (u : Plane) : Phase := ![u 0,u 1,0,0]
def boundaryTangent (u : Plane) : Phase := ![-u 1,u 0,0,0]
def inwardNormal : Phase := ![0,0,1,0]
def secondNormal : Phase := ![0,0,0,-1]

lemma disk_fderiv_boundary (u v : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ disk u v=
      ![v 0-u 0*(u 0*v 0+u 1*v 1),v 1-u 1*(u 0*v 0+u 1*v 1),
        -(u 0*v 0+u 1*v 1),0] := by
  have h0 := (ContinuousLinearMap.proj (0:Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h1 := (ContinuousLinearMap.proj (1:Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := u)
  have hn := (h0.pow 2).add (h1.pow 2)
  change HasFDerivAt planeNormSq _ u at hn
  have hi := (hasFDerivAt_inv (denominator_pos u).ne').comp u ((hasFDerivAt_const (1:ℝ) u).add hn)
  have d0 := ((h0.const_mul 2).mul hi).fderiv
  have d1 := ((h1.const_mul 2).mul hi).fderiv
  have d2 := (((hasFDerivAt_const (1:ℝ) u).sub hn).mul hi).fderiv
  change fderiv ℝ (fun w : Plane => (2*w 0)*(1+planeNormSq w)⁻¹) u=_ at d0
  change fderiv ℝ (fun w : Plane => (2*w 1)*(1+planeNormSq w)⁻¹) u=_ at d1
  change fderiv ℝ (fun w : Plane => (1-planeNormSq w)*(1+planeNormSq w)⁻¹) u=_ at d2
  change planeNormSq u=1 at hu
  have hd := disk_contDiff.differentiable (by simp) u
  ext i
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L v) (fderiv_apply hd i)
  change fderiv ℝ (fun w => disk w i) u v=fderiv ℝ disk u v i at he
  fin_cases i
  · change _ = v 0-u 0*(u 0*v 0+u 1*v 1)
    rw [← he]
    change fderiv ℝ (fun w : Plane => (2*w 0)*(1+planeNormSq w)⁻¹) u v=_
    rw [d0]
    simp [hu]
    ring
  · change _ = v 1-u 1*(u 0*v 0+u 1*v 1)
    rw [← he]
    change fderiv ℝ (fun w : Plane => (2*w 1)*(1+planeNormSq w)⁻¹) u v=_
    rw [d1]
    simp [hu]
    ring
  · change _ = -(u 0*v 0+u 1*v 1)
    rw [← he]
    change fderiv ℝ (fun w : Plane => (1-planeNormSq w)*(1+planeNormSq w)⁻¹) u v=_
    rw [d2]
    simp [hu]
    ring
  · change _ = 0
    rw [← he]
    change fderiv ℝ (fun _ : Plane => (0:ℝ)) u v=0
    simp

lemma disk_boundary_tangent (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ disk u (circleTangent u)=boundaryTangent u := by
  rw [disk_fderiv_boundary u _ hu]
  ext i
  fin_cases i <;> simp only [circleTangent,boundaryTangent,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.vecHead,Matrix.vecTail] <;> ring

lemma disk_inward_normal (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ disk u (-u)=inwardNormal := by
  rw [disk_fderiv_boundary u _ hu]
  have hs : u 0^2+u 1^2=1 := hu
  have hd : u 0*(-u 0)+u 1*(-u 1)= -1 := by nlinarith
  change ![-u 0-u 0*(u 0*(-u 0)+u 1*(-u 1)),
    -u 1-u 1*(u 0*(-u 0)+u 1*(-u 1)),
    -(u 0*(-u 0)+u 1*(-u 1)),0]=inwardNormal
  rw [hd]
  ext i
  fin_cases i <;> simp [inwardNormal]

lemma boundary_frame_values (u : Plane) :
    frameA (boundaryCore u)=boundaryTangent u ∧
    frameB (boundaryCore u)=u 1 • inwardNormal+u 0 • secondNormal := by
  constructor <;> ext i <;> fin_cases i <;>
    simp [frameA,frameB,boundaryCore,boundaryTangent,inwardNormal,secondNormal]

lemma boundary_normal_frame_independent (u : Plane) (hu : u ∈ unitCircle)
    (a b d : ℝ) (h : a • boundaryTangent u+b • inwardNormal+d • secondNormal=0) :
    a=0 ∧ b=0 ∧ d=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  dsimp [boundaryTangent,inwardNormal,secondNormal] at h0 h1 h2 h3
  simp only [mul_zero,mul_one,mul_neg,zero_add,add_zero] at h0 h1 h2 h3
  have hs : u 0^2+u 1^2=1 := hu
  refine ⟨?_,h2,by linarith⟩
  have ha : a*(u 0^2+u 1^2)=0 := by
    linear_combination (u 0)*h1-(u 1)*h0
  simpa [hs] using ha

def contactVolume (y v w z : Phase) : ℝ :=
  2*(phaseRadialContact y v*phaseRadialContact w z-
    phaseRadialContact y w*phaseRadialContact v z+
    phaseRadialContact y z*phaseRadialContact v w)

lemma boundary_normal_frame_positive (u : Plane) (hu : u ∈ unitCircle) :
    contactVolume (boundaryCore u) (boundaryTangent u) inwardNormal secondNormal=1/2 := by
  have hs : u 0^2+u 1^2=1 := hu
  have he : contactVolume (boundaryCore u) (boundaryTangent u) inwardNormal secondNormal=
      (u 0^2+u 1^2)/2 := by
    simp [contactVolume,boundaryCore,boundaryTangent,inwardNormal,secondNormal,
      phaseRadialContact,phaseSymplecticForm]
    ring
  rw [he,hs]

def circlePoint (t : ℝ) : Plane := ![Real.cos t,Real.sin t]
def twistAngle (t : ℝ) : ℝ := Real.pi/2-t

lemma circlePoint_mem (t : ℝ) : circlePoint t ∈ unitCircle := by
  change Real.cos t^2+Real.sin t^2=1
  nlinarith [Real.sin_sq_add_cos_sq t]

lemma contact_normal_twist (t : ℝ) :
    frameB (boundaryCore (circlePoint t))=
      Real.cos (twistAngle t) • inwardNormal+Real.sin (twistAngle t) • secondNormal := by
  rw [(boundary_frame_values _).2]
  simp [circlePoint,twistAngle,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]

lemma twistAngle_endpoint : twistAngle (2*Real.pi)-twistAngle 0= -2*Real.pi := by
  unfold twistAngle
  ring

lemma pushed_boundary_tangent (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (imageDisk F) u (circleTangent u)=
      pushVector F (disk u) (frameA (disk u)) := by
  have hd := fderiv_comp u ((F.smooth _ (disk_sphere u)).differentiableAt (by simp))
    (disk_contDiff.differentiable (by simp) u)
  change fderiv ℝ (F.toFun ∘ disk) u _=_
  rw [hd]
  change pushVector F (disk u) (fderiv ℝ disk u (circleTangent u))=_
  rw [disk_boundary_tangent u hu,disk_boundary u hu]
  exact congrArg (pushVector F (boundaryCore u)) (boundary_frame_values u).1.symm

lemma pushed_disk_inward_normal (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (imageDisk F) u (-u)=pushVector F (disk u) inwardNormal := by
  have hd := fderiv_comp u ((F.smooth _ (disk_sphere u)).differentiableAt (by simp))
    (disk_contDiff.differentiable (by simp) u)
  change fderiv ℝ (F.toFun ∘ disk) u _=_
  rw [hd]
  change pushVector F (disk u) (fderiv ℝ disk u (-u))=_
  rw [disk_inward_normal u hu]

lemma pushed_contact_frame_spans (F : EquivariantSphereContactomorphism)
    (y w : Phase) (hy : y ∈ unitThreeSphere)
    (ht : phaseDot (F.toFun y) w=0) (hc : phaseRadialContact (F.toFun y) w=0) :
    ∃ a b : ℝ, w=a • pushVector F y (frameA y)+b • pushVector F y (frameB y) := by
  let v := fderiv ℝ F.invFun (F.toFun y) w
  have hi := (F.inv_smooth _ (F.maps_sphere hy)).differentiableAt (by simp)
  have hf := (F.smooth y hy).differentiableAt (by simp)
  have hv : phaseDot y v=0 := by
    have hh := sphere_map_fderiv_tangent F.invFun (F.toFun y) w
      (F.maps_sphere hy) ht hi F.inv_maps_sphere
    simpa only [F.left_inv y hy] using hh
  have hback : pushVector F y v=w := by
    have hf' : DifferentiableAt ℝ F.toFun (F.invFun (F.toFun y)) := by
      simpa only [F.left_inv y hy] using hf
    have hh := sphere_tangent_fderiv_eq (F.toFun ∘ F.invFun) id (F.toFun y) w
      (F.maps_sphere hy) ht (hf'.comp _ hi) differentiableAt_id F.right_inv
    rw [fderiv_comp _ hf' hi,F.left_inv y hy] at hh
    simpa only [fderiv_id,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,pushVector,v] using hh
  obtain ⟨a,ha,hF⟩ := F.contact y hy
  have hvC : phaseRadialContact y v=0 := by
    have hh := hF v hv
    change phaseRadialContact (F.toFun y) (pushVector F y v)=_ at hh
    rw [hback,hc] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left ha.ne'
  have hrep := contact_frame_spans y v hy hv hvC
  refine ⟨phaseDot (frameA y) v,phaseDot (frameB y) v,?_⟩
  rw [← hback]
  change fderiv ℝ F.toFun y v=_
  conv_lhs => rw [hrep]
  rw [map_add,map_smul,map_smul]
  rfl

lemma pushed_contact_normal_twist (F : EquivariantSphereContactomorphism) (t : ℝ) :
    pushVector F (disk (circlePoint t)) (frameB (disk (circlePoint t)))=
      Real.cos (twistAngle t) • pushVector F (disk (circlePoint t)) inwardNormal+
      Real.sin (twistAngle t) • pushVector F (disk (circlePoint t)) secondNormal := by
  rw [disk_boundary _ (circlePoint_mem t)]
  change fderiv ℝ F.toFun _ (frameB (boundaryCore (circlePoint t)))=_
  rw [contact_normal_twist,map_add,map_smul,map_smul]
  rfl

lemma pushed_boundary_actual_tangent (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (imageDisk F) u (circleTangent u)=pushVector F (disk u) (boundaryTangent u) := by
  rw [pushed_boundary_tangent F u hu,disk_boundary u hu]
  exact congrArg (pushVector F (boundaryCore u)) (boundary_frame_values u).1

lemma twisting_lift_increment (θ : ℝ → ℝ)
    (hθ : ContinuousOn θ (Icc 0 (2*Real.pi)))
    (hcos : ∀ t ∈ Icc 0 (2*Real.pi), Real.cos (θ t)=Real.sin t)
    (hsin : ∀ t ∈ Icc 0 (2*Real.pi), Real.sin (θ t)=Real.cos t) :
    θ (2*Real.pi)-θ 0= -2*Real.pi := by
  let f : ℝ → ℝ := fun t => (θ t-twistAngle t)/(2*Real.pi)
  have hf : ContinuousOn f (Icc 0 (2*Real.pi)) :=
    (hθ.sub ((continuous_const.sub continuous_id).continuousOn)).div_const _
  have hm : MapsTo f (Icc 0 (2*Real.pi)) (range ((↑) : ℤ → ℝ)) := by
    intro t ht
    have he : Real.cos (θ t-twistAngle t)=1 := by
      rw [Real.cos_sub,hcos t ht,hsin t ht]
      simp only [twistAngle,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
      nlinarith [Real.sin_sq_add_cos_sq t]
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp he
    refine ⟨n,?_⟩
    dsimp [f]
    rw [← hn]
    field_simp [Real.pi_ne_zero]
  have he := isPreconnected_Icc.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hf hm
    (show (0:ℝ) ∈ Icc 0 (2*Real.pi) from ⟨le_rfl,by positivity⟩)
    (show 2*Real.pi ∈ Icc 0 (2*Real.pi) from ⟨by positivity,le_rfl⟩)
  dsimp [f] at he
  have hh := (div_left_inj' (show (2*Real.pi:ℝ) ≠ 0 by positivity)).mp he
  unfold twistAngle at hh
  linarith

lemma rotation_lift_increment (θ : ℝ → ℝ)
    (hθ : ContinuousOn θ (Icc 0 (2*Real.pi)))
    (hcos : ∀ t ∈ Icc 0 (2*Real.pi), Real.cos (θ t)=1)
    (hsin : ∀ t ∈ Icc 0 (2*Real.pi), Real.sin (θ t)=0) :
    θ (2*Real.pi)-θ 0=0 := by
  let f : ℝ → ℝ := fun t => θ t/(2*Real.pi)
  have hf : ContinuousOn f (Icc 0 (2*Real.pi)) := hθ.div_const _
  have hm : MapsTo f (Icc 0 (2*Real.pi)) (range ((↑) : ℤ → ℝ)) := by
    intro t ht
    obtain ⟨n,hn⟩ := (Real.cos_eq_one_iff _).mp (hcos t ht)
    refine ⟨n,?_⟩
    dsimp [f]
    rw [← hn]
    field_simp [Real.pi_ne_zero]
  have he := isPreconnected_Icc.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hf hm
    (show (0:ℝ) ∈ Icc 0 (2*Real.pi) from ⟨le_rfl,by positivity⟩)
    (show 2*Real.pi ∈ Icc 0 (2*Real.pi) from ⟨by positivity,le_rfl⟩)
  dsimp [f] at he
  have hh := (div_left_inj' (show (2*Real.pi:ℝ) ≠ 0 by positivity)).mp he
  linarith

lemma pushed_boundary_frame_independent (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) (a b d : ℝ)
    (h : a • pushVector F (disk u) (boundaryTangent u)+
      b • pushVector F (disk u) inwardNormal+
      d • pushVector F (disk u) secondNormal=0) : a=0 ∧ b=0 ∧ d=0 := by
  apply boundary_normal_frame_independent u hu a b d
  have hh := congrArg (fderiv ℝ F.invFun (F.toFun (disk u))) h
  simp only [map_add,map_smul,map_zero,pushVector] at hh
  have hT : phaseDot (disk u) (boundaryTangent u)=0 := by
    rw [disk_boundary u hu]
    simp [boundaryTangent,phaseDot]
    ring
  have hN : phaseDot (disk u) inwardNormal=0 := by
    rw [disk_boundary u hu]
    simp [inwardNormal,phaseDot]
  have hM : phaseDot (disk u) secondNormal=0 := by
    rw [disk_boundary u hu]
    simp [secondNormal,phaseDot]
  rw [sphere_derivative_left_inverse F _ _ (disk_sphere u) hT,
    sphere_derivative_left_inverse F _ _ (disk_sphere u) hN,
    sphere_derivative_left_inverse F _ _ (disk_sphere u) hM] at hh
  exact hh

lemma pushed_normal_angle_coefficients (F : EquivariantSphereContactomorphism)
    (t a b d : ℝ)
    (h : pushVector F (disk (circlePoint t)) (frameB (disk (circlePoint t)))=
      a • pushVector F (disk (circlePoint t)) (boundaryTangent (circlePoint t))+
      b • pushVector F (disk (circlePoint t)) inwardNormal+
      d • pushVector F (disk (circlePoint t)) secondNormal) :
    a=0 ∧ b=Real.sin t ∧ d=Real.cos t := by
  have hh := congrArg (fderiv ℝ F.invFun (F.toFun (disk (circlePoint t)))) h
  have hc := (frame_identities (disk (circlePoint t))).2.1
  have hT : phaseDot (disk (circlePoint t)) (boundaryTangent (circlePoint t))=0 := by
    rw [disk_boundary _ (circlePoint_mem t)]
    simp [boundaryTangent,phaseDot,circlePoint]
    ring
  have hN : phaseDot (disk (circlePoint t)) inwardNormal=0 := by
    rw [disk_boundary _ (circlePoint_mem t)]
    simp [inwardNormal,phaseDot]
  have hM : phaseDot (disk (circlePoint t)) secondNormal=0 := by
    rw [disk_boundary _ (circlePoint_mem t)]
    simp [secondNormal,phaseDot]
  simp only [map_add,map_smul,pushVector] at hh
  rw [sphere_derivative_left_inverse F _ _ (disk_sphere _) hc,
    sphere_derivative_left_inverse F _ _ (disk_sphere _) hT,
    sphere_derivative_left_inverse F _ _ (disk_sphere _) hN,
    sphere_derivative_left_inverse F _ _ (disk_sphere _) hM,
    disk_boundary _ (circlePoint_mem t)] at hh
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  have h2 := congrFun hh 2
  have h3 := congrFun hh 3
  dsimp [frameB,boundaryTangent,inwardNormal,secondNormal,circlePoint] at h0 h1 h2 h3
  simp only [neg_zero,mul_zero,zero_add,add_zero,mul_one,mul_neg] at h0 h1 h2 h3
  refine ⟨?_,h2.symm,by linarith⟩
  have he : a*(Real.sin t^2+Real.cos t^2)=0 := by
    linear_combination (Real.sin t)*h0-(Real.cos t)*h1
  rw [Real.sin_sq_add_cos_sq,mul_one] at he
  exact he

lemma pushed_twisting_lift_increment (F : EquivariantSphereContactomorphism)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 (2*Real.pi)))
    (hlift : ∀ t ∈ Icc 0 (2*Real.pi), ∃ a : ℝ,
      pushVector F (disk (circlePoint t)) (frameB (disk (circlePoint t)))=
        a • pushVector F (disk (circlePoint t)) (boundaryTangent (circlePoint t))+
        Real.cos (θ t) • pushVector F (disk (circlePoint t)) inwardNormal+
        Real.sin (θ t) • pushVector F (disk (circlePoint t)) secondNormal) :
    θ (2*Real.pi)-θ 0= -2*Real.pi := by
  apply twisting_lift_increment θ hθ
  · intro t ht
    obtain ⟨a,ha⟩ := hlift t ht
    exact (pushed_normal_angle_coefficients F t a _ _ ha).2.1
  · intro t ht
    obtain ⟨a,ha⟩ := hlift t ht
    exact (pushed_normal_angle_coefficients F t a _ _ ha).2.2

lemma pushed_rotation_lift_increment (F : EquivariantSphereContactomorphism)
    (θ : ℝ → ℝ) (hθ : ContinuousOn θ (Icc 0 (2*Real.pi)))
    (hlift : ∀ t ∈ Icc 0 (2*Real.pi),
      fderiv ℝ (imageDisk F) (circlePoint t) (circleTangent (circlePoint t))=
        Real.cos (θ t) • pushVector F (disk (circlePoint t)) (frameA (disk (circlePoint t)))+
        Real.sin (θ t) • pushVector F (disk (circlePoint t)) (frameB (disk (circlePoint t)))) :
    θ (2*Real.pi)-θ 0=0 := by
  have hcoeff (t : ℝ) (ht : t ∈ Icc 0 (2*Real.pi)) :
      Real.cos (θ t)=1 ∧ Real.sin (θ t)=0 := by
    have he := hlift t ht
    rw [pushed_boundary_tangent F _ (circlePoint_mem t)] at he
    have hh : (Real.cos (θ t)-1) • pushVector F (disk (circlePoint t)) (frameA (disk (circlePoint t)))+
        Real.sin (θ t) • pushVector F (disk (circlePoint t)) (frameB (disk (circlePoint t)))=0 := by
      rw [sub_smul,one_smul]
      rw [sub_add_eq_add_sub,← he,sub_self]
    have hc := pushed_frame_independent F _ (disk_sphere _) _ _ hh
    exact ⟨by linarith [hc.1],hc.2⟩
  exact rotation_lift_increment θ hθ (fun t ht => (hcoeff t ht).1)
    (fun t ht => (hcoeff t ht).2)

end
end ContactTopology.CoreDisk

namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection
open scoped ContDiff
noncomputable section
def sphereRadialForm (y : Phase) : Phase →L[ℝ] ℝ :=
  (y 2/2) • ContinuousLinearMap.proj 0+(y 3/2) • ContinuousLinearMap.proj 1-
    (y 0/2) • ContinuousLinearMap.proj 2-(y 1/2) • ContinuousLinearMap.proj 3

lemma sphereRadialForm_apply (y v : Phase) : sphereRadialForm y v = phaseRadialContact y v := by
  simp [sphereRadialForm,phaseRadialContact,phaseSymplecticForm]
  ring

lemma sphereRadialForm_contDiff : ContDiff ℝ ∞ sphereRadialForm := by
  exact (((((contDiff_apply ℝ ℝ 2).div_const 2).smul contDiff_const).add
    (((contDiff_apply ℝ ℝ 3).div_const 2).smul contDiff_const)).sub
    (((contDiff_apply ℝ ℝ 0).div_const 2).smul contDiff_const)).sub
    (((contDiff_apply ℝ ℝ 1).div_const 2).smul contDiff_const)

def sphereRadialFormLinear : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := sphereRadialForm
      map_add' := by intro u v; ext w; simp [sphereRadialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring
      map_smul' := by intro a v; ext w; simp [sphereRadialForm_apply,phaseRadialContact,phaseSymplecticForm]; ring }

lemma sphereRadialForm_fderiv (y u v : Phase) :
    fderiv ℝ sphereRadialForm y u v = phaseRadialContact u v := by
  have hlin : fderiv ℝ (sphereRadialFormLinear : Phase → (Phase →L[ℝ] ℝ)) y = sphereRadialFormLinear :=
    sphereRadialFormLinear.hasFDerivAt.fderiv
  have he := congrArg (fun L : Phase →L[ℝ] (Phase →L[ℝ] ℝ) => L u) hlin
  change fderiv ℝ sphereRadialForm y u = sphereRadialForm u at he
  rw [he,sphereRadialForm_apply]

end
end ContactTopology.CoreDisk

namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def dotForm (y : Phase) : Phase →L[ℝ] ℝ :=
  y 0 • ContinuousLinearMap.proj 0+y 1 • ContinuousLinearMap.proj 1+
    y 2 • ContinuousLinearMap.proj 2+y 3 • ContinuousLinearMap.proj 3

lemma dotForm_apply (y v : Phase) : dotForm y v=phaseDot y v := by
  simp [dotForm,phaseDot]

def dotFormLinear : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := dotForm
      map_add' := by intro u v; ext w; simp [dotForm_apply,phaseDot]; ring
      map_smul' := by intro a v; ext w; simp [dotForm_apply,phaseDot]; ring }

lemma dotForm_contDiff : ContDiff ℝ ∞ dotForm := dotFormLinear.contDiff

lemma dotForm_fderiv (y u v : Phase) : fderiv ℝ dotForm y u v=phaseDot u v := by
  have he := congrArg (fun L : Phase →L[ℝ] (Phase →L[ℝ] ℝ) => L u)
    (dotFormLinear.hasFDerivAt (x := y)).fderiv
  change fderiv ℝ dotForm y u=dotForm u at he
  rw [he,dotForm_apply]

def contactReeb (y : Phase) : Phase := ![y 2,y 3,-y 0,-y 1]

lemma contactReeb_tangent (y : Phase) : phaseDot y (contactReeb y)=0 := by
  dsimp [contactReeb,phaseDot]
  ring

lemma contactReeb_value (y : Phase) :
    2*phaseRadialContact y (contactReeb y)=phaseDot y y := by
  dsimp [contactReeb,phaseRadialContact,phaseSymplecticForm,phaseDot]
  ring

lemma contact_self_zero (y : Phase) : phaseRadialContact y y=0 := by
  simp [phaseRadialContact,phaseSymplecticForm]
  ring

lemma contact_skew (u v : Phase) : phaseRadialContact u v= -phaseRadialContact v u := by
  dsimp [phaseRadialContact,phaseSymplecticForm]
  ring

def contactPullback (F : EquivariantSphereContactomorphism) (y : Phase) : Phase →L[ℝ] ℝ :=
  (sphereRadialForm (F.toFun y)).comp (fderiv ℝ F.toFun y)

lemma contactPullback_apply (F : EquivariantSphereContactomorphism) (y v : Phase) :
    contactPullback F y v=phaseRadialContact (F.toFun y) (pushVector F y v) := by
  simp only [contactPullback,ContinuousLinearMap.comp_apply,sphereRadialForm_apply,pushVector]

def contactFactor (F : EquivariantSphereContactomorphism) (y : Phase) : ℝ :=
  2*contactPullback F y (contactReeb y)

def radialError (F : EquivariantSphereContactomorphism) (y : Phase) : ℝ :=
  contactPullback F y y

lemma contactPullback_smooth (F : EquivariantSphereContactomorphism) (y : Phase)
    (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (contactPullback F) y :=
  (sphereRadialForm_contDiff.contDiffAt.comp y (F.smooth y hy)).clm_comp
    ((F.smooth y hy).fderiv_right (by simp))

lemma contactFactor_smooth (F : EquivariantSphereContactomorphism) (y : Phase)
    (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (contactFactor F) y := by
  have hR : ContDiff ℝ ∞ contactReeb := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp [contactReeb] <;> fun_prop
  exact contDiffAt_const.mul ((contactPullback_smooth F y hy).clm_apply hR.contDiffAt)

lemma radialError_smooth (F : EquivariantSphereContactomorphism) (y : Phase)
    (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (radialError F) y :=
  (contactPullback_smooth F y hy).clm_apply contDiffAt_id

lemma contactFactor_positive_and_pullback (F : EquivariantSphereContactomorphism)
    (y : Phase) (hy : y ∈ unitThreeSphere) :
    0 < contactFactor F y ∧ ∀ v : Phase, phaseDot y v=0 →
      phaseRadialContact (F.toFun y) (pushVector F y v)=
        contactFactor F y*phaseRadialContact y v := by
  obtain ⟨a,ha,hF⟩ := F.contact y hy
  have he : contactFactor F y=a := by
    have hh := hF (contactReeb y) (contactReeb_tangent y)
    change phaseRadialContact (F.toFun y) (pushVector F y (contactReeb y))=_ at hh
    rw [← contactPullback_apply] at hh
    have hR := contactReeb_value y
    rw [sphere_dot_self hy] at hR
    unfold contactFactor
    rw [hh]
    nlinarith
  rw [he]
  exact ⟨ha,hF⟩

def contactPullbackExtension (F : EquivariantSphereContactomorphism) (y : Phase) : Phase →L[ℝ] ℝ :=
  contactFactor F y • sphereRadialForm y+radialError F y • dotForm y

lemma contactPullbackExtension_smooth (F : EquivariantSphereContactomorphism)
    (y : Phase) (hy : y ∈ unitThreeSphere) : ContDiffAt ℝ ∞ (contactPullbackExtension F) y :=
  ((contactFactor_smooth F y hy).smul sphereRadialForm_contDiff.contDiffAt).add
    ((radialError_smooth F y hy).smul dotForm_contDiff.contDiffAt)

lemma contactPullback_decomposition (F : EquivariantSphereContactomorphism) :
    EqOn (contactPullback F) (contactPullbackExtension F) unitThreeSphere := by
  intro y hy
  ext v
  have ht : phaseDot y (v-phaseDot y v • y)=0 := by
    change dotForm y (v-phaseDot y v • y)=0
    rw [map_sub,map_smul,dotForm_apply,dotForm_apply,sphere_dot_self hy]
    ring
  have hh := (contactFactor_positive_and_pullback F y hy).2 (v-phaseDot y v • y) ht
  rw [← contactPullback_apply,← sphereRadialForm_apply] at hh
  rw [map_sub,map_smul,map_sub,map_smul,sphereRadialForm_apply,sphereRadialForm_apply,
    contact_self_zero,smul_zero,sub_zero] at hh
  simp only [smul_eq_mul] at hh
  change contactPullback F y v=
    contactFactor F y*sphereRadialForm y v+radialError F y*dotForm y v
  rw [sphereRadialForm_apply,dotForm_apply]
  unfold radialError
  linarith

lemma contactPullbackExtension_fderiv (F : EquivariantSphereContactomorphism)
    (y u v : Phase) (hy : y ∈ unitThreeSphere) :
    fderiv ℝ (contactPullbackExtension F) y u v=
      fderiv ℝ (contactFactor F) y u*phaseRadialContact y v+
      contactFactor F y*phaseRadialContact u v+
      fderiv ℝ (radialError F) y u*phaseDot y v+
      radialError F y*phaseDot u v := by
  have hd := (((contactFactor_smooth F y hy).differentiableAt (by simp)).hasFDerivAt.smul
    (sphereRadialForm_contDiff.differentiable (by simp) y).hasFDerivAt).add
    ((((radialError_smooth F y hy).differentiableAt (by simp)).hasFDerivAt.smul
      (dotForm_contDiff.differentiable (by simp) y).hasFDerivAt))
  change HasFDerivAt (contactPullbackExtension F) _ y at hd
  rw [hd.fderiv]
  simp [sphereRadialForm_apply,sphereRadialForm_fderiv,dotForm_apply,dotForm_fderiv]
  ring

lemma contact_exterior_transport (F : EquivariantSphereContactomorphism)
    (y u v : Phase) (hy : y ∈ unitThreeSphere)
    (hu : phaseDot y u=0) (hv : phaseDot y v=0) :
    2*phaseRadialContact (pushVector F y u) (pushVector F y v)=
      fderiv ℝ (contactFactor F) y u*phaseRadialContact y v-
      fderiv ℝ (contactFactor F) y v*phaseRadialContact y u+
      2*contactFactor F y*phaseRadialContact u v := by
  have hp := ContactCalculus.exterior_pairing_pullback sphereRadialForm F.toFun y u v
    (sphereRadialForm_contDiff.differentiable (by simp) _)
    ((F.smooth y hy).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  change fderiv ℝ (contactPullback F) y u v-fderiv ℝ (contactPullback F) y v u=_ at hp
  have heu := sphere_tangent_fderiv_eq (contactPullback F) (contactPullbackExtension F) y u hy hu
    ((contactPullback_smooth F y hy).differentiableAt (by simp))
    ((contactPullbackExtension_smooth F y hy).differentiableAt (by simp))
    (contactPullback_decomposition F)
  have hev := sphere_tangent_fderiv_eq (contactPullback F) (contactPullbackExtension F) y v hy hv
    ((contactPullback_smooth F y hy).differentiableAt (by simp))
    ((contactPullbackExtension_smooth F y hy).differentiableAt (by simp))
    (contactPullback_decomposition F)
  rw [heu,hev,contactPullbackExtension_fderiv F y u v hy,
    contactPullbackExtension_fderiv F y v u hy,sphereRadialForm_fderiv,sphereRadialForm_fderiv,
    hu,hv,mul_zero,mul_zero] at hp
  have hdot : phaseDot u v=phaseDot v u := by dsimp [phaseDot]; ring
  rw [hdot,contact_skew v u,contact_skew (fderiv ℝ F.toFun y v) (fderiv ℝ F.toFun y u)] at hp
  change 2*phaseRadialContact (fderiv ℝ F.toFun y u) (fderiv ℝ F.toFun y v)=_
  linarith

lemma pushed_contact_frame_positive (F : EquivariantSphereContactomorphism)
    (y : Phase) (hy : y ∈ unitThreeSphere) :
    0 < phaseRadialContact (pushVector F y (frameA y)) (pushVector F y (frameB y)) := by
  have hh := frame_identities y
  have he := contact_exterior_transport F y (frameA y) (frameB y) hy hh.1 hh.2.1
  rw [hh.2.2.1,hh.2.2.2.1,mul_zero,mul_zero,sub_self,zero_add] at he
  have hf := hh.2.2.2.2.2.2.2
  rw [sphere_dot_self hy] at hf
  nlinarith [(contactFactor_positive_and_pullback F y hy).1]

lemma contact_volume_transport (F : EquivariantSphereContactomorphism)
    (y u v w : Phase) (hy : y ∈ unitThreeSphere)
    (hu : phaseDot y u=0) (hv : phaseDot y v=0) (hw : phaseDot y w=0) :
    contactVolume (F.toFun y) (pushVector F y u) (pushVector F y v) (pushVector F y w)=
      contactFactor F y^2*contactVolume y u v w := by
  have hF := (contactFactor_positive_and_pullback F y hy).2
  have huv := contact_exterior_transport F y u v hy hu hv
  have huw := contact_exterior_transport F y u w hy hu hw
  have hvw := contact_exterior_transport F y v w hy hv hw
  unfold contactVolume
  rw [hF u hu,hF v hv,hF w hw]
  linear_combination (contactFactor F y*phaseRadialContact y u)*hvw-
    (contactFactor F y*phaseRadialContact y v)*huw+
    (contactFactor F y*phaseRadialContact y w)*huv

lemma pushed_boundary_normal_frame_positive (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    0 < contactVolume (imageDisk F u)
      (pushVector F (disk u) (boundaryTangent u))
      (pushVector F (disk u) inwardNormal) (pushVector F (disk u) secondNormal) := by
  have hT : phaseDot (disk u) (boundaryTangent u)=0 := by
    rw [disk_boundary u hu]
    dsimp [phaseDot,boundaryTangent]
    ring
  have hN : phaseDot (disk u) inwardNormal=0 := by
    rw [disk_boundary u hu]
    simp [phaseDot,inwardNormal]
  have hM : phaseDot (disk u) secondNormal=0 := by
    rw [disk_boundary u hu]
    simp [phaseDot,secondNormal]
  change 0 < contactVolume (F.toFun (disk u)) _ _ _
  have hvol : contactVolume (disk u) (boundaryTangent u) inwardNormal secondNormal=1/2 := by
    rw [disk_boundary u hu]
    exact boundary_normal_frame_positive u hu
  rw [contact_volume_transport F _ _ _ _ (disk_sphere u) hT hN hM,hvol]
  exact mul_pos (sq_pos_of_pos (contactFactor_positive_and_pullback F _ (disk_sphere u)).1)
    (by norm_num)

end
end ContactTopology.CoreDisk

namespace ContactTopology.CoreDisk
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma disk_fderiv_apply (u v : Plane) :
    fderiv ℝ disk u v=
      ![(2*v 0*(1+planeNormSq u)-4*u 0*(u 0*v 0+u 1*v 1))/(1+planeNormSq u)^2,
        (2*v 1*(1+planeNormSq u)-4*u 1*(u 0*v 0+u 1*v 1))/(1+planeNormSq u)^2,
        -4*(u 0*v 0+u 1*v 1)/(1+planeNormSq u)^2,0] := by
  have h0 := (ContinuousLinearMap.proj (0:Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h1 := (ContinuousLinearMap.proj (1:Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := u)
  have hn := (h0.pow 2).add (h1.pow 2)
  change HasFDerivAt planeNormSq _ u at hn
  have hi := (hasFDerivAt_inv (denominator_pos u).ne').comp u ((hasFDerivAt_const (1:ℝ) u).add hn)
  have d0 := ((h0.const_mul 2).mul hi).fderiv
  have d1 := ((h1.const_mul 2).mul hi).fderiv
  have d2 := (((hasFDerivAt_const (1:ℝ) u).sub hn).mul hi).fderiv
  change fderiv ℝ (fun w : Plane => (2*w 0)*(1+planeNormSq w)⁻¹) u=_ at d0
  change fderiv ℝ (fun w : Plane => (2*w 1)*(1+planeNormSq w)⁻¹) u=_ at d1
  change fderiv ℝ (fun w : Plane => (1-planeNormSq w)*(1+planeNormSq w)⁻¹) u=_ at d2
  have hd := disk_contDiff.differentiable (by simp) u
  ext i
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L v) (fderiv_apply hd i)
  change fderiv ℝ (fun w => disk w i) u v=fderiv ℝ disk u v i at he
  fin_cases i
  · change _ = (2*v 0*(1+planeNormSq u)-4*u 0*(u 0*v 0+u 1*v 1))/(1+planeNormSq u)^2
    rw [← he]
    change fderiv ℝ (fun w : Plane => (2*w 0)*(1+planeNormSq w)⁻¹) u v=_
    rw [d0]
    simp
    field_simp [(denominator_pos u).ne']
    ring
  · change _ = (2*v 1*(1+planeNormSq u)-4*u 1*(u 0*v 0+u 1*v 1))/(1+planeNormSq u)^2
    rw [← he]
    change fderiv ℝ (fun w : Plane => (2*w 1)*(1+planeNormSq w)⁻¹) u v=_
    rw [d1]
    simp
    field_simp [(denominator_pos u).ne']
    ring
  · change _ = -4*(u 0*v 0+u 1*v 1)/(1+planeNormSq u)^2
    rw [← he]
    change fderiv ℝ (fun w : Plane => (1-planeNormSq w)*(1+planeNormSq w)⁻¹) u v=_
    rw [d2]
    simp
    field_simp [(denominator_pos u).ne']
    ring
  · change _ = 0
    rw [← he]
    change fderiv ℝ (fun _ : Plane => (0:ℝ)) u v=0
    simp

def pushCos (s : ℝ) : ℝ := (1-s^2)/(1+s^2)
def pushSin (s : ℝ) : ℝ := 2*s/(1+s^2)

lemma push_denominator_pos (s : ℝ) : 0 < 1+s^2 := by nlinarith [sq_nonneg s]

lemma pushCos_sq_add_pushSin_sq (s : ℝ) : pushCos s^2+pushSin s^2=1 := by
  unfold pushCos pushSin
  field_simp [(push_denominator_pos s).ne']
  ring

def pushCircle (s : ℝ) (u : Plane) : Phase :=
  pushCos s • boundaryCore u+pushSin s • frameB (boundaryCore u)

lemma pushCircle_coordinates (s : ℝ) (u : Plane) :
    pushCircle s u=![pushCos s*u 0,pushCos s*u 1,pushSin s*u 1,-pushSin s*u 0] := by
  ext i
  fin_cases i <;> simp [pushCircle,boundaryCore,frameB]

lemma pushCircle_smooth : ContDiff ℝ ∞ (fun z : ℝ × Plane => pushCircle z.1 z.2) := by
  have hi : ContDiff ℝ ∞ (fun z : ℝ × Plane => (1+z.1^2)⁻¹) :=
    (contDiff_const.add (contDiff_fst.pow 2)).inv (fun z => (push_denominator_pos z.1).ne')
  apply contDiff_pi.mpr
  intro i
  simp only [pushCircle_coordinates]
  fin_cases i <;> dsimp [pushCos,pushSin] <;> (try simp only [div_eq_mul_inv]) <;> fun_prop

lemma pushCircle_sphere (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    pushCircle s u ∈ unitThreeSphere := by
  have hs : u 0^2+u 1^2=1 := hu
  rw [pushCircle_coordinates]
  change (pushCos s*u 0)^2+(pushCos s*u 1)^2+
    ((pushSin s*u 1)^2+(-pushSin s*u 0)^2)=1
  calc
    _ = (pushCos s^2+pushSin s^2)*(u 0^2+u 1^2) := by ring
    _ = 1 := by rw [pushCos_sq_add_pushSin_sq,hs]; norm_num

def pushCircleLinear (s : ℝ) : Plane →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := pushCircle s
      map_add' := by
        intro u v
        simp only [pushCircle_coordinates]
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro a v
        simp only [pushCircle_coordinates]
        ext i
        fin_cases i <;> simp <;> ring }

lemma pushCircle_fderiv (s : ℝ) (u v : Plane) :
    fderiv ℝ (pushCircle s) u v=pushCircle s v :=
  congrArg (fun L : Plane →L[ℝ] Phase => L v) (pushCircleLinear s).hasFDerivAt.fderiv

lemma pushCircle_injective (s : ℝ) : Injective (pushCircle s) := by
  intro u v he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  simp only [pushCircle_coordinates] at h0 h1 h2 h3
  dsimp at h0 h1 h2 h3
  have hs := pushCos_sq_add_pushSin_sq s
  by_cases ha : pushCos s=0
  · have hb : pushSin s ≠ 0 := by intro hb; simp [ha,hb] at hs
    ext i
    fin_cases i
    · exact mul_left_cancel₀ (neg_ne_zero.mpr hb) h3
    · exact mul_left_cancel₀ hb h2
  · ext i
    fin_cases i
    · exact mul_left_cancel₀ ha h0
    · exact mul_left_cancel₀ ha h1

lemma pushCircle_odd (s : ℝ) (u : Plane) : pushCircle s (-u)= -pushCircle s u :=
  (pushCircleLinear s).map_neg u

lemma pushCircle_start (u : Plane) : pushCircle 0 u=boundaryCore u := by
  simp [pushCircle,pushCos,pushSin]

lemma pushCircle_initial_velocity (u : Plane) :
    HasDerivAt (fun s : ℝ => pushCircle s u) ((2:ℝ) • frameB (boundaryCore u)) 0 := by
  have hs := (hasDerivAt_id (0:ℝ)).pow 2
  have ha := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub hs).div
    ((hasDerivAt_const (0:ℝ) (1:ℝ)).add hs) (by norm_num)
  have hb := ((hasDerivAt_id (0:ℝ)).const_mul 2).div
    ((hasDerivAt_const (0:ℝ) (1:ℝ)).add hs) (by norm_num)
  have hd := (ha.smul_const (boundaryCore u)).add (hb.smul_const (frameB (boundaryCore u)))
  convert! hd using 1 <;> norm_num [pushCircle,pushCos,pushSin]

lemma pushCircle_avoids_core (s : ℝ) (hs : s ≠ 0) (u v : Plane)
    (hu : u ∈ unitCircle) : pushCircle s u ≠ boundaryCore v := by
  intro he
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  simp only [pushCircle_coordinates] at h2 h3
  dsimp [boundaryCore] at h2 h3
  have hb : pushSin s ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hs) (push_denominator_pos s).ne'
  have hu1 : u 1=0 := (mul_eq_zero.mp h2).resolve_left hb
  have hu0 : u 0=0 := by
    have hh : pushSin s*u 0=0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_left hb
  have hh : u 0^2+u 1^2=1 := hu
  simp [hu0,hu1] at hh

def diskIntersectionParameter : Plane := ![0,1/3]
def circleIntersectionParameter : Plane := ![0,1]

lemma intersection_parameter_interior : planeNormSq diskIntersectionParameter < 1 := by
  norm_num [planeNormSq,diskIntersectionParameter]

lemma fixed_push_intersection :
    disk diskIntersectionParameter=pushCircle (1/2) circleIntersectionParameter := by
  rw [pushCircle_coordinates]
  ext i
  fin_cases i <;> norm_num [disk,planeNormSq,diskIntersectionParameter,circleIntersectionParameter,pushCos,pushSin]

lemma fixed_push_intersection_unique (u v : Plane) (hu : u ∈ unitCircle)
    (hv : planeNormSq v ≤ 1) :
    disk v=pushCircle (1/2) u ↔
      v=diskIntersectionParameter ∧ u=circleIntersectionParameter := by
  constructor
  · intro he
    have h3 := congrFun he 3
    have h2 := congrFun he 2
    rw [pushCircle_coordinates] at h3 h2
    dsimp [disk,pushCos,pushSin] at h3 h2
    norm_num at h3 h2
    have hs : u 0^2+u 1^2=1 := hu
    have h0 : u 0=0 := by linarith
    have h1 : u 1=1 := by
      have hp := disk_upper v hv
      change 0 ≤ (1-planeNormSq v)/(1+planeNormSq v) at hp
      have hn : 0 ≤ u 1 := by linarith
      nlinarith
    have hu' : u=circleIntersectionParameter := by ext i; fin_cases i <;> simp [circleIntersectionParameter,h0,h1]
    refine ⟨?_,hu'⟩
    apply disk_injective
    rw [he,hu',fixed_push_intersection]
  · rintro ⟨rfl,rfl⟩
    exact fixed_push_intersection

lemma fixed_push_quotient_intersection_unique (u v : Plane) (hu : u ∈ unitCircle)
    (hv : planeNormSq v ≤ 1) :
    (disk v=pushCircle (1/2) u ∨ disk v= -pushCircle (1/2) u) ↔
      v=diskIntersectionParameter ∧
        (u=circleIntersectionParameter ∨ u= -circleIntersectionParameter) := by
  constructor
  · rintro (he|he)
    · obtain ⟨hv',hu'⟩ := (fixed_push_intersection_unique u v hu hv).mp he
      exact ⟨hv',Or.inl hu'⟩
    · have hneg : -u ∈ unitCircle := by simpa [unitCircle,planeNormSq] using hu
      rw [← pushCircle_odd] at he
      obtain ⟨hv',hu'⟩ := (fixed_push_intersection_unique (-u) v hneg hv).mp he
      exact ⟨hv',Or.inr (neg_eq_iff_eq_neg.mp hu')⟩
  · rintro ⟨rfl,he|he⟩
    · rw [he]
      exact Or.inl fixed_push_intersection
    · rw [he,pushCircle_odd,neg_neg]
      exact Or.inr fixed_push_intersection

lemma fixed_push_intersection_sign :
    contactVolume (disk diskIntersectionParameter)
      (fderiv ℝ disk diskIntersectionParameter ![1,0])
      (fderiv ℝ disk diskIntersectionParameter ![0,1])
      (fderiv ℝ (pushCircle (1/2)) circleIntersectionParameter
        (circleTangent circleIntersectionParameter)) < 0 := by
  rw [disk_fderiv_apply,disk_fderiv_apply,pushCircle_fderiv,pushCircle_coordinates]
  dsimp [contactVolume,disk,planeNormSq,diskIntersectionParameter,circleIntersectionParameter,
    circleTangent,pushCos,pushSin,phaseRadialContact,phaseSymplecticForm]
  norm_num

def imagePushCircle (F : EquivariantSphereContactomorphism) (s : ℝ) : Plane → Phase :=
  F.toFun ∘ pushCircle s

lemma imagePushCircle_smooth (F : EquivariantSphereContactomorphism) (s : ℝ)
    (u : Plane) (hu : u ∈ unitCircle) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Plane => imagePushCircle F z.1 z.2) (s,u) :=
  (F.smooth _ (pushCircle_sphere s u hu)).comp (s,u) pushCircle_smooth.contDiffAt

lemma imagePushCircle_sphere (F : EquivariantSphereContactomorphism) (s : ℝ)
    (u : Plane) (hu : u ∈ unitCircle) :
    imagePushCircle F s u ∈ unitThreeSphere := F.maps_sphere (pushCircle_sphere s u hu)

lemma imagePushCircle_injective (F : EquivariantSphereContactomorphism) (s : ℝ) :
    InjOn (imagePushCircle F s) unitCircle := by
  intro u hu v hv he
  apply pushCircle_injective s
  have hh := congrArg F.invFun he
  simpa only [imagePushCircle,Function.comp_apply,F.left_inv _ (pushCircle_sphere s u hu),
    F.left_inv _ (pushCircle_sphere s v hv)] using hh

lemma imagePushCircle_odd (F : EquivariantSphereContactomorphism) (s : ℝ)
    (u : Plane) (hu : u ∈ unitCircle) :
    imagePushCircle F s (-u)= -imagePushCircle F s u := by
  change F.toFun (pushCircle s (-u))= -F.toFun (pushCircle s u)
  rw [pushCircle_odd,F.antipodal _ (pushCircle_sphere s u hu)]

lemma pushCircle_tangent (s : ℝ) (u : Plane) :
    phaseDot (pushCircle s u) (pushCircle s (circleTangent u))=0 := by
  simp only [pushCircle_coordinates]
  dsimp [phaseDot,circleTangent]
  ring

lemma pushCircle_contact_value (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    phaseRadialContact (pushCircle s u)
      (fderiv ℝ (pushCircle s) u (circleTangent u))= -pushCos s*pushSin s := by
  rw [pushCircle_fderiv]
  simp only [pushCircle_coordinates]
  have hs : u 0^2+u 1^2=1 := hu
  dsimp [phaseRadialContact,phaseSymplecticForm,circleTangent]
  linear_combination (-pushCos s*pushSin s)*hs

lemma imagePushCircle_negative (F : EquivariantSphereContactomorphism) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (u : Plane) (hu : u ∈ unitCircle) :
    phaseRadialContact (imagePushCircle F s u)
      (fderiv ℝ (imagePushCircle F s) u (circleTangent u)) < 0 := by
  have ha : 0 < pushCos s := div_pos (by nlinarith) (push_denominator_pos s)
  have hb : 0 < pushSin s := div_pos (by positivity) (push_denominator_pos s)
  obtain ⟨a,ha',hF⟩ := F.contact _ (pushCircle_sphere s u hu)
  have hD := fderiv_comp u ((F.smooth _ (pushCircle_sphere s u hu)).differentiableAt (by simp))
    (pushCircleLinear s).differentiableAt
  change phaseRadialContact (F.toFun (pushCircle s u))
    (fderiv ℝ (F.toFun ∘ pushCircle s) u (circleTangent u)) < 0
  rw [hD]
  change phaseRadialContact (F.toFun (pushCircle s u))
    (fderiv ℝ F.toFun (pushCircle s u) (fderiv ℝ (pushCircle s) u (circleTangent u))) < 0
  have ht : phaseDot (pushCircle s u) (fderiv ℝ (pushCircle s) u (circleTangent u))=0 := by
    rw [pushCircle_fderiv]
    exact pushCircle_tangent s u
  rw [hF _ ht,pushCircle_contact_value s u hu]
  exact mul_neg_of_pos_of_neg ha' (mul_neg_of_neg_of_pos (neg_neg_of_pos ha) hb)

lemma imagePushCircle_initial_velocity (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    HasDerivAt (fun s : ℝ => imagePushCircle F s u)
      ((2:ℝ) • pushVector F (disk u) (frameB (disk u))) 0 := by
  have hbd : disk u=boundaryCore u := disk_boundary u hu
  have hmem : boundaryCore u ∈ unitThreeSphere := by
    rw [← hbd]
    exact disk_sphere u
  have hF : DifferentiableAt ℝ F.toFun (pushCircle 0 u) := by
    rw [pushCircle_start]
    exact (F.smooth _ hmem).differentiableAt (by simp)
  have hd := hF.hasFDerivAt.comp_hasDerivAt 0 (pushCircle_initial_velocity u)
  rw [pushCircle_start,map_smul,← hbd] at hd
  exact hd

lemma imagePushCircle_avoids_core (F : EquivariantSphereContactomorphism)
    (s : ℝ) (hs : s ≠ 0) (u v : Plane) (hu : u ∈ unitCircle) (hv : v ∈ unitCircle) :
    imagePushCircle F s u ≠ F.toFun (boundaryCore v) := by
  intro he
  apply pushCircle_avoids_core s hs u v hu
  have hh := congrArg F.invFun he
  have hmem : boundaryCore v ∈ unitThreeSphere := by
    change ![v 0,v 1,0,0] ∈ unitThreeSphere
    rw [← disk_boundary v hv]
    exact disk_sphere v
  simpa only [imagePushCircle,Function.comp_apply,F.left_inv _ (pushCircle_sphere s u hu),
    F.left_inv _ hmem] using hh

lemma image_fixed_push_quotient_intersection_unique (F : EquivariantSphereContactomorphism)
    (u v : Plane) (hu : u ∈ unitCircle) (hv : planeNormSq v ≤ 1) :
    (imageDisk F v=imagePushCircle F (1/2) u ∨
      imageDisk F v= -imagePushCircle F (1/2) u) ↔
      v=diskIntersectionParameter ∧
        (u=circleIntersectionParameter ∨ u= -circleIntersectionParameter) := by
  have hraw :
      (imageDisk F v=imagePushCircle F (1/2) u ∨
        imageDisk F v= -imagePushCircle F (1/2) u) ↔
      (disk v=pushCircle (1/2) u ∨ disk v= -pushCircle (1/2) u) := by
    constructor
    · rintro (he|he)
      · left
        have hh := congrArg F.invFun he
        simpa only [imageDisk,imagePushCircle,Function.comp_apply,F.left_inv _ (disk_sphere v),
          F.left_inv _ (pushCircle_sphere (1/2) u hu)] using hh
      · right
        have hm : -pushCircle (1/2) u ∈ unitThreeSphere := by
          simpa [unitThreeSphere,zNormSq,wNormSq] using pushCircle_sphere (1/2) u hu
        have hh := congrArg F.invFun he
        change F.invFun (F.toFun (disk v))=F.invFun (-F.toFun (pushCircle (1/2) u)) at hh
        rw [← F.antipodal _ (pushCircle_sphere (1/2) u hu),F.left_inv _ (disk_sphere v),
          F.left_inv _ hm] at hh
        exact hh
    · rintro (he|he)
      · exact Or.inl (congrArg F.toFun he)
      · right
        change F.toFun (disk v)= -F.toFun (pushCircle (1/2) u)
        rw [he,F.antipodal _ (pushCircle_sphere (1/2) u hu)]
  exact hraw.trans (fixed_push_quotient_intersection_unique u v hu hv)

lemma image_fixed_push_intersection_sign (F : EquivariantSphereContactomorphism) :
    contactVolume (imageDisk F diskIntersectionParameter)
      (fderiv ℝ (imageDisk F) diskIntersectionParameter ![1,0])
      (fderiv ℝ (imageDisk F) diskIntersectionParameter ![0,1])
      (fderiv ℝ (imagePushCircle F (1/2)) circleIntersectionParameter
        (circleTangent circleIntersectionParameter)) < 0 := by
  have hq : circleIntersectionParameter ∈ unitCircle := by
    norm_num [circleIntersectionParameter,unitCircle,planeNormSq]
  have hd (v : Plane) : fderiv ℝ (imageDisk F) diskIntersectionParameter v=
      pushVector F (disk diskIntersectionParameter) (fderiv ℝ disk diskIntersectionParameter v) := by
    exact congrArg (fun L : Plane →L[ℝ] Phase => L v)
      (fderiv_comp _ ((F.smooth _ (disk_sphere _)).differentiableAt (by simp))
        (disk_contDiff.differentiable (by simp) _))
  have hp : fderiv ℝ (imagePushCircle F (1/2)) circleIntersectionParameter
      (circleTangent circleIntersectionParameter)=
      pushVector F (disk diskIntersectionParameter)
        (fderiv ℝ (pushCircle (1/2)) circleIntersectionParameter (circleTangent circleIntersectionParameter)) := by
    have hh := congrArg (fun L : Plane →L[ℝ] Phase => L (circleTangent circleIntersectionParameter))
      (fderiv_comp circleIntersectionParameter
        ((F.smooth _ (pushCircle_sphere (1/2) _ hq)).differentiableAt (by simp))
        (pushCircleLinear (1/2)).differentiableAt)
    change fderiv ℝ (imagePushCircle F (1/2)) circleIntersectionParameter _=
      fderiv ℝ F.toFun (pushCircle (1/2) circleIntersectionParameter) _ at hh
    rw [← fixed_push_intersection] at hh
    exact hh
  have htan (v : Plane) : phaseDot (disk diskIntersectionParameter)
      (fderiv ℝ disk diskIntersectionParameter v)=0 := by
    rw [disk_fderiv_apply]
    dsimp [disk,planeNormSq,diskIntersectionParameter,phaseDot]
    ring
  have hpt : phaseDot (disk diskIntersectionParameter)
      (fderiv ℝ (pushCircle (1/2)) circleIntersectionParameter (circleTangent circleIntersectionParameter))=0 := by
    rw [pushCircle_fderiv,pushCircle_coordinates]
    dsimp [disk,planeNormSq,diskIntersectionParameter,circleIntersectionParameter,circleTangent,phaseDot,pushCos,pushSin]
    norm_num
  rw [hd,hd,hp]
  change contactVolume (F.toFun (disk diskIntersectionParameter)) _ _ _ < 0
  rw [contact_volume_transport F _ _ _ _ (disk_sphere _) (htan _) (htan _) hpt]
  exact mul_neg_of_pos_of_neg
    (sq_pos_of_pos (contactFactor_positive_and_pullback F _ (disk_sphere _)).1)
    fixed_push_intersection_sign

end
end ContactTopology.CoreDisk




namespace ContactTopology.Projective
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphereSet_closed (n : ℕ) : IsClosed (sphereSet n) := by
  exact isClosed_eq (by fun_prop) continuous_const

lemma sphereSet_compact (n : ℕ) : IsCompact (sphereSet n) := by
  apply Metric.isCompact_of_isClosed_isBounded (sphereSet_closed n)
  apply (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := 1)).subset
  intro y hy
  rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  rw [Real.norm_eq_abs]
  apply (sq_le_one_iff_abs_le_one _).mp
  have hi : y i^2 ≤ ∑ j, y j^2 := Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  exact hi.trans_eq hy

instance (n : ℕ) : CompactSpace (RoundSphere n) := isCompact_iff_compactSpace.mp (sphereSet_compact n)

lemma sphere_not_zero (n : ℕ) (y : RoundSphere n) : (y : Fin n → ℝ) ≠ 0 := by
  intro he
  have hh := y.property
  change ∑ i, (y : Fin n → ℝ) i^2=1 at hh
  simp [he] at hh

lemma sphere_not_neg_self (n : ℕ) (y : RoundSphere n) : -(y : Fin n → ℝ) ≠ y := by
  intro he
  apply sphere_not_zero n y
  ext i
  change (y : Fin n → ℝ) i=0
  have hh := congrFun he i
  change -(y : Fin n → ℝ) i=(y : Fin n → ℝ) i at hh
  linarith

lemma units_smul_coe (n : ℕ) (g : ℤˣ) (y : RoundSphere n) :
    (g • y : RoundSphere n).val=(g : ℤ) • (y : Fin n → ℝ) := rfl

instance (n : ℕ) : ContinuousConstSMul ℤˣ (RoundSphere n) where
  continuous_const_smul g := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.const_smul (g : ℤ)

instance (n : ℕ) : IsCancelSMul ℤˣ (RoundSphere n) where
  right_cancel' g h y he := by
    have hh := congrArg Subtype.val he
    change (g : ℤ) • (y : Fin n → ℝ)=(h : ℤ) • (y : Fin n → ℝ) at hh
    obtain rfl|rfl := Int.units_eq_one_or g <;>
      obtain rfl|rfl := Int.units_eq_one_or h
    · rfl
    · simp at hh
      exact False.elim (sphere_not_neg_self n y hh.symm)
    · simp at hh
      exact False.elim (sphere_not_neg_self n y hh)
    · rfl

lemma project_eq_iff (n : ℕ) (x y : RoundSphere n) :
    project n x=project n y ↔ (x : Fin n → ℝ)=y ∨ (x : Fin n → ℝ)= -y := by
  constructor
  · intro he
    obtain ⟨g,hg⟩ := Quotient.exact he
    have hh := congrArg Subtype.val hg
    change (g : ℤ) • (y : Fin n → ℝ)=(x : Fin n → ℝ) at hh
    obtain rfl|rfl := Int.units_eq_one_or g
    · left
      simpa using hh.symm
    · right
      simpa using hh.symm
  · rintro (he|he)
    · apply Quotient.sound
      refine ⟨1,?_⟩
      apply Subtype.ext
      change (1:ℤ) • (y : Fin n → ℝ)=(x : Fin n → ℝ)
      simpa using he.symm
    · apply Quotient.sound
      refine ⟨-1,?_⟩
      apply Subtype.ext
      change (-1:ℤ) • (y : Fin n → ℝ)=(x : Fin n → ℝ)
      simpa using he.symm

lemma project_quotient_cover (n : ℕ) : IsQuotientCoveringMap (project n) ℤˣ :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

lemma project_covering (n : ℕ) : IsCoveringMap (project n) :=
  (project_quotient_cover n).isCoveringMap

lemma project_continuous (n : ℕ) : Continuous (project n) :=
  (project_covering n).continuous

lemma project_fiber_card (n : ℕ) (x : ProjectiveSphere n) :
    Nat.card ((project n) ⁻¹' {x})=2 := by
  obtain ⟨y,hy⟩ := (project_quotient_cover n).surjective x
  have hc := Nat.card_congr ((project_quotient_cover n).fiberEquivGroup ⟨y,hy⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units_int] using hc

lemma sphere2_iff (u : Plane) : u ∈ sphereSet 2 ↔ u ∈ unitCircle := by
  simp [sphereSet,Fin.sum_univ_two,unitCircle,planeNormSq]

lemma sphere4_iff (y : Phase) : y ∈ sphereSet 4 ↔ y ∈ unitThreeSphere := by
  simp [sphereSet,Fin.sum_univ_four,unitThreeSphere,zNormSq,wNormSq,add_assoc]

def coreSphere (u : RoundSphere 2) : RoundSphere 4 :=
  ⟨![u.val 0,u.val 1,0,0],by
    have hh := (sphere2_iff u.val).mp u.property
    apply (sphere4_iff _).mpr
    change (u.val 0)^2+(u.val 1)^2+(0^2+0^2)=1
    have hs : u.val 0^2+u.val 1^2=1 := hh
    nlinarith⟩

lemma coreSphere_continuous : Continuous coreSphere := by
  apply Continuous.subtype_mk
  change Continuous (fun u : RoundSphere 2 => ![u.val 0,u.val 1,0,0])
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun u : RoundSphere 2 => u.val 0)
    exact (continuous_apply 0).comp continuous_subtype_val
  · change Continuous (fun u : RoundSphere 2 => u.val 1)
    exact (continuous_apply 1).comp continuous_subtype_val
  · change Continuous (fun _ : RoundSphere 2 => (0:ℝ))
    exact continuous_const
  · change Continuous (fun _ : RoundSphere 2 => (0:ℝ))
    exact continuous_const

lemma coreSphere_equivariant (g : ℤˣ) (u : RoundSphere 2) :
    coreSphere (g • u)=g • coreSphere u := by
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [coreSphere,units_smul_coe]

lemma coreSphere_injective : Injective coreSphere := by
  intro u v he
  apply Subtype.ext
  have hh := congrArg Subtype.val he
  ext i
  fin_cases i
  · exact congrFun hh 0
  · exact congrFun hh 1

def coreProjective : ProjectiveSphere 2 → ProjectiveSphere 4 :=
  Quotient.map coreSphere (by
    intro u v h
    obtain ⟨g,hg⟩ := h
    change g • v=u at hg
    exact ⟨g,by change g • coreSphere v=coreSphere u; rw [← coreSphere_equivariant,hg]⟩)

lemma coreProjective_continuous : Continuous coreProjective := by
  apply continuous_quot_lift
  exact (project_continuous 4).comp coreSphere_continuous

lemma coreProjective_injective : Injective coreProjective := by
  intro x y h
  induction x using Quotient.inductionOn with | _ u =>
    induction y using Quotient.inductionOn with | _ v =>
      change project 4 (coreSphere u)=project 4 (coreSphere v) at h
      rw [project_eq_iff] at h
      apply (project_eq_iff 2 u v).mpr
      rcases h with he|he
      · left
        exact congrArg Subtype.val (coreSphere_injective (Subtype.ext he))
      · right
        ext i
        fin_cases i
        · exact congrFun he 0
        · exact congrFun he 1

lemma coreProjective_embedding : IsEmbedding coreProjective :=
  (coreProjective_continuous.isClosedEmbedding coreProjective_injective).isEmbedding

end
end ContactTopology.Projective

namespace ContactTopology.Projective
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def descend {n m : ℕ} (f : RoundSphere n → RoundSphere m)
    (hf : ∀ g : ℤˣ, ∀ x, f (g • x)=g • f x) : ProjectiveSphere n → ProjectiveSphere m :=
  Quotient.map f (by
    intro x y h
    obtain ⟨g,hg⟩ := h
    change g • y=x at hg
    exact ⟨g,by change g • f y=f x; rw [← hf,hg]⟩)

lemma descend_continuous {n m : ℕ} (f : RoundSphere n → RoundSphere m)
    (he : ∀ g : ℤˣ, ∀ x, f (g • x)=g • f x) (hc : Continuous f) :
    Continuous (descend f he) := by
  apply continuous_quot_lift
  exact (project_continuous m).comp hc

lemma equivariant_inverse {n m : ℕ} (f : RoundSphere n ≃ₜ RoundSphere m)
    (he : ∀ g : ℤˣ, ∀ x, f (g • x)=g • f x) (g : ℤˣ) (y : RoundSphere m) :
    f.symm (g • y)=g • f.symm y := by
  apply f.injective
  rw [f.apply_symm_apply,he,f.apply_symm_apply]

def descendHomeomorph {n m : ℕ} (f : RoundSphere n ≃ₜ RoundSphere m)
    (he : ∀ g : ℤˣ, ∀ x, f (g • x)=g • f x) : ProjectiveSphere n ≃ₜ ProjectiveSphere m where
  toFun := descend f he
  invFun := descend f.symm (equivariant_inverse f he)
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ y =>
      change project n (f.symm (f y))=project n y
      rw [f.symm_apply_apply]
  right_inv := by
    intro x
    induction x using Quotient.inductionOn with | _ y =>
      change project m (f (f.symm y))=project m y
      rw [f.apply_symm_apply]
  continuous_toFun := descend_continuous _ _ f.continuous
  continuous_invFun := descend_continuous _ _ f.symm.continuous

def sphereMap (F : EquivariantSphereContactomorphism) (y : RoundSphere 4) : RoundSphere 4 :=
  ⟨F.toFun y.val,(sphere4_iff _).mpr (F.maps_sphere ((sphere4_iff _).mp y.property))⟩

def sphereInvMap (F : EquivariantSphereContactomorphism) (y : RoundSphere 4) : RoundSphere 4 :=
  ⟨F.invFun y.val,(sphere4_iff _).mpr (F.inv_maps_sphere ((sphere4_iff _).mp y.property))⟩

lemma sphereMap_continuous (F : EquivariantSphereContactomorphism) : Continuous (sphereMap F) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (((F.smooth _ ((sphere4_iff _).mp y.property)).continuousAt).comp
    continuous_subtype_val.continuousAt).codRestrict _

lemma sphereInvMap_continuous (F : EquivariantSphereContactomorphism) : Continuous (sphereInvMap F) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (((F.inv_smooth _ ((sphere4_iff _).mp y.property)).continuousAt).comp
    continuous_subtype_val.continuousAt).codRestrict _

def sphereHomeomorph (F : EquivariantSphereContactomorphism) : RoundSphere 4 ≃ₜ RoundSphere 4 where
  toFun := sphereMap F
  invFun := sphereInvMap F
  left_inv y := Subtype.ext (F.left_inv _ ((sphere4_iff _).mp y.property))
  right_inv y := Subtype.ext (F.right_inv _ ((sphere4_iff _).mp y.property))
  continuous_toFun := sphereMap_continuous F
  continuous_invFun := sphereInvMap_continuous F

lemma sphereHomeomorph_equivariant (F : EquivariantSphereContactomorphism)
    (g : ℤˣ) (y : RoundSphere 4) : sphereHomeomorph F (g • y)=g • sphereHomeomorph F y := by
  obtain rfl|rfl := Int.units_eq_one_or g
  · simp
  · apply Subtype.ext
    change F.toFun ((-1:ℤ) • (y : Phase))=(-1:ℤ) • F.toFun (y : Phase)
    simpa only [neg_one_zsmul] using F.antipodal (y : Phase) ((sphere4_iff _).mp y.property)

def projectiveHomeomorph (F : EquivariantSphereContactomorphism) :
    ProjectiveSphere 4 ≃ₜ ProjectiveSphere 4 :=
  descendHomeomorph (sphereHomeomorph F) (sphereHomeomorph_equivariant F)

def knot (F : EquivariantSphereContactomorphism) : ProjectiveSphere 2 → ProjectiveSphere 4 :=
  projectiveHomeomorph F ∘ coreProjective

lemma knot_embedding (F : EquivariantSphereContactomorphism) : IsEmbedding (knot F) :=
  (projectiveHomeomorph F).isEmbedding.comp coreProjective_embedding

def knotTrace (F : EquivariantSphereContactomorphism) := range (knot F)

def boundaryCover (F : EquivariantSphereContactomorphism) : RoundSphere 2 → knotTrace F :=
  (knot_embedding F).toHomeomorph ∘ project 2

lemma boundaryCover_covering (F : EquivariantSphereContactomorphism) :
    IsCoveringMap (boundaryCover F) :=
  (project_covering 2).homeomorph_comp (knot_embedding F).toHomeomorph

lemma boundaryCover_fiber_card (F : EquivariantSphereContactomorphism) (x : knotTrace F) :
    Nat.card ((boundaryCover F) ⁻¹' {x})=2 := by
  have he := (project_quotient_cover 2).homeomorph_comp (knot_embedding F).toHomeomorph
  obtain ⟨y,hy⟩ := he.surjective x
  have hc := Nat.card_congr (he.fiberEquivGroup ⟨y,hy⟩)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units_int,boundaryCover] using hc

def closedDiskSet : Set Plane := {u | planeNormSq u ≤ 1}
abbrev ClosedDisk := closedDiskSet
abbrev OpenDisk := {u : Plane | planeNormSq u < 1}

lemma closedDisk_compact : IsCompact closedDiskSet := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (by unfold planeNormSq; fun_prop) continuous_const
  · apply (Metric.isBounded_closedBall (x := (0:Plane)) (r := 1)).subset
    intro u hu
    change u 0^2+u 1^2 ≤ 1 at hu
    rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_one_iff_abs_le_one _).mp
    fin_cases i
    · change u 0^2 ≤ 1
      nlinarith [sq_nonneg (u 1)]
    · change u 1^2 ≤ 1
      nlinarith [sq_nonneg (u 0)]

instance : CompactSpace ClosedDisk := isCompact_iff_compactSpace.mp closedDisk_compact

def diskSphere (u : Plane) : RoundSphere 4 :=
  ⟨CoreDisk.disk u,(sphere4_iff _).mpr (CoreDisk.disk_sphere u)⟩

lemma diskSphere_continuous : Continuous diskSphere :=
  CoreDisk.disk_contDiff.continuous.subtype_mk _

def diskProject : Plane → ProjectiveSphere 4 := project 4 ∘ diskSphere

lemma diskProject_continuous : Continuous diskProject :=
  (project_continuous 4).comp diskSphere_continuous

lemma diskProject_fibers (u v : Plane) (hu : planeNormSq u ≤ 1) (hv : planeNormSq v ≤ 1) :
    diskProject u=diskProject v ↔
      u=v ∨ (planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v) := by
  change project 4 (diskSphere u)=project 4 (diskSphere v) ↔ _
  rw [project_eq_iff]
  constructor
  · rintro (he|he)
    · exact Or.inl (CoreDisk.disk_injective he)
    · exact Or.inr ((CoreDisk.disk_antipodal_fibers u v hu hv).mp he)
  · rintro (rfl|he)
    · exact Or.inl rfl
    · exact Or.inr ((CoreDisk.disk_antipodal_fibers u v hu hv).mpr he)

lemma diskProject_interior_fiber (u v : Plane) (hu : planeNormSq u < 1) (hv : planeNormSq v ≤ 1) :
    diskProject u=diskProject v ↔ u=v := by
  rw [diskProject_fibers u v hu.le hv]
  constructor
  · rintro (he|he)
    · exact he
    · linarith [he.1]
  · exact Or.inl

def closedDiskProject : ClosedDisk → ProjectiveSphere 4 := fun u => diskProject u.val
def openDiskProject : OpenDisk → ProjectiveSphere 4 := fun u => diskProject u.val

lemma closedDiskProject_continuous : Continuous closedDiskProject :=
  diskProject_continuous.comp continuous_subtype_val

def diskInteriorTrace : Set (ProjectiveSphere 4) := range openDiskProject

lemma preimage_interior_trace (u : ClosedDisk) :
    closedDiskProject u ∈ diskInteriorTrace ↔ planeNormSq u.val < 1 := by
  constructor
  · rintro ⟨v,hv⟩
    have he : v.val=u.val := (diskProject_interior_fiber v.val u.val v.property u.property).mp hv
    have hv' : planeNormSq v.val < 1 := v.property
    rw [he] at hv'
    exact hv'
  · intro hu
    exact ⟨⟨u.val,hu⟩,rfl⟩

def openDiskPreimageHomeomorph :
    OpenDisk ≃ₜ closedDiskProject ⁻¹' diskInteriorTrace where
  toFun u := ⟨⟨u.val,show planeNormSq u.val ≤ 1 from (show planeNormSq u.val < 1 from u.property).le⟩,
    (preimage_interior_trace _).mpr u.property⟩
  invFun u := ⟨u.val.val,(preimage_interior_trace _).mp u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

lemma openDiskProject_embedding : IsEmbedding openDiskProject := by
  let f := diskInteriorTrace.restrictPreimage closedDiskProject
  have hc : Continuous f := by
    apply Continuous.subtype_mk
    exact closedDiskProject_continuous.comp continuous_subtype_val
  have hcl : IsClosedMap f := closedDiskProject_continuous.isClosedMap.restrictPreimage _
  have hi : Injective f := by
    intro u v he
    apply Subtype.ext
    apply Subtype.ext
    have hu : planeNormSq u.val.val < 1 := (preimage_interior_trace _).mp u.property
    have hh := congrArg Subtype.val he
    exact (diskProject_interior_fiber _ _ hu v.val.property).mp hh
  have hf : IsEmbedding f := (IsClosedEmbedding.of_continuous_injective_isClosedMap hc hi hcl).isEmbedding
  have hh := IsEmbedding.subtypeVal.comp (hf.comp openDiskPreimageHomeomorph.isEmbedding)
  convert! hh using 1

def imageDiskProject (F : EquivariantSphereContactomorphism) : Plane → ProjectiveSphere 4 :=
  projectiveHomeomorph F ∘ diskProject

lemma imageDiskProject_continuous (F : EquivariantSphereContactomorphism) : Continuous (imageDiskProject F) :=
  (projectiveHomeomorph F).continuous.comp diskProject_continuous

lemma imageDiskProject_interior_embedding (F : EquivariantSphereContactomorphism) :
    IsEmbedding (fun u : OpenDisk => imageDiskProject F u.val) :=
  (projectiveHomeomorph F).isEmbedding.comp openDiskProject_embedding

lemma imageDiskProject_boundary (F : EquivariantSphereContactomorphism) (u : RoundSphere 2) :
    imageDiskProject F u.val=(boundaryCover F u).val := by
  change projectiveHomeomorph F (project 4 (diskSphere u.val))=
    projectiveHomeomorph F (project 4 (coreSphere u))
  congr 2
  apply Subtype.ext
  exact CoreDisk.disk_boundary u.val ((sphere2_iff _).mp u.property)

lemma imageDiskProject_interior_disjoint (F : EquivariantSphereContactomorphism) (u : OpenDisk) :
    imageDiskProject F u.val ∉ knotTrace F := by
  rintro ⟨x,hx⟩
  induction x using Quotient.inductionOn with | _ v =>
    have hh := (projectiveHomeomorph F).injective hx
    change project 4 (coreSphere v)=project 4 (diskSphere u.val) at hh
    have hd : diskSphere v.val=coreSphere v :=
      Subtype.ext (CoreDisk.disk_boundary v.val ((sphere2_iff _).mp v.property))
    rw [← hd] at hh
    have hv : planeNormSq v.val=1 := (sphere2_iff _).mp v.property
    have he := (diskProject_interior_fiber u.val v.val u.property hv.le).mp hh.symm
    have hu : planeNormSq u.val < 1 := u.property
    rw [he,hv] at hu
    exact lt_irrefl _ hu

end
end ContactTopology.Projective

namespace ContactTopology.Projective
open BirkhoffGlobalSection Set Function
lemma circle_exists_angle (u : Plane) (hu : u ∈ unitCircle) :
    ∃ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x)] = u := by
  have hnorm : u 0^2+u 1^2=1 := hu
  have hlow : -1 ≤ u 0 := by nlinarith [sq_nonneg (u 1)]
  have hhigh : u 0 ≤ 1 := by nlinarith [sq_nonneg (u 1)]
  have hcos := Real.cos_arccos hlow hhigh
  have hsqrt : Real.sqrt (1-u 0^2) = |u 1| := by
    rw [show 1-u 0^2=(u 1)^2 by nlinarith,Real.sqrt_sq_eq_abs]
  by_cases hsign : 0 ≤ u 1
  · refine ⟨Real.arccos (u 0)/(2*Real.pi),?_⟩
    have ha : 2*Real.pi*(Real.arccos (u 0)/(2*Real.pi)) = Real.arccos (u 0) := by field_simp
    ext i
    fin_cases i
    · change Real.cos (2*Real.pi*(Real.arccos (u 0)/(2*Real.pi))) = u 0
      rw [ha]
      exact hcos
    · change Real.sin (2*Real.pi*(Real.arccos (u 0)/(2*Real.pi))) = u 1
      rw [ha,Real.sin_arccos,hsqrt,abs_of_nonneg hsign]
  · refine ⟨-Real.arccos (u 0)/(2*Real.pi),?_⟩
    have ha : 2*Real.pi*(-Real.arccos (u 0)/(2*Real.pi)) = -Real.arccos (u 0) := by field_simp
    ext i
    fin_cases i
    · change Real.cos (2*Real.pi*(-Real.arccos (u 0)/(2*Real.pi))) = u 0
      rw [ha,Real.cos_neg]
      exact hcos
    · change Real.sin (2*Real.pi*(-Real.arccos (u 0)/(2*Real.pi))) = u 1
      rw [ha,Real.sin_neg,Real.sin_arccos,hsqrt,abs_of_neg (lt_of_not_ge hsign),neg_neg]

end ContactTopology.Projective

namespace ContactTopology.Projective
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def doubleCircle (u : RoundSphere 2) : RoundSphere 2 :=
  ⟨![u.val 0^2-u.val 1^2,2*u.val 0*u.val 1],by
    apply (sphere2_iff _).mpr
    have hs : u.val 0^2+u.val 1^2=1 := (sphere2_iff _).mp u.property
    change (u.val 0^2-u.val 1^2)^2+(2*u.val 0*u.val 1)^2=1
    nlinarith [sq_nonneg (u.val 0^2+u.val 1^2-1)]⟩

lemma doubleCircle_continuous : Continuous doubleCircle := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun u : RoundSphere 2 => u.val 0^2-u.val 1^2)
    exact (((continuous_apply 0).comp continuous_subtype_val).pow 2).sub
      (((continuous_apply 1).comp continuous_subtype_val).pow 2)
  · change Continuous (fun u : RoundSphere 2 => 2*u.val 0*u.val 1)
    exact (continuous_const.mul ((continuous_apply 0).comp continuous_subtype_val)).mul
      ((continuous_apply 1).comp continuous_subtype_val)

lemma doubleCircle_fibers (u v : RoundSphere 2) :
    doubleCircle u=doubleCircle v ↔ u.val=v.val ∨ u.val= -v.val := by
  constructor
  · intro he
    have hh := congrArg Subtype.val he
    have h0 := congrFun hh 0
    have h1 := congrFun hh 1
    dsimp [doubleCircle] at h0 h1
    let z : ℂ := ⟨u.val 0,u.val 1⟩
    let w : ℂ := ⟨v.val 0,v.val 1⟩
    have hs : z^2=w^2 := by
      apply Complex.ext
      · simp only [pow_two,Complex.mul_re]
        dsimp [z,w]
        nlinarith
      · simp only [pow_two,Complex.mul_im]
        dsimp [z,w]
        nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hz|hz
    · left
      ext i
      fin_cases i
      · exact congrArg Complex.re hz
      · exact congrArg Complex.im hz
    · right
      ext i
      fin_cases i
      · exact congrArg Complex.re hz
      · exact congrArg Complex.im hz
  · rintro (he|he)
    · exact congrArg doubleCircle (Subtype.ext he)
    · apply Subtype.ext
      ext i
      fin_cases i <;> dsimp [doubleCircle] <;> rw [he] <;> simp

def anglePoint (t : ℝ) : RoundSphere 2 :=
  ⟨![Real.cos t,Real.sin t],by
    apply (sphere2_iff _).mpr
    change Real.cos t^2+Real.sin t^2=1
    nlinarith [Real.sin_sq_add_cos_sq t]⟩

lemma doubleCircle_anglePoint (t : ℝ) : doubleCircle (anglePoint t)=anglePoint (2*t) := by
  apply Subtype.ext
  ext i
  fin_cases i
  · change Real.cos t^2-Real.sin t^2=Real.cos (2*t)
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · change 2*Real.cos t*Real.sin t=Real.sin (2*t)
    rw [Real.sin_two_mul]
    ring

lemma doubleCircle_surjective : Surjective doubleCircle := by
  intro v
  obtain ⟨x,hx⟩ := circle_exists_angle v.val ((sphere2_iff _).mp v.property)
  refine ⟨anglePoint (Real.pi*x),?_⟩
  rw [doubleCircle_anglePoint]
  apply Subtype.ext
  change ![Real.cos (2*(Real.pi*x)),Real.sin (2*(Real.pi*x))]=v.val
  have ha : 2*(Real.pi*x)=2*Real.pi*x := by ring
  rw [ha]
  exact hx

def doubleProjective : ProjectiveSphere 2 → RoundSphere 2 :=
  Quotient.lift doubleCircle (by
    intro u v h
    apply (doubleCircle_fibers u v).mpr
    exact (project_eq_iff 2 u v).mp (Quotient.sound h))

lemma doubleProjective_continuous : Continuous doubleProjective := by
  apply continuous_quot_lift
  exact doubleCircle_continuous

lemma doubleProjective_injective : Injective doubleProjective := by
  intro x y he
  induction x using Quotient.inductionOn with | _ u =>
    induction y using Quotient.inductionOn with | _ v =>
      apply (project_eq_iff 2 u v).mpr
      exact (doubleCircle_fibers u v).mp he

lemma doubleProjective_surjective : Surjective doubleProjective := by
  intro v
  obtain ⟨u,hu⟩ := doubleCircle_surjective v
  exact ⟨project 2 u,hu⟩

def doubleHomeomorph : ProjectiveSphere 2 ≃ₜ RoundSphere 2 :=
  (doubleProjective_continuous.isClosedEmbedding doubleProjective_injective).isEmbedding.toHomeomorphOfSurjective
    doubleProjective_surjective

def clockKnot (F : EquivariantSphereContactomorphism) : RoundSphere 2 → ProjectiveSphere 4 :=
  knot F ∘ doubleHomeomorph.symm

lemma clockKnot_embedding (F : EquivariantSphereContactomorphism) : IsEmbedding (clockKnot F) :=
  (knot_embedding F).comp doubleHomeomorph.symm.isEmbedding

lemma boundaryCover_clock (F : EquivariantSphereContactomorphism) (u : RoundSphere 2) :
    (boundaryCover F u).val=clockKnot F (doubleCircle u) := by
  change knot F (project 2 u)=knot F (doubleHomeomorph.symm (doubleHomeomorph (project 2 u)))
  rw [doubleHomeomorph.symm_apply_apply]

lemma boundaryCover_angle_clock (F : EquivariantSphereContactomorphism) (t : ℝ) :
    (boundaryCover F (anglePoint t)).val=clockKnot F (anglePoint (2*t)) := by
  rw [boundaryCover_clock,doubleCircle_anglePoint]

lemma doubleCircle_clock_velocity (t : ℝ) :
    HasDerivAt (fun s : ℝ => (doubleCircle (anglePoint s)).val)
      ((2:ℝ) • circleTangent (anglePoint (2*t)).val) t := by
  have heq : (fun s : ℝ => (doubleCircle (anglePoint s)).val)=
      fun s => ![Real.cos (2*s),Real.sin (2*s)] := by
    funext s
    rw [doubleCircle_anglePoint]
    rfl
  rw [heq]
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! ((hasDerivAt_id t).const_mul 2).cos using 1 <;> dsimp [circleTangent,anglePoint] <;> ring
  · convert! ((hasDerivAt_id t).const_mul 2).sin using 1 <;> dsimp [circleTangent,anglePoint] <;> ring

lemma doubleCircle_covering : IsCoveringMap doubleCircle :=
  (project_covering 2).homeomorph_comp doubleHomeomorph

def clockBoundaryCover (F : EquivariantSphereContactomorphism) : RoundSphere 2 → range (clockKnot F) :=
  (clockKnot_embedding F).toHomeomorph ∘ doubleCircle

lemma clockBoundaryCover_covering (F : EquivariantSphereContactomorphism) :
    IsCoveringMap (clockBoundaryCover F) :=
  doubleCircle_covering.homeomorph_comp (clockKnot_embedding F).toHomeomorph

lemma clockBoundaryCover_fiber_card (F : EquivariantSphereContactomorphism) (x : range (clockKnot F)) :
    Nat.card ((clockBoundaryCover F) ⁻¹' {x})=2 := by
  have he := ((project_quotient_cover 2).homeomorph_comp doubleHomeomorph).homeomorph_comp
    (clockKnot_embedding F).toHomeomorph
  obtain ⟨y,hy⟩ := he.surjective x
  have hc := Nat.card_congr (he.fiberEquivGroup ⟨y,hy⟩)
  have heq : (clockKnot_embedding F).toHomeomorph ∘ doubleHomeomorph ∘ project 2=
      (clockKnot_embedding F).toHomeomorph ∘ doubleCircle := by
    ext u
    rfl
  rw [heq] at hc
  simpa only [Nat.card_eq_fintype_card,Fintype.card_units_int,clockBoundaryCover] using hc

lemma clockBoundaryCover_eq_boundaryCover (F : EquivariantSphereContactomorphism) (u : RoundSphere 2) :
    (clockBoundaryCover F u).val=(boundaryCover F u).val := by
  change clockKnot F (doubleCircle u)=(boundaryCover F u).val
  exact (boundaryCover_clock F u).symm

lemma clockKnot_range (F : EquivariantSphereContactomorphism) : range (clockKnot F)=knotTrace F := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨doubleHomeomorph.symm y,rfl⟩
  · rintro ⟨y,rfl⟩
    refine ⟨doubleHomeomorph y,?_⟩
    change knot F (doubleHomeomorph.symm (doubleHomeomorph y))=knot F y
    rw [doubleHomeomorph.symm_apply_apply]

def imageDiskLift (F : EquivariantSphereContactomorphism) : Plane → RoundSphere 4 :=
  sphereMap F ∘ diskSphere

lemma imageDiskLift_coe (F : EquivariantSphereContactomorphism) (u : Plane) :
    (imageDiskLift F u).val=F.toFun (CoreDisk.disk u) := rfl

lemma imageDiskLift_smooth (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (fun u => (imageDiskLift F u).val) := CoreDisk.imageDisk_contDiff F

lemma imageDiskLift_project (F : EquivariantSphereContactomorphism) (u : Plane) :
    project 4 (imageDiskLift F u)=imageDiskProject F u := rfl

lemma imageDiskLift_boundary (F : EquivariantSphereContactomorphism) (u : RoundSphere 2) :
    (clockBoundaryCover F u).val=project 4 (imageDiskLift F u.val) := by
  rw [clockBoundaryCover_eq_boundaryCover,imageDiskLift_project,imageDiskProject_boundary]

lemma imageDiskLift_interior_disjoint (F : EquivariantSphereContactomorphism) (u : OpenDisk) :
    project 4 (imageDiskLift F u.val) ∉ range (clockKnot F) := by
  rw [imageDiskLift_project,clockKnot_range]
  exact imageDiskProject_interior_disjoint F u

end
end ContactTopology.Projective

namespace ContactTopology.Projective
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

def pushLift (F : EquivariantSphereContactomorphism) (u : RoundSphere 2) : RoundSphere 4 :=
  ⟨CoreDisk.imagePushCircle F (1/2) u.val,
    (sphere4_iff _).mpr (CoreDisk.imagePushCircle_sphere F (1/2) u.val ((sphere2_iff _).mp u.property))⟩

def pushProject (F : EquivariantSphereContactomorphism) : RoundSphere 2 → ProjectiveSphere 4 :=
  project 4 ∘ pushLift F

lemma projectiveDisk_push_fibers (F : EquivariantSphereContactomorphism)
    (u : RoundSphere 2) (v : Plane) (hv : planeNormSq v ≤ 1) :
    imageDiskProject F v=pushProject F u ↔
      v=CoreDisk.diskIntersectionParameter ∧
        (u.val=CoreDisk.circleIntersectionParameter ∨ u.val= -CoreDisk.circleIntersectionParameter) := by
  change project 4 (imageDiskLift F v)=project 4 (pushLift F u) ↔ _
  rw [project_eq_iff]
  exact CoreDisk.image_fixed_push_quotient_intersection_unique F u.val v
    ((sphere2_iff _).mp u.property) hv

def intersectionPoint : ClosedDisk :=
  ⟨CoreDisk.diskIntersectionParameter,
    show planeNormSq CoreDisk.diskIntersectionParameter ≤ 1 from CoreDisk.intersection_parameter_interior.le⟩

def circleIntersectionPoint : RoundSphere 2 :=
  ⟨CoreDisk.circleIntersectionParameter,by
    apply (sphere2_iff _).mpr
    norm_num [CoreDisk.circleIntersectionParameter,unitCircle,planeNormSq]⟩

def quotientIntersections (F : EquivariantSphereContactomorphism) : Set ClosedDisk :=
  {v | ∃ u : RoundSphere 2, imageDiskProject F v.val=pushProject F u}

lemma quotientIntersections_singleton (F : EquivariantSphereContactomorphism) :
    quotientIntersections F={intersectionPoint} := by
  ext v
  constructor
  · rintro ⟨u,hu⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact ((projectiveDisk_push_fibers F u v.val v.property).mp hu).1
  · intro hv
    have he : v=intersectionPoint := Set.mem_singleton_iff.mp hv
    rw [he]
    refine ⟨circleIntersectionPoint,?_⟩
    apply (projectiveDisk_push_fibers F circleIntersectionPoint intersectionPoint.val intersectionPoint.property).mpr
    exact ⟨rfl,Or.inl rfl⟩

lemma quotientIntersections_ncard (F : EquivariantSphereContactomorphism) :
    (quotientIntersections F).ncard=1 := by
  rw [quotientIntersections_singleton,Set.ncard_singleton]

lemma quotientIntersection_negative_lift (F : EquivariantSphereContactomorphism) :
    CoreDisk.contactVolume (imageDiskLift F intersectionPoint.val).val
      (fderiv ℝ (fun v : Plane => (imageDiskLift F v).val) intersectionPoint.val ![1,0])
      (fderiv ℝ (fun v : Plane => (imageDiskLift F v).val) intersectionPoint.val ![0,1])
      (fderiv ℝ (CoreDisk.imagePushCircle F (1/2)) circleIntersectionPoint.val
        (circleTangent circleIntersectionPoint.val)) < 0 :=
  CoreDisk.image_fixed_push_intersection_sign F

end
end ContactTopology.Projective


namespace ContactTopology.RationalInvariants
open BirkhoffGlobalSection Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma direction_continuous_comp {X : Type*} [TopologicalSpace X]
    (z : X → ℂ) (hz : Continuous z) (hne : ∀ x, z x ≠ 0) :
    Continuous (fun x => direction (z x)) := by
  apply continuous_induced_rng.mpr
  have heq : (fun x => (direction (z x) : ℂ))=fun x => z x/(‖z x‖ : ℂ) := by
    funext x
    simp only [direction,dif_neg (hne x)]
  change Continuous (fun x => (direction (z x) : ℂ))
  rw [heq]
  exact hz.div (Complex.continuous_ofReal.comp hz.norm)
    (fun x => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne x)))

lemma winding_unique (f : ℝ → Circle) (k l : ℤ)
    (hk : HasWinding f k) (hl : HasWinding f l) : k=l := by
  obtain ⟨θ,hθ,hθf,hθend⟩ := hk
  obtain ⟨ψ,hψ,hψf,hψend⟩ := hl
  let d : ℝ → ℝ := fun t => (θ t-ψ t)/(2*Real.pi)
  have hd : ContinuousOn d (Icc 0 (2*Real.pi)) := (hθ.sub hψ).div_const _
  have hm : MapsTo d (Icc 0 (2*Real.pi)) (range ((↑) : ℤ → ℝ)) := by
    intro t ht
    have he := (hθf t ht).trans (hψf t ht).symm
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp he
    refine ⟨n,?_⟩
    dsimp [d]
    rw [hn]
    field_simp [Real.pi_ne_zero]
    ring
  have he := isPreconnected_Icc.constant_of_mapsTo
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range hd hm
    (show (0:ℝ) ∈ Icc 0 (2*Real.pi) from ⟨le_rfl,by positivity⟩)
    (show 2*Real.pi ∈ Icc 0 (2*Real.pi) from ⟨by positivity,le_rfl⟩)
  dsimp [d] at he
  have hh := (div_left_inj' (show (2*Real.pi:ℝ) ≠ 0 by positivity)).mp he
  have hreal : (k : ℝ)=(l : ℝ) := by nlinarith [Real.pi_pos]
  exact_mod_cast hreal

lemma rational_rotation_unique (f : ℝ → Circle) (r : ℕ) (q q' : ℚ)
    (hq : HasRationalRotation f r q) (hq' : HasRationalRotation f r q') : q=q' := by
  obtain ⟨hr,k,hk,rfl⟩ := hq
  obtain ⟨_,l,hl,rfl⟩ := hq'
  rw [winding_unique f k l hk hl]

lemma exists_continuous_angle {X : Type*} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] [Nonempty X]
    (f : X → Circle) (hf : Continuous f) :
    ∃ θ : X → ℝ, Continuous θ ∧ ∀ x, Circle.exp (θ x)=f x := by
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨a,ha⟩ := Circle.exp_surjective (f x₀)
  obtain ⟨θ,⟨hθ₀,hθ⟩,hunique⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    ⟨f,hf⟩ x₀ a ha
  exact ⟨θ,θ.continuous,fun x => congrFun hθ x⟩

lemma winding_zero_of_plane_extension (z : Plane → ℂ) (hz : Continuous z)
    (hne : ∀ u, z u ≠ 0) :
    HasWinding (fun t => direction (z ![Real.cos t,Real.sin t])) 0 := by
  obtain ⟨θ,hθ,hθf⟩ := exists_continuous_angle (fun u => direction (z u))
    (direction_continuous_comp z hz hne)
  refine ⟨fun t => θ ![Real.cos t,Real.sin t],?_,?_,?_⟩
  · apply Continuous.continuousOn
    apply hθ.comp
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  · intro t ht
    exact hθf _
  · simp [Real.cos_two_pi,Real.sin_two_pi]

lemma rational_rotation_zero_of_plane_extension (z : Plane → ℂ) (hz : Continuous z)
    (hne : ∀ u, z u ≠ 0) (r : ℕ) (hr : 0 < r) (q : ℚ) :
    HasRationalRotation (fun t => direction (z ![Real.cos t,Real.sin t])) r q ↔ q=0 := by
  have hw := winding_zero_of_plane_extension z hz hne
  constructor
  · intro hq
    have h0 : HasRationalRotation (fun t => direction (z ![Real.cos t,Real.sin t])) r 0 :=
      ⟨hr,0,hw,by simp⟩
    exact rational_rotation_unique _ r q 0 hq h0
  · rintro rfl
    exact ⟨hr,0,hw,by simp⟩

end
end ContactTopology.RationalInvariants

namespace ContactTopology.RationalInvariants
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Topology
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma contact_derivative_antipodal (F : EquivariantSphereContactomorphism)
    (y v : Phase) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v=0) :
    fderiv ℝ F.toFun (-y) (-v)= -fderiv ℝ F.toFun y v := by
  have hneg : -y ∈ unitThreeSphere := by simpa [unitThreeSphere,zNormSq,wNormSq] using hy
  have hF := (F.smooth y hy).differentiableAt (by simp)
  have hFn := (F.smooth (-y) hneg).differentiableAt (by simp)
  have hn := (hasFDerivAt_id (𝕜 := ℝ) y).neg
  have hg := hFn.hasFDerivAt.comp y hn
  have hh := hF.hasFDerivAt.neg
  have he := sphere_tangent_fderiv_eq (fun z => F.toFun (-z)) (fun z => -F.toFun z) y v hy hv
    hg.differentiableAt hh.differentiableAt F.antipodal
  have hgd := hg.fderiv
  have hhd := hh.fderiv
  change fderiv ℝ (fun z : Phase => F.toFun (-z)) y=_ at hgd
  change fderiv ℝ (fun z : Phase => -F.toFun z) y=_ at hhd
  rw [hgd,hhd] at he
  simpa using he

lemma imagePush_derivative_antipodal (F : EquivariantSphereContactomorphism)
    (s : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    fderiv ℝ (CoreDisk.imagePushCircle F s) (-u) (circleTangent (-u))=
      -fderiv ℝ (CoreDisk.imagePushCircle F s) u (circleTangent u) := by
  have hneg : -u ∈ unitCircle := by simpa [unitCircle,planeNormSq] using hu
  have hd := fderiv_comp u ((F.smooth _ (CoreDisk.pushCircle_sphere s u hu)).differentiableAt (by simp))
    (CoreDisk.pushCircleLinear s).differentiableAt
  have hdn := fderiv_comp (-u) ((F.smooth _ (CoreDisk.pushCircle_sphere s (-u) hneg)).differentiableAt (by simp))
    (CoreDisk.pushCircleLinear s).differentiableAt
  have hJ : circleTangent (-u)= -circleTangent u := by
    ext i
    fin_cases i <;> simp [circleTangent]
  change fderiv ℝ (F.toFun ∘ CoreDisk.pushCircle s) (-u) _=
    -fderiv ℝ (F.toFun ∘ CoreDisk.pushCircle s) u _
  rw [hdn,hd]
  change fderiv ℝ F.toFun (CoreDisk.pushCircle s (-u))
      (fderiv ℝ (CoreDisk.pushCircle s) (-u) (circleTangent (-u)))=
    -fderiv ℝ F.toFun (CoreDisk.pushCircle s u)
      (fderiv ℝ (CoreDisk.pushCircle s) u (circleTangent u))
  rw [CoreDisk.pushCircle_fderiv,CoreDisk.pushCircle_fderiv,hJ,
    CoreDisk.pushCircle_odd,CoreDisk.pushCircle_odd]
  exact contact_derivative_antipodal F _ _ (CoreDisk.pushCircle_sphere s u hu)
    (CoreDisk.pushCircle_tangent s u)

def tangentExtension (F : EquivariantSphereContactomorphism) (u : Plane) : Phase :=
  CoreDisk.pushVector F (CoreDisk.disk u) (CoreDisk.frameA (CoreDisk.disk u))

lemma tangentExtension_smooth (F : EquivariantSphereContactomorphism) :
    ContDiff ℝ ∞ (tangentExtension F) := CoreDisk.pushVector_smooth F _ CoreDisk.frameA_contDiff

lemma tangentExtension_nonzero (F : EquivariantSphereContactomorphism) (u : Plane) :
    tangentExtension F u ≠ 0 := by
  intro he
  have hh : (1:ℝ) • CoreDisk.pushVector F (CoreDisk.disk u) (CoreDisk.frameA (CoreDisk.disk u))+
      (0:ℝ) • CoreDisk.pushVector F (CoreDisk.disk u) (CoreDisk.frameB (CoreDisk.disk u))=0 := by
    simpa only [one_smul,zero_smul,add_zero,tangentExtension] using he
  have hc := CoreDisk.pushed_frame_independent F _ (CoreDisk.disk_sphere u) 1 0 hh
  norm_num at hc

def tangentCoordinates (F : EquivariantSphereContactomorphism) (u : Plane) : ℂ :=
  ⟨phaseDot (CoreDisk.frameA (CoreDisk.imageDisk F u)) (tangentExtension F u),
    phaseDot (CoreDisk.frameB (CoreDisk.imageDisk F u)) (tangentExtension F u)⟩

lemma tangentCoordinates_continuous (F : EquivariantSphereContactomorphism) :
    Continuous (tangentCoordinates F) := by
  have hA := CoreDisk.frameA_contDiff.comp (CoreDisk.imageDisk_contDiff F)
  have hB := CoreDisk.frameB_contDiff.comp (CoreDisk.imageDisk_contDiff F)
  have hT := tangentExtension_smooth F
  have hAc : Continuous (fun u => CoreDisk.frameA (CoreDisk.imageDisk F u)) := hA.continuous
  have hBc : Continuous (fun u => CoreDisk.frameB (CoreDisk.imageDisk F u)) := hB.continuous
  have hTc : Continuous (tangentExtension F) := hT.continuous
  have ha : Continuous (fun u => phaseDot (CoreDisk.frameA (CoreDisk.imageDisk F u)) (tangentExtension F u)) := by
    dsimp [phaseDot]
    exact (((((continuous_apply 0).comp hAc).mul ((continuous_apply 0).comp hTc)).add
      (((continuous_apply 1).comp hAc).mul ((continuous_apply 1).comp hTc))).add
      (((continuous_apply 2).comp hAc).mul ((continuous_apply 2).comp hTc))).add
      (((continuous_apply 3).comp hAc).mul ((continuous_apply 3).comp hTc))
  have hb : Continuous (fun u => phaseDot (CoreDisk.frameB (CoreDisk.imageDisk F u)) (tangentExtension F u)) := by
    dsimp [phaseDot]
    exact (((((continuous_apply 0).comp hBc).mul ((continuous_apply 0).comp hTc)).add
      (((continuous_apply 1).comp hBc).mul ((continuous_apply 1).comp hTc))).add
      (((continuous_apply 2).comp hBc).mul ((continuous_apply 2).comp hTc))).add
      (((continuous_apply 3).comp hBc).mul ((continuous_apply 3).comp hTc))
  convert! (Complex.continuous_ofReal.comp ha).add
    ((Complex.continuous_ofReal.comp hb).mul (continuous_const (y := Complex.I))) using 1
  ext u <;> simp [tangentCoordinates,Complex.ext_iff]

lemma tangentCoordinates_nonzero (F : EquivariantSphereContactomorphism) (u : Plane) :
    tangentCoordinates F u ≠ 0 := by
  intro he
  have ha : phaseDot (CoreDisk.frameA (CoreDisk.imageDisk F u)) (tangentExtension F u)=0 :=
    congrArg Complex.re he
  have hb : phaseDot (CoreDisk.frameB (CoreDisk.imageDisk F u)) (tangentExtension F u)=0 :=
    congrArg Complex.im he
  have hh := CoreDisk.pushed_frame_contact F _ (CoreDisk.disk_sphere u)
  have hr := CoreDisk.contact_frame_spans (CoreDisk.imageDisk F u) (tangentExtension F u)
    (CoreDisk.imageDisk_sphere F u) hh.1 hh.2.2.1
  rw [ha,hb,zero_smul,zero_smul,add_zero] at hr
  exact tangentExtension_nonzero F u hr

lemma tangentCoordinates_boundary (F : EquivariantSphereContactomorphism)
    (u : Plane) (hu : u ∈ unitCircle) :
    tangentCoordinates F u=
      ⟨phaseDot (CoreDisk.frameA (CoreDisk.imageDisk F u))
          (fderiv ℝ (CoreDisk.imageDisk F) u (circleTangent u)),
        phaseDot (CoreDisk.frameB (CoreDisk.imageDisk F u))
          (fderiv ℝ (CoreDisk.imageDisk F) u (circleTangent u))⟩ := by
  unfold tangentCoordinates
  rw [CoreDisk.pushed_boundary_tangent F u hu]
  rfl

lemma core_rational_rotation (F : EquivariantSphereContactomorphism) (q : ℚ) :
    HasRationalRotation
      (fun t => direction (tangentCoordinates F ![Real.cos t,Real.sin t])) 2 q ↔ q=0 :=
  rational_rotation_zero_of_plane_extension (tangentCoordinates F)
    (tangentCoordinates_continuous F) (tangentCoordinates_nonzero F) 2 (by norm_num) q

def boundaryTangentCoordinates (F : EquivariantSphereContactomorphism) (t : ℝ) : ℂ :=
  let u : Plane := ![Real.cos t,Real.sin t]
  ⟨phaseDot (CoreDisk.frameA (CoreDisk.imageDisk F u))
      (fderiv ℝ (CoreDisk.imageDisk F) u (circleTangent u)),
    phaseDot (CoreDisk.frameB (CoreDisk.imageDisk F u))
      (fderiv ℝ (CoreDisk.imageDisk F) u (circleTangent u))⟩

lemma boundaryTangentCoordinates_eq (F : EquivariantSphereContactomorphism) (t : ℝ) :
    boundaryTangentCoordinates F t=tangentCoordinates F ![Real.cos t,Real.sin t] :=
  (tangentCoordinates_boundary F _ (CoreDisk.circlePoint_mem t)).symm

lemma boundaryTangentCoordinates_nonzero (F : EquivariantSphereContactomorphism) (t : ℝ) :
    boundaryTangentCoordinates F t ≠ 0 := by
  rw [boundaryTangentCoordinates_eq]
  exact tangentCoordinates_nonzero F _

lemma core_rational_rotation_boundary (F : EquivariantSphereContactomorphism) (q : ℚ) :
    HasRationalRotation (fun t => direction (boundaryTangentCoordinates F t)) 2 q ↔ q=0 := by
  have heq : (fun t => direction (boundaryTangentCoordinates F t))=
      fun t => direction (tangentCoordinates F ![Real.cos t,Real.sin t]) := by
    funext t
    rw [boundaryTangentCoordinates_eq]
  rw [heq]
  exact core_rational_rotation F q

lemma core_intersection_set (F : EquivariantSphereContactomorphism) :
    quotientIntersectionSet (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2))=
      {CoreDisk.diskIntersectionParameter} := by
  ext v
  constructor
  · rintro ⟨hv,u,hu,he⟩
    exact ((CoreDisk.image_fixed_push_quotient_intersection_unique F u v hu hv).mp he).1
  · intro hv
    have he : v=CoreDisk.diskIntersectionParameter := hv
    rw [he]
    refine ⟨CoreDisk.intersection_parameter_interior.le,CoreDisk.circleIntersectionParameter,?_,Or.inl ?_⟩
    · norm_num [CoreDisk.circleIntersectionParameter,unitCircle,planeNormSq]
    · exact congrArg F.toFun CoreDisk.fixed_push_intersection

lemma core_representative_sign (F : EquivariantSphereContactomorphism) (v u : Plane)
    (hv : v ∈ quotientIntersectionSet (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2)))
    (hu : u ∈ unitCircle)
    (he : CoreDisk.imageDisk F v=CoreDisk.imagePushCircle F (1/2) u ∨
      CoreDisk.imageDisk F v= -CoreDisk.imagePushCircle F (1/2) u) :
    representativeSign (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2)) v u= -1 := by
  have hmatch := (CoreDisk.image_fixed_push_quotient_intersection_unique F u v hu hv.1).mp he
  obtain ⟨rfl,hu'|hu'⟩ := hmatch
  · rw [hu']
    have hp : CoreDisk.imageDisk F CoreDisk.diskIntersectionParameter=
        CoreDisk.imagePushCircle F (1/2) CoreDisk.circleIntersectionParameter :=
      congrArg F.toFun CoreDisk.fixed_push_intersection
    unfold representativeSign
    rw [if_pos hp]
    exact if_pos (CoreDisk.image_fixed_push_intersection_sign F)
  · rw [hu']
    have hp : CoreDisk.imageDisk F CoreDisk.diskIntersectionParameter=
        CoreDisk.imagePushCircle F (1/2) CoreDisk.circleIntersectionParameter :=
      congrArg F.toFun CoreDisk.fixed_push_intersection
    have hcircle : CoreDisk.circleIntersectionParameter ∈ unitCircle := by
      norm_num [CoreDisk.circleIntersectionParameter,unitCircle,planeNormSq]
    have hneq : CoreDisk.imageDisk F CoreDisk.diskIntersectionParameter ≠
        CoreDisk.imagePushCircle F (1/2) (-CoreDisk.circleIntersectionParameter) := by
      rw [CoreDisk.imagePushCircle_odd F (1/2) _ hcircle,← hp]
      intro h
      exact Projective.sphere_not_neg_self 4
        (Projective.imageDiskLift F CoreDisk.diskIntersectionParameter) h.symm
    unfold representativeSign
    rw [if_neg hneq,imagePush_derivative_antipodal F (1/2) _ hcircle,neg_neg]
    exact if_pos (CoreDisk.image_fixed_push_intersection_sign F)

lemma core_intersection_sign (F : EquivariantSphereContactomorphism) :
    quotientIntersectionSign (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2))
      CoreDisk.diskIntersectionParameter= -1 := by
  classical
  have hv : CoreDisk.diskIntersectionParameter ∈
      quotientIntersectionSet (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2)) := by
    rw [core_intersection_set]
    exact Set.mem_singleton _
  unfold quotientIntersectionSign
  rw [dif_pos hv]
  obtain ⟨hu,he⟩ := Classical.choose_spec hv.2
  exact core_representative_sign F _ _ hv hu he

lemma core_algebraic_intersection (F : EquivariantSphereContactomorphism)
    (h : (quotientIntersectionSet (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2))).Finite) :
    algebraicIntersection (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2)) h= -1 := by
  classical
  have hf : h.toFinset={CoreDisk.diskIntersectionParameter} := by
    ext v
    simp only [Set.Finite.mem_toFinset,Finset.mem_singleton]
    rw [core_intersection_set]
    rfl
  unfold algebraicIntersection
  rw [hf,Finset.sum_singleton,core_intersection_sign]

lemma core_normalized_intersection (F : EquivariantSphereContactomorphism)
    (h : (quotientIntersectionSet (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2))).Finite) :
    normalizedIntersection (CoreDisk.imageDisk F) (CoreDisk.imagePushCircle F (1/2)) 2 h= -1/2 := by
  unfold normalizedIntersection
  rw [core_algebraic_intersection]
  norm_num

end
end ContactTopology.RationalInvariants
open BirkhoffGlobalSection ContactTopology.RationalInvariants Set Function
open scoped ContDiff
theorem solution
    (F : EquivariantSphereContactomorphism) :
    let D : Plane → Phase := fun u =>
      ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
        (1-planeNormSq u)/(1+planeNormSq u),0]
    let G : Plane → Phase := F.toFun ∘ D
    let A : Phase → Phase := fun y => ![-y 1,y 0,y 3,-y 2]
    let B : Phase → Phase := fun y => ![y 3,-y 2,y 1,-y 0]
    let P : ℝ → Plane → Phase := fun s u =>
      ((1-s^2)/(1+s^2)) • ![u 0,u 1,0,0]+(2*s/(1+s^2)) • B ![u 0,u 1,0,0]
    let γ : Plane → Phase := F.toFun ∘ P (1/2)
    let c : ℝ → Plane := fun t => ![Real.cos t,Real.sin t]
    let z : ℝ → ℂ := fun t =>
      ⟨phaseDot (A (G (c t))) (fderiv ℝ G (c t) (circleTangent (c t))),
        phaseDot (B (G (c t))) (fderiv ℝ G (c t) (circleTangent (c t)))⟩
    quotientIntersectionSet G γ={![0,1/3]} ∧
    (∀ v u : Plane, v ∈ quotientIntersectionSet G γ → u ∈ unitCircle →
      (G v=γ u ∨ G v= -γ u) → representativeSign G γ v u= -1) ∧
    (quotientIntersectionSet G γ).Finite ∧
    (∀ h : (quotientIntersectionSet G γ).Finite,
      algebraicIntersection G γ h= -1 ∧ normalizedIntersection G γ 2 h= -1/2) ∧
    (∀ t : ℝ, z t ≠ 0) ∧
    (∀ q : ℚ, HasRationalRotation (fun t => direction (z t)) 2 q ↔ q=0) := by
  refine ⟨core_intersection_set F,core_representative_sign F,?_,
    fun h => ⟨core_algebraic_intersection F h,core_normalized_intersection F h⟩,
    boundaryTangentCoordinates_nonzero F,core_rational_rotation_boundary F⟩
  change (quotientIntersectionSet (ContactTopology.CoreDisk.imageDisk F)
    (ContactTopology.CoreDisk.imagePushCircle F (1/2))).Finite
  rw [core_intersection_set]
  exact Set.finite_singleton _
