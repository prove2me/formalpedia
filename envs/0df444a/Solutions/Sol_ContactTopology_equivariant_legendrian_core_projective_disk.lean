-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_projective_disk
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T02:32:18.858313+00:00
-- url     : https://prove2.me/submissions/d002dd91-9136-4a4c-b8e9-a6ca3432cb51

import Definitions.Def_ContactTopology_AntipodalSphereQuotients
import Mathlib.Topology.Covering.Quotient
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

open BirkhoffGlobalSection ContactTopology.Projective Set Function Topology
open scoped ContDiff
theorem solution
    (F : EquivariantSphereContactomorphism) :
    let D : Plane → Phase := fun u =>
      ![2*u 0/(1+planeNormSq u),2*u 1/(1+planeNormSq u),
        (1-planeNormSq u)/(1+planeNormSq u),0]
    ∃ L : Plane → RoundSphere 4,
    ∃ K : RoundSphere 2 → ProjectiveSphere 4,
    ∃ p : RoundSphere 2 → range K,
    ∃ δ : RoundSphere 2 → RoundSphere 2,
    ∃ c : ℝ → RoundSphere 2,
      ContDiff ℝ ∞ (fun u => (L u).val) ∧
      (∀ u, (L u).val=F.toFun (D u)) ∧
      Continuous (fun u => project 4 (L u)) ∧
      IsCompact {u : Plane | planeNormSq u ≤ 1} ∧
      IsEmbedding K ∧
      IsEmbedding (fun u : {u : Plane | planeNormSq u < 1} => project 4 (L u.val)) ∧
      (∀ u : {u : Plane | planeNormSq u < 1}, project 4 (L u.val) ∉ range K) ∧
      (∀ u v : Plane, planeNormSq u ≤ 1 → planeNormSq v ≤ 1 →
        (project 4 (L u)=project 4 (L v) ↔
          u=v ∨ (planeNormSq u=1 ∧ planeNormSq v=1 ∧ u= -v))) ∧
      IsCoveringMap p ∧
      (∀ x : range K, Nat.card (p ⁻¹' {x})=2) ∧
      (∀ u : RoundSphere 2, (p u).val=project 4 (L u.val)) ∧
      (∀ u : RoundSphere 2, (p u).val=K (δ u)) ∧
      (∀ u : RoundSphere 2, (δ u).val=![u.val 0^2-u.val 1^2,2*u.val 0*u.val 1]) ∧
      (∀ t : ℝ, (c t).val=![Real.cos t,Real.sin t]) ∧
      (∀ t : ℝ, δ (c t)=c (2*t)) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => (δ (c s)).val)
        ((2:ℝ) • circleTangent (c (2*t)).val) t) := by
  refine ⟨imageDiskLift F,clockKnot F,clockBoundaryCover F,doubleCircle,anglePoint,
    imageDiskLift_smooth F,imageDiskLift_coe F,?_,closedDisk_compact,
    clockKnot_embedding F,?_,imageDiskLift_interior_disjoint F,?_,
    clockBoundaryCover_covering F,clockBoundaryCover_fiber_card F,
    imageDiskLift_boundary F,?_,fun _ => rfl,fun _ => rfl,
    doubleCircle_anglePoint,doubleCircle_clock_velocity⟩
  · exact imageDiskProject_continuous F
  · exact imageDiskProject_interior_embedding F
  · intro u v hu hv
    change imageDiskProject F u=imageDiskProject F v ↔ _
    change projectiveHomeomorph F (diskProject u)=projectiveHomeomorph F (diskProject v) ↔ _
    rw [(projectiveHomeomorph F).injective.eq_iff]
    exact diskProject_fibers u v hu hv
  · intro u
    rfl
