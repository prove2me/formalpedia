-- Prove2me | solution 2 for BirkhoffGlobalSection.convex_model_transports_transverse_hopf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T00:10:29.471113+00:00
-- url     : https://prove2.me/submissions/af88f296-89be-471e-a9fa-e87e123a314f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_BirkhoffGlobalSection_convex_model_transverse_hopf_contact_transfer
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactTopology_equivariant_legendrian_core_alignment
import Theorems.Thm_ContactTopology_equivariant_legendrian_core_fixing_preserves_hopf


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


namespace ContactTopology.SphereContactAlgebra
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphere_neg {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

def compose (F G : EquivariantSphereContactomorphism) : EquivariantSphereContactomorphism where
  toFun := F.toFun ∘ G.toFun
  invFun := G.invFun ∘ F.invFun
  smooth := fun y hy => (F.smooth _ (G.maps_sphere hy)).comp y (G.smooth y hy)
  inv_smooth := fun y hy => (G.inv_smooth _ (F.inv_maps_sphere hy)).comp y (F.inv_smooth y hy)
  maps_sphere := fun y hy => F.maps_sphere (G.maps_sphere hy)
  inv_maps_sphere := fun y hy => G.inv_maps_sphere (F.inv_maps_sphere hy)
  left_inv := by
    intro y hy
    change G.invFun (F.invFun (F.toFun (G.toFun y))) = y
    rw [F.left_inv _ (G.maps_sphere hy),G.left_inv y hy]
  right_inv := by
    intro y hy
    change F.toFun (G.toFun (G.invFun (F.invFun y))) = y
    rw [G.right_inv _ (F.inv_maps_sphere hy),F.right_inv y hy]
  antipodal := by
    intro y hy
    change F.toFun (G.toFun (-y)) = -F.toFun (G.toFun y)
    rw [G.antipodal y hy,F.antipodal _ (G.maps_sphere hy)]
  contact := by
    intro y hy
    obtain ⟨a,ha,hF⟩ := F.contact _ (G.maps_sphere hy)
    obtain ⟨b,hb,hG⟩ := G.contact y hy
    refine ⟨a*b,mul_pos ha hb,?_⟩
    intro v hv
    have htan := sphere_map_fderiv_tangent G.toFun y v hy hv
      ((G.smooth y hy).differentiableAt (by simp)) G.maps_sphere
    have hd := fderiv_comp y ((F.smooth _ (G.maps_sphere hy)).differentiableAt (by simp))
      ((G.smooth y hy).differentiableAt (by simp))
    change phaseRadialContact (F.toFun (G.toFun y)) (fderiv ℝ (F.toFun ∘ G.toFun) y v) = _
    rw [hd]
    change phaseRadialContact (F.toFun (G.toFun y)) (fderiv ℝ F.toFun (G.toFun y) (fderiv ℝ G.toFun y v)) = _
    rw [hF _ htan,hG v hv]
    ring

def inverse (F : EquivariantSphereContactomorphism) : EquivariantSphereContactomorphism where
  toFun := F.invFun
  invFun := F.toFun
  smooth := F.inv_smooth
  inv_smooth := F.smooth
  maps_sphere := F.inv_maps_sphere
  inv_maps_sphere := F.maps_sphere
  left_inv := F.right_inv
  right_inv := F.left_inv
  antipodal := by
    intro y hy
    have hx := F.inv_maps_sphere hy
    calc
      F.invFun (-y) = F.invFun (-F.toFun (F.invFun y)) := by rw [F.right_inv y hy]
      _ = F.invFun (F.toFun (-F.invFun y)) := by rw [F.antipodal _ hx]
      _ = -F.invFun y := F.left_inv _ (sphere_neg hx)
  contact := by
    intro y hy
    have hx := F.inv_maps_sphere hy
    obtain ⟨a,ha,hc⟩ := F.contact _ hx
    refine ⟨a⁻¹,inv_pos.mpr ha,?_⟩
    intro v hv
    have hw := sphere_map_fderiv_tangent F.invFun y v hy hv
      ((F.inv_smooth y hy).differentiableAt (by simp)) F.inv_maps_sphere
    have hdf := (F.smooth _ hx).differentiableAt (by simp)
    have hdi := (F.inv_smooth y hy).differentiableAt (by simp)
    have heq := sphere_tangent_fderiv_eq (F.toFun ∘ F.invFun) id y v hy hv
      (hdf.comp y hdi) differentiableAt_id F.right_inv
    rw [fderiv_comp y hdf hdi] at heq
    have hder : fderiv ℝ F.toFun (F.invFun y) (fderiv ℝ F.invFun y v) = v := by simpa using heq
    have hh := hc (fderiv ℝ F.invFun y v) hw
    rw [F.right_inv y hy,hder] at hh
    calc
      phaseRadialContact (F.invFun y) (fderiv ℝ F.invFun y v) = phaseRadialContact y v/a :=
        (eq_div_iff ha.ne').mpr (by nlinarith [hh])
      _ = _ := by ring

def isotopy_congr (F G : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F)
    (heq : ∀ y ∈ unitThreeSphere, F.toFun y = G.toFun y) :
    EquivariantSphereContactIsotopy G where
  slice := I.slice
  smooth := I.smooth
  start := I.start
  finish := fun y hy => (I.finish y hy).trans (heq y hy)

def isotopy_compose (F G : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) (J : EquivariantSphereContactIsotopy G) :
    EquivariantSphereContactIsotopy (compose F G) where
  slice := fun t => compose (I.slice t) (J.slice t)
  smooth := by
    intro t ht y hy
    have hxy := (J.slice t).maps_sphere hy
    exact (I.smooth t ht _ hxy).comp (t,y) (contDiffAt_fst.prodMk (J.smooth t ht y hy))
  start := by
    intro y hy
    change (I.slice 0).toFun ((J.slice 0).toFun y) = y
    rw [J.start y hy,I.start y hy]
  finish := by
    intro y hy
    change (I.slice 1).toFun ((J.slice 1).toFun y) = F.toFun (G.toFun y)
    rw [I.finish _ ((J.slice 1).maps_sphere hy),J.finish y hy]

/-- Reversing the path and composing with the fixed endpoint inverse avoids
assuming joint smoothness of the inverses of an arbitrary isotopy. -/
def isotopy_inverse (F : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy F) : EquivariantSphereContactIsotopy (inverse F) where
  slice := fun t => compose (inverse F) (I.slice (1-t))
  smooth := by
    intro t ht y hy
    have hs : 1-t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hclock : ContDiffAt ℝ ∞ (fun q : ℝ × Phase => (1-q.1,q.2)) (t,y) :=
      (contDiffAt_const.sub contDiffAt_fst).prodMk contDiffAt_snd
    have hI := (I.smooth (1-t) hs y hy).comp (t,y) hclock
    exact (F.inv_smooth _ ((I.slice (1-t)).maps_sphere hy)).comp (t,y) hI
  start := by
    intro y hy
    change F.invFun ((I.slice (1-0)).toFun y) = y
    rw [sub_zero,I.finish y hy,F.left_inv y hy]
  finish := by
    intro y hy
    change F.invFun ((I.slice (1-1)).toFun y) = F.invFun y
    rw [sub_self,I.start y hy]

end
end ContactTopology.SphereContactAlgebra

namespace BirkhoffGlobalSection.ContactGenerator
open BirkhoffGlobalSection Set
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


end
end BirkhoffGlobalSection.ContactGenerator


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma circle_sphere_map_fderiv_tangent (k : Plane → Phase)
    (hk : ∀ u ∈ unitCircle, DifferentiableAt ℝ k u)
    (hsphere : MapsTo k unitCircle unitThreeSphere) (u : Plane) (hu : u ∈ unitCircle) :
    phaseDot (k u) (fderiv ℝ k u (circleTangent u)) = 0 := by
  have hku : DifferentiableAt ℝ k (ContactGenerator.circleCurve u 0) := by
    rw [ContactGenerator.circleCurve_zero]
    exact hk u hu
  have hc : HasDerivAt (fun s => k (ContactGenerator.circleCurve u s))
      (fderiv ℝ k u (circleTangent u)) 0 := by
    convert! hku.hasFDerivAt.comp_hasDerivAt 0 (ContactGenerator.circleCurve_hasDerivAt u) using 1
    simp only [ContactGenerator.circleCurve_zero]
  have hd := dot_self_hasDerivAt hc
  have heq : (fun s => phaseDot (k (ContactGenerator.circleCurve u s)) (k (ContactGenerator.circleCurve u s))) =
      fun _ => (1:ℝ) := by
    funext s
    exact sphere_dot_self (hsphere (ContactGenerator.circleCurve_mem u hu s))
  rw [heq] at hd
  have he := hd.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [ContactGenerator.circleCurve_zero] at he
  linarith


end
end BirkhoffGlobalSection.HopfTransport


namespace BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma contact_isotopy_transports_hopf {K : Set Phase}
    (F : EquivariantSphereContactomorphism) (C : EquivariantSphereContactIsotopy F)
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by
  let J : ℝ × Plane → Phase := fun p => (C.slice p.1).toFun (I.isotopy p)
  have hslice : ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      DifferentiableAt ℝ (fun w => I.isotopy (t,w)) u := by
    intro t ht u hu
    exact ((I.smooth t ht u hu).comp u (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  refine ⟨{
    isotopy := J
    smooth := ?_
    sphere := ?_
    injective := ?_
    antipodal := ?_
    positive := ?_
    start := ?_
    finish := ?_ }⟩
  · intro t ht u hu
    exact (C.smooth t ht (I.isotopy (t,u)) (I.sphere t ht u hu)).comp (t,u)
      (contDiffAt_fst.prodMk (I.smooth t ht u hu))
  · intro t ht u hu
    exact (C.slice t).maps_sphere (I.sphere t ht u hu)
  · intro t ht u hu v hv he
    have hh := congrArg (C.slice t).invFun he
    have heq : I.isotopy (t,u) = I.isotopy (t,v) := by
      simpa only [J,(C.slice t).left_inv _ (I.sphere t ht u hu),(C.slice t).left_inv _ (I.sphere t ht v hv)] using hh
    exact I.injective t ht hu hv heq
  · intro t ht u hu
    change (C.slice t).toFun (I.isotopy (t,-u)) = -(C.slice t).toFun (I.isotopy (t,u))
    rw [I.antipodal t ht u hu,(C.slice t).antipodal _ (I.sphere t ht u hu)]
  · intro t ht u hu
    have hku := hslice t ht u hu
    have hFu := ((C.slice t).smooth _ (I.sphere t ht u hu)).differentiableAt (by simp)
    have htan := circle_sphere_map_fderiv_tangent (fun w => I.isotopy (t,w))
      (hslice t ht) (fun w hw => I.sphere t ht w hw) u hu
    obtain ⟨a,ha,hcontact⟩ := (C.slice t).contact _ (I.sphere t ht u hu)
    change 0 < phaseRadialContact ((C.slice t).toFun (I.isotopy (t,u)))
      (fderiv ℝ ((C.slice t).toFun ∘ fun w => I.isotopy (t,w)) u (circleTangent u))
    rw [fderiv_comp u hFu hku]
    change 0 < phaseRadialContact ((C.slice t).toFun (I.isotopy (t,u)))
      (fderiv ℝ (C.slice t).toFun (I.isotopy (t,u)) (fderiv ℝ (fun w => I.isotopy (t,w)) u (circleTangent u)))
    rw [hcontact _ htan]
    exact mul_pos ha (I.positive t ht u hu)
  · intro u hu
    change (C.slice 0).toFun (I.isotopy (0,u)) = standardHopfCircle u
    rw [C.start _ (I.sphere 0 ⟨le_rfl,by norm_num⟩ u hu),I.start u hu]
  · calc
      (fun u => J (1,u)) '' unitCircle = (fun u => F.toFun (I.isotopy (1,u))) '' unitCircle := by
        apply Set.image_congr
        intro u hu
        exact C.finish _ (I.sphere 1 ⟨by norm_num,le_rfl⟩ u hu)
      _ = F.toFun '' K := by
        change (F.toFun ∘ fun u => I.isotopy (1,u)) '' unitCircle = _
        rw [Set.image_comp,I.finish]

end
end BirkhoffGlobalSection.HopfTransport
open BirkhoffGlobalSection Set
theorem solution
    (μ c : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (M : ConvexRegularizationModel μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ)
    (γ : PeriodicOrbit φ)
    (hI : Nonempty (EquivariantTransverseHopfIsotopy (radialNormalize '' orbitSet γ))) :
    Nonempty (EquivariantTransverseHopfIsotopy
      (radialNormalize '' (M.toModel '' orbitSet γ))) := by
  obtain ⟨K,F,⟨I⟩,himage⟩ := convex_model_transverse_hopf_contact_transfer μ c hμ0 hμ1 hc M φ hφ γ hI
  obtain ⟨A,⟨IA⟩,hcore⟩ := ContactTopology.equivariant_legendrian_core_alignment F
  let G := ContactTopology.SphereContactAlgebra.compose A F
  obtain ⟨J⟩ := ContactTopology.equivariant_legendrian_core_fixing_preserves_hopf G hcore I
  have hh := HopfTransport.contact_isotopy_transports_hopf
    (ContactTopology.SphereContactAlgebra.inverse A)
    (ContactTopology.SphereContactAlgebra.isotopy_inverse A IA) J
  have hKs : K ⊆ unitThreeSphere := by
    rw [← I.finish]
    rintro y ⟨u,hu,rfl⟩
    exact I.sphere 1 ⟨zero_le_one,le_rfl⟩ u hu
  have heq : (ContactTopology.SphereContactAlgebra.inverse A).toFun '' (G.toFun '' K) = F.toFun '' K := by
    rw [← Set.image_comp]
    apply Set.image_congr
    intro y hy
    exact A.left_inv _ (F.maps_sphere (hKs hy))
  rw [heq,himage] at hh
  exact hh
