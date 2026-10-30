-- Prove2me | solution 1 for ContactTopology.equivariant_legendrian_core_fixing_preserves_hopf
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T00:10:16.189453+00:00
-- url     : https://prove2.me/submissions/66c776b1-a097-43c9-9a43-9726d65c3f2e

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_BirkhoffGlobalSection_transverse_isotopy_contact_generator
import Theorems.Thm_ContactTopology_equivariant_legendrian_neighborhood_fixing
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
import Theorems.Thm_FlowCalculus_uniform_spatial_lipschitz_of_compact_support
import Theorems.Thm_GrayStability_pullback_family_hasDerivAt
import Theorems.Thm_ParameterizedCalculus_smooth_scalar_linear_transport


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


open BirkhoffGlobalSection GrayStability
open scoped ContDiff Topology

namespace BirkhoffGlobalSection.IsotopyExtension

/-- The round sphere as the zero level of `|y|² - 1`. -/
noncomputable def sphereEq : E 4 → (Fin 1 → ℝ) := fun y _ => zNormSq y + wNormSq y - 1

lemma mem_levelSet_sphereEq {y : Phase} : y ∈ levelSet sphereEq ↔ y ∈ unitThreeSphere := by
  change sphereEq y = 0 ↔ zNormSq y + wNormSq y = 1
  constructor
  · intro h
    have := congrFun h 0
    simp only [sphereEq, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [sphereEq, Pi.zero_apply, h, sub_self]

/-- The derivative of the squared norm. -/
noncomputable def normSqDeriv (y : Phase) : Phase →L[ℝ] ℝ :=
  (2 * y 0) • ContinuousLinearMap.proj 0 + (2 * y 1) • ContinuousLinearMap.proj 1 +
    (2 * y 2) • ContinuousLinearMap.proj 2 + (2 * y 3) • ContinuousLinearMap.proj 3

lemma normSqDeriv_apply (y v : Phase) : normSqDeriv y v = 2 * phaseDot y v := by
  simp [normSqDeriv, phaseDot]
  ring

lemma hasFDerivAt_normSq (y : Phase) :
    HasFDerivAt (fun x : Phase => zNormSq x + wNormSq x) (normSqDeriv y) y := by
  have hp := fun i : Fin 4 =>
    (hasFDerivAt_apply (𝕜 := ℝ) i y).mul (hasFDerivAt_apply (𝕜 := ℝ) i y)
  have hN := ((hp 0).add (hp 1)).add ((hp 2).add (hp 3))
  refine (hN.congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · refine ContinuousLinearMap.ext fun v => ?_
    simp [normSqDeriv]
    ring
  · simp [zNormSq, wNormSq]
    ring

lemma hasFDerivAt_sphereEq (y : Phase) :
    HasFDerivAt sphereEq (ContinuousLinearMap.pi fun _ : Fin 1 => normSqDeriv y) y :=
  hasFDerivAt_pi.2 fun _ => (hasFDerivAt_normSq y).sub_const 1

lemma mem_tangentSpace_sphereEq {y v : Phase} :
    v ∈ tangentSpace sphereEq y ↔ phaseDot y v = 0 := by
  change fderiv ℝ sphereEq y v = 0 ↔ phaseDot y v = 0
  rw [(hasFDerivAt_sphereEq y).fderiv]
  constructor
  · intro h
    have := congrFun h 0
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply] at this
    linarith
  · intro h
    funext i
    simp only [ContinuousLinearMap.pi_apply, normSqDeriv_apply, Pi.zero_apply, h, mul_zero]

lemma sphereEq_regular : IsCompactRegularLevel sphereEq := by
  refine ⟨?_, ?_, ?_⟩
  · refine contDiff_pi.2 fun _ => ?_
    show ContDiff ℝ ∞ (fun y : Phase => zNormSq y + wNormSq y - 1)
    unfold zNormSq wNormSq
    fun_prop
  · have hset : levelSet sphereEq = unitThreeSphere := Set.ext fun y => mem_levelSet_sphereEq
    rw [hset]
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by unfold zNormSq wNormSq; fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Phase)) (r := 1)).subset fun y hy => ?_
      have h : zNormSq y + wNormSq y = 1 := hy
      simp only [zNormSq, wNormSq] at h
      have h0 : y 0 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 1), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h1 : y 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 2), sq_nonneg (y 3)]
      have h2 : y 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 3)]
      have h3 : y 3 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1), sq_nonneg (y 2)]
      rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      refine (sq_le_one_iff_abs_le_one _).1 ?_
      fin_cases i
      exacts [h0, h1, h2, h3]
  · intro y hy w
    have hy' : zNormSq y + wNormSq y = 1 := mem_levelSet_sphereEq.1 hy
    have hyy : phaseDot y y = 1 := by
      simp only [zNormSq, wNormSq] at hy'
      simp only [phaseDot]
      linarith [hy']
    refine ⟨(w 0 / 2) • y, ?_⟩
    rw [(hasFDerivAt_sphereEq y).fderiv]
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp only [ContinuousLinearMap.pi_apply, map_smul, normSqDeriv_apply, smul_eq_mul, hyy]
    ring

/-- The radial contact form `λ_y(v) = -ω(y,v)/2` as a linear family of covectors. -/
noncomputable def radialForm : Phase →L[ℝ] (Phase →L[ℝ] ℝ) :=
  (-(1 / 2 : ℝ)) •
    ((ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 2 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 0 : Phase →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ) -
      (ContinuousLinearMap.proj 3 : Phase →L[ℝ] ℝ).smulRight
        (ContinuousLinearMap.proj 1 : Phase →L[ℝ] ℝ))

lemma radialForm_apply (y v : Phase) : radialForm y v = phaseRadialContact y v := by
  simp [radialForm, phaseRadialContact, phaseSymplecticForm]
  ring


end BirkhoffGlobalSection.IsotopyExtension


open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.HopfTransport
noncomputable section

lemma smooth_inverse_of_bijective_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f) (hb : Function.Bijective f)
    (hi : ∀ x, Function.Injective (fderiv ℝ f x)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E → E ≃L[ℝ] E := fun x => (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap
    ⟨hi x,LinearMap.injective_iff_surjective.mp (hi x)⟩).toContinuousLinearEquiv
  have hd : ∀ x, HasFDerivAt f (L x : E →L[ℝ] E) x := by
    intro x
    exact (hf.differentiable (by simp) x).hasFDerivAt
  have ho : IsOpenMap f := isOpenMap_of_hasStrictFDerivAt_equiv
    (fun x => hf.contDiffAt.hasStrictFDerivAt' (hd x) (by simp))
  let H : E ≃ₜ E := (Equiv.ofBijective f hb).toHomeomorphOfContinuousOpen hf.continuous ho
  have hH : ContDiff ℝ ∞ (H : E → E) := hf
  have hHd : ∀ x, HasFDerivAt (H : E → E) (L x : E →L[ℝ] E) x := hd
  exact ⟨H.symm,H.contDiff_symm hHd hH,H.symm_apply_apply,H.apply_symm_apply⟩

lemma smooth_joint_flow_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hb : ∀ t, Function.Bijective (ψ t))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t) :
    ∃ ρ : ℝ → V → V, ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let F : ℝ × V → ℝ × V := fun p => (p.1,ψ p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hψ
  have hFb : Function.Bijective F := by
    constructor
    · intro p q he
      change (p.1,ψ p.1 p.2) = (q.1,ψ q.1 q.2) at he
      have ht := congrArg (fun z : ℝ × V => z.1) he
      have hy := congrArg (fun z : ℝ × V => z.2) he
      refine Prod.ext ht ?_
      apply (hb p.1).1
      change ψ p.1 p.2 = ψ q.1 q.2 at hy
      rw [← ht] at hy
      exact hy
    · rintro ⟨t,y⟩
      obtain ⟨x,hx⟩ := (hb t).2 y
      exact ⟨(t,x),Prod.ext rfl hx⟩
  have hFi : ∀ p, Function.Injective (fderiv ℝ F p) := by
    intro p
    have hfd := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk ((hψ.differentiable (by simp) p).hasFDerivAt)
    change HasFDerivAt F _ p at hfd
    have hslice := ((hψ.differentiable (by simp) p).hasFDerivAt).comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    change HasFDerivAt (ψ p.1) _ p.2 at hslice
    have hsi := FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hd p.1 p.2
    intro v w he
    rw [hfd.fderiv] at he
    change (v.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v) =
      (w.1,(fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w) at he
    have ht := congrArg (fun z : ℝ × V => z.1) he
    have hy := congrArg (fun z : ℝ × V => z.2) he
    have hz : (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) (0,v.2-w.2) = 0 := by
      change (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) v =
        (fderiv ℝ (fun q : ℝ × V => ψ q.1 q.2) p) w at hy
      have hsub := sub_eq_zero.mpr hy
      rw [← map_sub] at hsub
      have hvw : v-w = (0,v.2-w.2) := by
        apply Prod.ext
        · exact sub_eq_zero.mpr ht
        · rfl
      rw [hvw] at hsub
      exact hsub
    refine Prod.ext ht ?_
    have hsz : fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0 := by
      change fderiv ℝ (ψ p.1) p.2 (v.2-w.2) = 0
      rw [hslice.fderiv]
      exact hz
    have hzv : v.2-w.2 = 0 := hsi (by simpa only [map_zero] using hsz)
    exact sub_eq_zero.mp hzv
  obtain ⟨G,hG,hGF,hFG⟩ := smooth_inverse_of_bijective_derivative F hF hFb hFi
  have hGt : ∀ t y, (G (t,y)).1 = t := by
    intro t y
    exact congrArg Prod.fst (hFG (t,y))
  refine ⟨fun t y => (G (t,y)).2,contDiff_snd.comp hG,?_,?_⟩
  · intro t y
    exact congrArg Prod.snd (hGF (t,y))
  · intro t y
    have he := congrArg Prod.snd (hFG (t,y))
    simpa only [F,hGt] using he

end
end BirkhoffGlobalSection.HopfTransport

namespace ContactTopology
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport BirkhoffGlobalSection.IsotopyExtension GrayStability Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- Integrate a compact odd contact generator to a jointly smooth flow and
inverse, with positive contact pullback throughout the unit interval. -/
lemma integrate_equivariant_contact_generator (X : ℝ → Phase → Phase) (mu : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hmu : ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hodd : ∀ t y, X t (-y) = -X t y)
    (htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0)
    (hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) = mu t y*phaseRadialContact y v) :
    ∃ psi rho : ℝ → Phase → Phase, ∃ lam : ℝ → Phase → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × Phase => psi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Phase => rho p.1 p.2) ∧
      (∀ y, psi 0 y = y) ∧
      (∀ t y, rho t (psi t y) = y) ∧ (∀ t y, psi t (rho t y) = y) ∧
      (∀ t y, psi t (-y) = -psi t y) ∧
      (∀ t y, HasDerivAt (fun s => psi s y) (X t (psi t y)) t) ∧
      (∀ t ∈ Icc (0:ℝ) 1, MapsTo (psi t) unitThreeSphere unitThreeSphere) ∧
      (∀ t ∈ Icc (0:ℝ) 1, MapsTo (rho t) unitThreeSphere unitThreeSphere) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, 0 < lam t y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
        phaseRadialContact (psi t y) (fderiv ℝ (psi t) y v) = lam t y*phaseRadialContact y v := by
  obtain ⟨psi,hpsi,h0,hbij,hflow,hiso,hDpsi⟩ := FlowCalculus.compact_supported_flow_preserves_regular_level
    sphereEq sphereEq_regular X hX hsupp (by
      intro t ht y hy
      exact mem_tangentSpace_sphereEq.mpr (htan t ht y (mem_levelSet_sphereEq.mp hy)))
  obtain ⟨rho,hrho,hrp,hpr⟩ := smooth_joint_flow_inverse X psi hX hpsi h0 hbij hflow
  have hpsiodd : ∀ t y, psi t (-y) = -psi t y := by
    intro t y
    have hp : (fun s => psi s (-y)) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => psi r (-y)) (X s (psi s (-y))) s := ⟨h0 (-y),fun s => hflow s (-y)⟩
    have hn : (fun s => -psi s y) 0 = -y ∧
        ∀ s, HasDerivAt (fun r => -psi r y) (X s (-psi s y)) s := by
      constructor
      · change -psi 0 y = -y
        rw [h0]
      · intro s
        rw [hodd]
        convert! (hflow s y).neg using 1
    have hh : (fun s => psi s (-y)) = fun s => -psi s y := by
      apply (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 (-y)).unique
      · convert! hp using 1
      · convert! hn using 1
    exact congrFun hh t
  have hmaps : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (psi t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    exact mem_levelSet_sphereEq.mp ((hiso.2.2 t ht).1.mapsTo (mem_levelSet_sphereEq.mpr hy))
  have hrhomaps : ∀ t ∈ Icc (0:ℝ) 1, MapsTo (rho t) unitThreeSphere unitThreeSphere := by
    intro t ht y hy
    obtain ⟨z,hz,hzmap⟩ := (hiso.2.2 t ht).1.surjOn (mem_levelSet_sphereEq.mpr hy)
    rw [← hzmap,hrp]
    exact mem_levelSet_sphereEq.mp hz
  let rate : ℝ → Phase → ℝ := fun t y => mu t (psi t y)
  have hrate : ContDiff ℝ ∞ (fun p : ℝ × Phase => rate p.1 p.2) := hmu.comp (contDiff_fst.prodMk hpsi)
  obtain ⟨lam,hlam,hlam0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport rate hrate
  refine ⟨psi,rho,lam,hpsi,hrho,h0,hrp,hpr,hpsiodd,hflow,hmaps,hrhomaps,fun t ht y hy => hpos t y,?_⟩
  intro t ht y hy v hv
  have hsmooth : IsSmoothFamily (fun _ : ℝ => (radialForm : OneForm 4)) :=
    radialForm.contDiff.comp contDiff_snd
  have hf : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r => phaseRadialContact (psi r y) (fderiv ℝ (psi r) y v))
        (rate s y*phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v)) s := by
    intro s hs
    have hz := hmaps s hs hy
    have hw := mem_tangentSpace_sphereEq.mp
      (hDpsi s hs y (mem_levelSet_sphereEq.mpr hy) v (mem_tangentSpace_sphereEq.mpr hv))
    have hd := GrayStability.pullback_family_hasDerivAt (fun _ => (radialForm : OneForm 4)) hsmooth
      X hX psi hpsi h0 hbij hflow s y v
    have hval : formTimeDeriv (fun _ : ℝ => (radialForm : OneForm 4)) s (psi s y) (fderiv ℝ (psi s) y v)+
        lieDerivOneForm (X s) radialForm (psi s y) (fderiv ℝ (psi s) y v) =
        rate s y*phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v) := by
      simp only [formTimeDeriv,lieDerivOneForm,deriv_const,ContinuousLinearMap.fderiv,
        radialForm_apply,zero_add,rate]
      exact hlie s hs _ hz _ hw
    rw [hval] at hd
    convert! hd using 1 <;> simp [pullback,radialForm_apply]
  have hinit : phaseRadialContact (psi 0 y) (fderiv ℝ (psi 0) y v) = phaseRadialContact y v := by
    have hid : psi 0 = id := funext h0
    simp [hid]
  simpa only [hinit] using htransport y
    (fun s => phaseRadialContact (psi s y) (fderiv ℝ (psi s) y v)) hf t ht

lemma contact_generator_flow_isotopy (X : ℝ → Phase → Phase) (mu : ℝ → Phase → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × Phase => X p.1 p.2))
    (hmu : ContDiff ℝ ∞ (fun p : ℝ × Phase => mu p.1 p.2))
    (hsupp : ∃ C : Set Phase, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0)
    (hodd : ∀ t y, X t (-y) = -X t y)
    (htan : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, phaseDot y (X t y) = 0)
    (hlie : ∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere, ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (X t y) v+phaseRadialContact y (fderiv ℝ (X t) y v) = mu t y*phaseRadialContact y v) :
    ∃ F : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy F) ∧
      ∃ psi : ℝ → Phase → Phase, F.toFun = psi 1 ∧ (∀ y, psi 0 y = y) ∧
        ∀ t y, HasDerivAt (fun s => psi s y) (X t (psi t y)) t := by
  obtain ⟨psi,rho,lam,hpsi,hrho,h0,hrp,hpr,hoddpsi,hflow,hmaps,hrhomaps,hpos,hcontact⟩ :=
    integrate_equivariant_contact_generator X mu hX hmu hsupp hodd htan hlie
  let sig : ℝ → ℝ := fun t => Real.smoothTransition t
  have hsig : ContDiff ℝ ∞ sig := Real.smoothTransition.contDiff (n := (⊤:ℕ∞))
  have hsigmem : ∀ t, sig t ∈ Icc (0:ℝ) 1 := fun t => ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  let C : ℝ → EquivariantSphereContactomorphism := fun t =>
    { toFun := psi (sig t)
      invFun := rho (sig t)
      smooth := fun y hy => (hpsi.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
      inv_smooth := fun y hy => (hrho.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
      maps_sphere := hmaps _ (hsigmem t)
      inv_maps_sphere := hrhomaps _ (hsigmem t)
      left_inv := fun y hy => hrp _ y
      right_inv := fun y hy => hpr _ y
      antipodal := fun y hy => hoddpsi _ y
      contact := fun y hy => ⟨lam (sig t) y,hpos _ (hsigmem t) y hy,hcontact _ (hsigmem t) y hy⟩ }
  have hs0 : sig 0 = 0 := Real.smoothTransition.zero_of_nonpos (by norm_num)
  have hs1 : sig 1 = 1 := Real.smoothTransition.one_of_one_le (by norm_num)
  refine ⟨C 1,⟨{slice := C,smooth := ?_,start := ?_,finish := ?_}⟩,psi,?_,h0,hflow⟩
  · intro t ht y hy
    exact (hpsi.comp ((hsig.comp contDiff_fst).prodMk contDiff_snd)).contDiffAt
  · intro y hy
    change psi (sig 0) y = y
    rw [hs0,h0]
  · intro y hy
    rfl
  · change psi (sig 1) = psi 1
    rw [hs1]

end
end ContactTopology


namespace ContactTopology.HopfPushOff
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def splitCircle (a b : ℝ) (u : Plane) : Phase :=
  ![Real.cos a*u 0,Real.cos b*u 1,-Real.sin b*u 1,Real.sin a*u 0]

def splitCircleLinear (a b : ℝ) : Plane →L[ℝ] Phase :=
  LinearMap.toContinuousLinearMap
    { toFun := splitCircle a b
      map_add' := by intro u v; ext i; fin_cases i <;> simp [splitCircle] <;> ring
      map_smul' := by intro r u; ext i; fin_cases i <;> simp [splitCircle] <;> ring }

lemma splitCircle_fderiv (a b : ℝ) (u v : Plane) :
    fderiv ℝ (splitCircle a b) u v = splitCircle a b v := by
  change fderiv ℝ (splitCircleLinear a b) u v = splitCircleLinear a b v
  exact congrArg (fun L : Plane →L[ℝ] Phase => L v) ((splitCircleLinear a b).hasFDerivAt (x := u)).fderiv

lemma splitCircle_injective (a b : ℝ) : Injective (splitCircle a b) := by
  have hleft (u : Plane) :
      ![Real.cos a*(splitCircle a b u) 0+Real.sin a*(splitCircle a b u) 3,
        Real.cos b*(splitCircle a b u) 1-Real.sin b*(splitCircle a b u) 2] = u := by
    ext i
    fin_cases i
    · change Real.cos a*(Real.cos a*u 0)+Real.sin a*(Real.sin a*u 0) = u 0
      calc
        _ = (Real.cos a^2+Real.sin a^2)*u 0 := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
    · change Real.cos b*(Real.cos b*u 1)-Real.sin b*(-Real.sin b*u 1) = u 1
      calc
        _ = (Real.cos b^2+Real.sin b^2)*u 1 := by ring
        _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  intro u v he
  have hh := congrArg (fun y : Phase =>
    ![Real.cos a*y 0+Real.sin a*y 3,Real.cos b*y 1-Real.sin b*y 2]) he
  simpa only [hleft] using hh

lemma splitCircle_sphere (a b : ℝ) (u : Plane) (hu : u ∈ unitCircle) :
    splitCircle a b u ∈ unitThreeSphere := by
  change u 0^2+u 1^2=1 at hu
  dsimp [unitThreeSphere,zNormSq,wNormSq,splitCircle]
  linear_combination (u 0)^2*(Real.cos_sq_add_sin_sq a)+
    (u 1)^2*(Real.cos_sq_add_sin_sq b)+hu

lemma splitCircle_contact (a b : ℝ) (u : Plane) :
    phaseRadialContact (splitCircle a b u)
      (fderiv ℝ (splitCircle a b) u (circleTangent u)) =
      Real.sin (a+b)/2*planeNormSq u := by
  rw [splitCircle_fderiv,Real.sin_add]
  simp [splitCircle,phaseRadialContact,phaseSymplecticForm,circleTangent,planeNormSq]
  ring

def pushOffFamily (d : ℝ) (p : ℝ × Plane) : Phase :=
  splitCircle (p.1*d) ((1-p.1)*(Real.pi/2)+p.1*d) p.2

lemma pushOffFamily_contDiff (d : ℝ) : ContDiff ℝ ∞ (pushOffFamily d) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [pushOffFamily,splitCircle] <;> fun_prop

lemma pushOffFamily_start (d : ℝ) (u : Plane) :
    pushOffFamily d (0,u) = standardHopfCircle u := by
  ext i
  fin_cases i <;> simp [pushOffFamily,splitCircle,standardHopfCircle]

lemma pushOffFamily_finish (d : ℝ) (u : Plane) :
    pushOffFamily d (1,u) = splitCircle d d u := by simp [pushOffFamily]

lemma pushOffFamily_positive (d : ℝ) (hd : 0 < d) (hdpi : d < Real.pi/4)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (u : Plane) (hu : u ∈ unitCircle) :
    0 < phaseRadialContact (pushOffFamily d (t,u))
      (fderiv ℝ (fun v => pushOffFamily d (t,v)) u (circleTangent u)) := by
  change 0 < phaseRadialContact (splitCircle (t*d) ((1-t)*(Real.pi/2)+t*d) u)
    (fderiv ℝ (splitCircle (t*d) ((1-t)*(Real.pi/2)+t*d)) u (circleTangent u))
  rw [splitCircle_contact,show planeNormSq u=1 from hu,mul_one]
  have hgap : 0 < Real.pi/2-2*d := by linarith
  have hlo : 0 < t*d+((1-t)*(Real.pi/2)+t*d) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hgap.le]
  have hhi : t*d+((1-t)*(Real.pi/2)+t*d) < Real.pi := by
    nlinarith [mul_nonneg ht.1 hgap.le,Real.pi_pos]
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi hlo hhi) (by norm_num)

 def pushOffIsotopy (d : ℝ) (hd : 0 < d) (hdpi : d < Real.pi/4) :
    EquivariantTransverseHopfIsotopy ((splitCircle d d) '' unitCircle) where
  isotopy := pushOffFamily d
  smooth := fun t ht u hu => (pushOffFamily_contDiff d).contDiffAt
  sphere := fun t ht u hu => splitCircle_sphere _ _ u hu
  injective := fun t ht => (splitCircle_injective (t*d) ((1-t)*(Real.pi/2)+t*d)).injOn
  antipodal := by
    intro t ht u hu
    ext i
    fin_cases i <;> simp [pushOffFamily,splitCircle]
  positive := pushOffFamily_positive d hd hdpi
  start := fun u hu => pushOffFamily_start d u
  finish := by
    apply image_congr
    intro u hu
    exact pushOffFamily_finish d u

lemma unitCircle_compact : IsCompact unitCircle := by
  have hp : Continuous planeNormSq := by unfold planeNormSq; fun_prop
  have hc : IsClosed unitCircle := isClosed_eq hp continuous_const
  apply (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hc
  intro u hu
  have he : u 0^2+u 1^2=1 := hu
  have h0 : |u 0| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]
  have h1 : |u 1| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (u 0),sq_nonneg (u 1)]
  have hi : ∀ i : Fin 2, ‖u i‖ ≤ 1 := by intro i; fin_cases i <;> assumption
  have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).mpr hi
  simpa [Metric.mem_closedBall,dist_zero_right] using hn

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

lemma exists_small_pushOff_in_neighborhood (O : Set Phase) (hO : IsOpen O)
    (hcore : ∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O) :
    ∃ d : ℝ, 0 < d ∧ d < Real.pi/4 ∧ ∀ u ∈ unitCircle, splitCircle d d u ∈ O := by
  have hcont : Continuous (fun p : ℝ × Plane => splitCircle p.1 p.1 p.2) := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [splitCircle] <;> fun_prop
  have hzero : ∀ u ∈ unitCircle, splitCircle 0 0 u ∈ O := by
    intro u hu
    obtain ⟨x,hx⟩ := circle_exists_angle u hu
    have hux : u 0=Real.cos (2*Real.pi*x) := (congrFun hx 0).symm
    have huy : u 1=Real.sin (2*Real.pi*x) := (congrFun hx 1).symm
    simpa [splitCircle,hux,huy] using hcore x
  have hev : ∀ᶠ d : ℝ in 𝓝 0, ∀ u ∈ unitCircle, splitCircle d d u ∈ O :=
    unitCircle_compact.eventually_forall_of_forall_eventually
      (fun u hu => hcont.continuousAt.preimage_mem_nhds (hO.mem_nhds (hzero u hu)))
  obtain ⟨e,he,hesub⟩ := Metric.mem_nhds_iff.mp hev
  let d : ℝ := min e (Real.pi/4)/2
  have hmin : 0 < min e (Real.pi/4) := lt_min he (by positivity)
  have hd : 0 < d := half_pos hmin
  have hde : d < e := by dsimp [d]; linarith [min_le_left e (Real.pi/4)]
  have hdpi : d < Real.pi/4 := by dsimp [d]; linarith [min_le_right e (Real.pi/4)]
  refine ⟨d,hd,hdpi,hesub ?_⟩
  simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hd] using hde

end
end ContactTopology.HopfPushOff

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

namespace ContactTopology.SphereContactAlgebra
open BirkhoffGlobalSection Set
open scoped ContDiff
noncomputable section

def isotopy_conjugate (H D : EquivariantSphereContactomorphism)
    (I : EquivariantSphereContactIsotopy D) :
    EquivariantSphereContactIsotopy (compose H (compose D (inverse H))) where
  slice := fun t => compose H (compose (I.slice t) (inverse H))
  smooth := by
    intro t ht y hy
    have hci : ContDiffAt ℝ ∞ (fun p : ℝ × Phase => H.invFun p.2) (t,y) :=
      (H.inv_smooth y hy).comp (t,y) contDiffAt_snd
    have hI := (I.smooth t ht _ (H.inv_maps_sphere hy)).comp (t,y)
      (contDiffAt_fst.prodMk hci)
    exact (H.smooth _ ((I.slice t).maps_sphere (H.inv_maps_sphere hy))).comp (t,y) hI
  start := by
    intro y hy
    change H.toFun ((I.slice 0).toFun (H.invFun y)) = y
    rw [I.start _ (H.inv_maps_sphere hy),H.right_inv y hy]
  finish := by
    intro y hy
    change H.toFun ((I.slice 1).toFun (H.invFun y)) = H.toFun (D.toFun (H.invFun y))
    rw [I.finish _ (H.inv_maps_sphere hy)]

end
end ContactTopology.SphereContactAlgebra

namespace ContactTopology.HopfPushOff
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport ContactTopology.SphereContactAlgebra Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma standardHopf_sphere (u : Plane) (hu : u ∈ unitCircle) :
    standardHopfCircle u ∈ unitThreeSphere := by
  simpa [splitCircle,standardHopfCircle] using splitCircle_sphere 0 (Real.pi/2) u hu

lemma contact_isotopy_realizes_transverse_endpoint {K : Set Phase}
    (I : EquivariantTransverseHopfIsotopy K) :
    ∃ D : EquivariantSphereContactomorphism, Nonempty (EquivariantSphereContactIsotopy D) ∧
      ∀ u ∈ unitCircle, D.toFun (standardHopfCircle u) = I.isotopy (1,u) := by
  obtain ⟨X,mu,hX,hmu,hsupp,hodd,htan,hlie,hvel⟩ := transverse_isotopy_contact_generator K I
  obtain ⟨D,hDiso,psi,hD,h0,hflow⟩ :=
    ContactTopology.contact_generator_flow_isotopy X mu hX hmu hsupp hodd htan hlie
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX hsupp 0 1
  refine ⟨D,hDiso,?_⟩
  intro u hu
  have hb : ∀ t ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun s => I.isotopy (s,u)) (X t (I.isotopy (t,u))) t := by
    intro t ht
    rw [hvel t ht u hu]
    exact ((I.smooth t ht u hu).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t u))
  have heq := ODE_solution_unique_of_mem_Icc_right (v := X) (s := fun _ => univ) (K := L)
    (f := fun t => psi t (I.isotopy (0,u))) (g := fun t => I.isotopy (t,u))
    (fun t ht => (hL t (Ico_subset_Icc_self ht)).lipschitzOnWith)
    (HasDerivAt.continuousOn fun t ht => hflow t _)
    (fun t ht => (hflow t _).hasDerivWithinAt) (fun t ht => trivial)
    (HasDerivAt.continuousOn fun t ht => hb t ht)
    (fun t ht => (hb t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (fun t ht => trivial)
    (by simp [h0])
  rw [hD,← I.start u hu]
  exact heq ⟨zero_le_one,le_rfl⟩

lemma contact_fixing_hopf_preserves_class {K : Set Phase}
    (F : EquivariantSphereContactomorphism)
    (hfix : ∀ u ∈ unitCircle, F.toFun (standardHopfCircle u) = standardHopfCircle u)
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by
  have hslice : ∀ t ∈ Icc (0:ℝ) 1, ∀ u ∈ unitCircle,
      DifferentiableAt ℝ (fun w => I.isotopy (t,w)) u := by
    intro t ht u hu
    exact ((I.smooth t ht u hu).comp u (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  refine ⟨{
    isotopy := fun p => F.toFun (I.isotopy p)
    smooth := ?_
    sphere := ?_
    injective := ?_
    antipodal := ?_
    positive := ?_
    start := ?_
    finish := ?_ }⟩
  · intro t ht u hu
    exact (F.smooth _ (I.sphere t ht u hu)).comp (t,u) (I.smooth t ht u hu)
  · intro t ht u hu
    exact F.maps_sphere (I.sphere t ht u hu)
  · intro t ht u hu v hv he
    have hh := congrArg F.invFun he
    rw [F.left_inv _ (I.sphere t ht u hu),F.left_inv _ (I.sphere t ht v hv)] at hh
    exact I.injective t ht hu hv hh
  · intro t ht u hu
    rw [I.antipodal t ht u hu,F.antipodal _ (I.sphere t ht u hu)]
  · intro t ht u hu
    have hku := hslice t ht u hu
    have hFu := (F.smooth _ (I.sphere t ht u hu)).differentiableAt (by simp)
    have htan := circle_sphere_map_fderiv_tangent (fun w => I.isotopy (t,w))
      (hslice t ht) (fun w hw => I.sphere t ht w hw) u hu
    obtain ⟨a,ha,hcontact⟩ := F.contact _ (I.sphere t ht u hu)
    change 0 < phaseRadialContact (F.toFun (I.isotopy (t,u)))
      (fderiv ℝ (F.toFun ∘ fun w => I.isotopy (t,w)) u (circleTangent u))
    rw [fderiv_comp u hFu hku]
    change 0 < phaseRadialContact (F.toFun (I.isotopy (t,u)))
      (fderiv ℝ F.toFun (I.isotopy (t,u)) (fderiv ℝ (fun w => I.isotopy (t,w)) u (circleTangent u)))
    rw [hcontact _ htan]
    exact mul_pos ha (I.positive t ht u hu)
  · intro u hu
    rw [I.start u hu,hfix u hu]
  · change (F.toFun ∘ fun u => I.isotopy (1,u)) '' unitCircle = _
    rw [Set.image_comp,I.finish]

lemma contact_agreeing_on_hopf_preserves_class {K : Set Phase}
    (F E : EquivariantSphereContactomorphism) (IE : EquivariantSphereContactIsotopy E)
    (hagree : ∀ u ∈ unitCircle, E.toFun (standardHopfCircle u) = F.toFun (standardHopfCircle u))
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by
  let P := compose (inverse E) F
  have hP : ∀ u ∈ unitCircle, P.toFun (standardHopfCircle u) = standardHopfCircle u := by
    intro u hu
    change E.invFun (F.toFun (standardHopfCircle u)) = standardHopfCircle u
    rw [← hagree u hu,E.left_inv _ (standardHopf_sphere u hu)]
  obtain ⟨J⟩ := contact_fixing_hopf_preserves_class P hP I
  have hh := contact_isotopy_transports_hopf E IE J
  have hKs : K ⊆ unitThreeSphere := by
    rw [← I.finish]
    rintro y ⟨u,hu,rfl⟩
    exact I.sphere 1 ⟨zero_le_one,le_rfl⟩ u hu
  have himage : E.toFun '' (P.toFun '' K) = F.toFun '' K := by
    rw [← Set.image_comp]
    apply image_congr
    intro y hy
    change E.toFun (E.invFun (F.toFun y)) = F.toFun y
    exact E.right_inv _ (F.maps_sphere (hKs hy))
  rwa [himage] at hh

lemma contact_fixing_legendrian_neighborhood_preserves_hopf {K : Set Phase}
    (H : EquivariantSphereContactomorphism)
    (O : Set Phase) (hO : IsOpen O)
    (hcore : ∀ x : ℝ, ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] ∈ O)
    (hfix : ∀ y ∈ O ∩ unitThreeSphere, H.toFun y=y)
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (H.toFun '' K)) := by
  obtain ⟨d,hd,hdpi,hsmall⟩ := exists_small_pushOff_in_neighborhood O hO hcore
  obtain ⟨D,⟨ID⟩,hD⟩ := contact_isotopy_realizes_transverse_endpoint (pushOffIsotopy d hd hdpi)
  have hDpush : ∀ u ∈ unitCircle, D.toFun (standardHopfCircle u) = splitCircle d d u := by
    intro u hu
    rw [hD u hu]
    exact pushOffFamily_finish d u
  have hHfix : ∀ u ∈ unitCircle, H.toFun (D.toFun (standardHopfCircle u)) = D.toFun (standardHopfCircle u) := by
    intro u hu
    rw [hDpush u hu]
    exact hfix _ ⟨hsmall u hu,splitCircle_sphere d d u hu⟩
  let E := compose (compose H (compose (inverse D) (inverse H))) D
  let IE : EquivariantSphereContactIsotopy E :=
    isotopy_compose _ _ (isotopy_conjugate H (inverse D) (isotopy_inverse D ID)) ID
  apply contact_agreeing_on_hopf_preserves_class H E IE ?_ I
  intro u hu
  have hs := D.maps_sphere (standardHopf_sphere u hu)
  have hh := congrArg H.invFun (hHfix u hu)
  rw [H.left_inv _ hs] at hh
  change H.toFun (D.invFun (H.invFun (D.toFun (standardHopfCircle u)))) = H.toFun (standardHopfCircle u)
  rw [← hh,D.left_inv _ (standardHopf_sphere u hu)]

lemma contact_fixing_legendrian_core_preserves_hopf {K : Set Phase}
    (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ, F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
      ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0])
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by
  obtain ⟨B,⟨IB⟩,O,hO,hOcore,hfix⟩ := ContactTopology.equivariant_legendrian_neighborhood_fixing F hcore
  let H := compose B F
  obtain ⟨J⟩ := contact_fixing_legendrian_neighborhood_preserves_hopf H O hO hOcore hfix I
  have hh := contact_isotopy_transports_hopf (inverse B) (isotopy_inverse B IB) J
  have hKs : K ⊆ unitThreeSphere := by
    rw [← I.finish]
    rintro y ⟨u,hu,rfl⟩
    exact I.sphere 1 ⟨zero_le_one,le_rfl⟩ u hu
  have heq : (inverse B).toFun '' (H.toFun '' K) = F.toFun '' K := by
    rw [← Set.image_comp]
    apply image_congr
    intro y hy
    exact B.left_inv _ (F.maps_sphere (hKs hy))
  rwa [heq] at hh

end
end ContactTopology.HopfPushOff
open BirkhoffGlobalSection Set
theorem solution {K : Set Phase}
    (F : EquivariantSphereContactomorphism)
    (hcore : ∀ x : ℝ, F.toFun ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0] =
      ![Real.cos (2*Real.pi*x),Real.sin (2*Real.pi*x),0,0])
    (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (EquivariantTransverseHopfIsotopy (F.toFun '' K)) := by
  exact ContactTopology.HopfPushOff.contact_fixing_legendrian_core_preserves_hopf F hcore I
