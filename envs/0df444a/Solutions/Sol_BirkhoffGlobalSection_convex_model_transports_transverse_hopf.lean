-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_transports_transverse_hopf
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T22:12:26.682408+00:00
-- url     : https://prove2.me/submissions/c612e832-527c-4390-8765-ce5f5a8b6802
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Theorems.Thm_BirkhoffGlobalSection_convex_model_transverse_hopf_contact_transfer
import Theorems.Thm_BirkhoffGlobalSection_equivariant_sphere_contact_group_connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

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


end
end BirkhoffGlobalSection.HopfTransport


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


open BirkhoffGlobalSection

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
  obtain ⟨C⟩ := equivariant_sphere_contact_group_connected F
  have hh := HopfTransport.contact_isotopy_transports_hopf F C I
  rwa [himage] at hh
