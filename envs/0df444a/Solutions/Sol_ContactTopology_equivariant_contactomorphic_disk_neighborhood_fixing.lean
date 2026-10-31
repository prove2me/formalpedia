-- Prove2me | solution 1 for ContactTopology.equivariant_contactomorphic_disk_neighborhood_fixing
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:35:25.418734+00:00
-- url     : https://prove2.me/submissions/da37a9b4-4691-4dbc-a0a7-457a71ee18ab

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_GrayStability_Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood
import Theorems.Thm_ContactTopology_local_fixed_surface_contact_field_homotopy
import Theorems.Thm_ContactTopology_relative_compact_contact_embedding_isotopy_extension
import Theorems.Thm_FlowCalculus_compact_supported_flow_preserves_regular_level
import Theorems.Thm_FlowCalculus_exists_unique_global_trajectory_of_compact_support
import Theorems.Thm_FlowCalculus_regular_level_trajectory_invariant
import Theorems.Thm_FlowCalculus_smooth_flow_spatial_derivative_injective
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



open Set Function
open scoped Topology
set_option autoImplicit false

/-- A thin neighborhood of a compact set can overlap its symmetric image only
inside a prescribed open neighborhood of the original overlap. -/
theorem support_neighborhood_separation {X : Type*} [TopologicalSpace X] [T2Space X]
    (σ : X → X) (hσ : Continuous σ) (D V : Set X) (hD : IsCompact D) (hV : IsOpen V)
    (hoverlap : D ∩ (σ '' D) ⊆ V) :
    ∃ U : Set X, IsOpen U ∧ D ⊆ U ∧ Disjoint (U \ V) (σ '' U) := by
  have hK : IsCompact (D \ V) := hD.diff hV
  have hdis : Disjoint (D \ V) (σ '' D) := by
    apply Set.disjoint_left.mpr
    intro x hx hxσ
    exact hx.2 (hoverlap ⟨hx.1,hxσ⟩)
  obtain ⟨A,B,hA,hB,hKA,hDB,hAB⟩ := SeparatedNhds.of_isCompact_isCompact hK (hD.image hσ) hdis
  let U := (A ∪ V) ∩ σ ⁻¹' B
  have hU : IsOpen U := (hA.union hV).inter (hB.preimage hσ)
  have hDU : D ⊆ U := by
    intro x hx
    refine ⟨?_,hDB ⟨x,hx,rfl⟩⟩
    by_cases hxV : x ∈ V
    · exact Or.inr hxV
    · exact Or.inl (hKA ⟨hx,hxV⟩)
  refine ⟨U,hU,hDU,Set.disjoint_left.mpr ?_⟩
  intro x hx hxσ
  obtain ⟨y,hy,hxy⟩ := hxσ
  have hxA : x ∈ A := hx.1.1.resolve_right hx.2
  have hxB : x ∈ B := by rw [← hxy]; exact hy.2
  exact Set.disjoint_left.mp hAB hxA hxB

theorem involutive_support_separation {X : Type*} [TopologicalSpace X] [T2Space X]
    (σ : X → X) (hσ : Continuous σ) (hi : Involutive σ)
    (D V : Set X) (hD : IsCompact D) (hV : IsOpen V) (hoverlap : D ∩ (σ '' D) ⊆ V) :
    ∃ U : Set X, IsOpen U ∧ D ⊆ U ∧ ∀ C : Set X, C ⊆ U \ V →
      Disjoint C (σ '' U) ∧ Disjoint U (σ '' C) := by
  obtain ⟨U,hU,hDU,hdis⟩ := support_neighborhood_separation σ hσ D V hD hV hoverlap
  refine ⟨U,hU,hDU,?_⟩
  intro C hC
  refine ⟨hdis.mono_left hC,Set.disjoint_left.mpr ?_⟩
  intro x hx hxσ
  obtain ⟨y,hy,hxy⟩ := hxσ
  have hyσ : y ∈ σ '' U := ⟨x,hx,by rw [← hxy,hi]⟩
  exact Set.disjoint_left.mp hdis (hC hy) hyσ

namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma sphere_neg {y : Phase} (hy : y ∈ unitThreeSphere) : -y ∈ unitThreeSphere := by
  simpa [unitThreeSphere,zNormSq,wNormSq] using hy

lemma supported_map_preserves_set (f r : Phase → Phase) (K : Set Phase)
    (hf : MapsTo f unitThreeSphere unitThreeSphere)
    (hrf : ∀ y ∈ unitThreeSphere, r (f y)=y)
    (hfix : ∀ y ∈ unitThreeSphere, y ∉ K → f y=y) :
    ∀ y ∈ unitThreeSphere, y ∈ K → f y ∈ K := by
  intro y hy hyK
  by_contra hn
  have hfx := hfix (f y) (hf hy) hn
  have hinj : InjOn f unitThreeSphere := by
    intro x hx z hz heq
    simpa only [hrf x hx,hrf z hz] using congrArg r heq
  exact hn ((hinj (hf hy) hy hfx).symm ▸ hyK)

lemma antipodal_pair_odd (f r : Phase → Phase) (K : Set Phase)
    (hf : MapsTo f unitThreeSphere unitThreeSphere)
    (hrf : ∀ y ∈ unitThreeSphere, r (f y)=y)
    (hfix : ∀ y ∈ unitThreeSphere, y ∉ K → f y=y)
    (hsep : ∀ y ∈ K, -y ∉ K) :
    ∀ y ∈ unitThreeSphere, f (-f (-(-y))) = -f (-f (-y)) := by
  intro y hy
  have hm := sphere_neg hy
  have hpres := supported_map_preserves_set f r K hf hrf hfix
  by_cases hyK : y ∈ K
  · have hmy := hfix (-y) hm (hsep y hyK)
    have hmfy := hfix (-f y) (sphere_neg (hf hy)) (hsep (f y) (hpres y hy hyK))
    simp only [neg_neg,hmy,hmfy]
  · by_cases hmK : -y ∈ K
    · have hfy := hfix y hy hyK
      have hnf : -f (-y) ∉ K := hsep (f (-y)) (hpres (-y) hm hmK)
      have hnfFix := hfix (-f (-y)) (sphere_neg (hf hm)) hnf
      simp only [neg_neg,hfy,hnfFix]
    · simp only [neg_neg,hfix y hy hyK,hfix (-y) hm hmK]

/-- The family is actual sphere maps with actual local smooth representatives;
there is no equivariance hypothesis. -/
structure Family where
  f : ℝ → Phase → Phase
  r : ℝ → Phase → Phase
  smooth : ∀ t y, y ∈ unitThreeSphere →
    ContDiffAt ℝ ∞ (fun p : ℝ × Phase => f p.1 p.2) (t,y)
  inv_smooth : ∀ t y, y ∈ unitThreeSphere →
    ContDiffAt ℝ ∞ (r t) y
  maps : ∀ t, MapsTo (f t) unitThreeSphere unitThreeSphere
  inv_maps : ∀ t, MapsTo (r t) unitThreeSphere unitThreeSphere
  left : ∀ t y, y ∈ unitThreeSphere → r t (f t y)=y
  right : ∀ t y, y ∈ unitThreeSphere → f t (r t y)=y
  start : ∀ y ∈ unitThreeSphere, f 0 y=y
  contact : ∀ t y, y ∈ unitThreeSphere → ∃ a : ℝ, 0 < a ∧
    ∀ v, phaseDot y v=0 →
      phaseRadialContact (f t y) (fderiv ℝ (f t) y v)=a*phaseRadialContact y v

lemma Family.slice_smooth (A : Family) (t : ℝ) (y : Phase) (hy : y ∈ unitThreeSphere) :
    ContDiffAt ℝ ∞ (A.f t) y :=
  (A.smooth t y hy).comp y (contDiffAt_const.prodMk contDiffAt_id)

lemma antipodal_conjugate_contact (A : Family) (t : ℝ) (y : Phase)
    (hy : y ∈ unitThreeSphere) :
    ∃ a : ℝ, 0 < a ∧ ∀ v, phaseDot y v=0 →
      phaseRadialContact (-A.f t (-y))
        (fderiv ℝ (fun z => -A.f t (-z)) y v)=a*phaseRadialContact y v := by
  obtain ⟨a,ha,hpb⟩ := A.contact t (-y) (sphere_neg hy)
  refine ⟨a,ha,?_⟩
  intro v hv
  have htan : phaseDot (-y) (-v)=0 := by simpa [phaseDot] using hv
  have hd : fderiv ℝ (fun z => -A.f t (-z)) y v =
      -(fderiv ℝ (A.f t) (-y) (-v)) := by
    have h := ((A.slice_smooth t (-y) (sphere_neg hy)).differentiableAt (by simp)).hasFDerivAt
    have hh := (h.comp y (hasFDerivAt_id y).neg).neg
    exact congrArg (fun L : Phase →L[ℝ] Phase => L v) hh.fderiv
  rw [hd]
  simpa [phaseRadialContact,phaseSymplecticForm] using hpb (-v) htan

def pairedSlice (A : Family) (K : Set Phase)
    (hfix : ∀ t y, y ∈ unitThreeSphere → y ∉ K → A.f t y=y)
    (hsep : ∀ y ∈ K, -y ∉ K) (t : ℝ) : EquivariantSphereContactomorphism where
  toFun := fun y => A.f t (-A.f t (-y))
  invFun := fun y => -A.r t (-A.r t y)
  smooth := by
    intro y hy
    exact (A.slice_smooth t _ (sphere_neg (A.maps t (sphere_neg hy)))).comp y
      (((A.slice_smooth t (-y) (sphere_neg hy)).comp y contDiffAt_id.neg).neg)
  inv_smooth := by
    intro y hy
    exact ((A.inv_smooth t _ (sphere_neg (A.inv_maps t hy))).comp y
      (A.inv_smooth t y hy).neg).neg
  maps_sphere := fun y hy => A.maps t (sphere_neg (A.maps t (sphere_neg hy)))
  inv_maps_sphere := fun y hy => sphere_neg (A.inv_maps t (sphere_neg (A.inv_maps t hy)))
  left_inv := by
    intro y hy
    simp only [A.left t _ (sphere_neg (A.maps t (sphere_neg hy))),neg_neg,
      A.left t _ (sphere_neg hy)]
  right_inv := by
    intro y hy
    simp only [neg_neg,A.right t _ (sphere_neg (A.inv_maps t hy)),A.right t y hy]
  antipodal := antipodal_pair_odd (A.f t) (A.r t) K (A.maps t) (A.left t) (hfix t) hsep
  contact := by
    intro y hy
    let g : Phase → Phase := fun z => -A.f t (-z)
    have hg : ContDiffAt ℝ ∞ g y :=
      ((A.slice_smooth t (-y) (sphere_neg hy)).comp y contDiffAt_id.neg).neg
    have hgMap : MapsTo g unitThreeSphere unitThreeSphere :=
      fun z hz => sphere_neg (A.maps t (sphere_neg hz))
    obtain ⟨a,ha,hf⟩ := A.contact t (g y) (hgMap hy)
    obtain ⟨b,hb,hgpb⟩ := antipodal_conjugate_contact A t y hy
    refine ⟨a*b,mul_pos ha hb,?_⟩
    intro v hv
    have htan := sphere_map_fderiv_tangent g y v hy hv
      (hg.differentiableAt (by simp)) hgMap
    change phaseRadialContact (A.f t (g y)) (fderiv ℝ (A.f t ∘ g) y v)=_
    rw [fderiv_comp y ((A.slice_smooth t (g y) (hgMap hy)).differentiableAt (by simp))
      (hg.differentiableAt (by simp))]
    change phaseRadialContact (A.f t (g y))
      (fderiv ℝ (A.f t) (g y) (fderiv ℝ g y v))=_
    rw [hf _ htan,hgpb v hv]
    ring

def pairedIsotopy (A : Family) (K : Set Phase)
    (hfix : ∀ t y, y ∈ unitThreeSphere → y ∉ K → A.f t y=y)
    (hsep : ∀ y ∈ K, -y ∉ K) :
    EquivariantSphereContactIsotopy (pairedSlice A K hfix hsep 1) where
  slice := pairedSlice A K hfix hsep
  smooth := by
    intro t ht y hy
    have hi : ContDiffAt ℝ ∞ (fun p : ℝ × Phase => -A.f p.1 (-p.2)) (t,y) :=
      ((A.smooth t (-y) (sphere_neg hy)).comp (t,y)
        (contDiffAt_fst.prodMk contDiffAt_snd.neg)).neg
    exact (A.smooth t _ (sphere_neg (A.maps t (sphere_neg hy)))).comp (t,y)
      (contDiffAt_fst.prodMk hi)
  start := by
    intro y hy
    change A.f 0 (-A.f 0 (-y))=y
    rw [A.start (-y) (sphere_neg hy),neg_neg,A.start y hy]
  finish := fun _ _ => rfl

lemma paired_agrees (A : Family) (K : Set Phase)
    (hfix : ∀ t y, y ∈ unitThreeSphere → y ∉ K → A.f t y=y)
    (hsep : ∀ y ∈ K, -y ∉ K) (t : ℝ) (y : Phase)
    (hy : y ∈ unitThreeSphere) (hny : -y ∉ K) :
    (pairedSlice A K hfix hsep t).toFun y=A.f t y := by
  change A.f t (-A.f t (-y))=A.f t y
  rw [hfix t (-y) (sphere_neg hy) hny,neg_neg]

end
end ContactTopology.SphereTransfer


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology Manifold
set_option backward.isDefEq.respectTransparency false
noncomputable section
abbrev V := Fin 3 → ℝ

lemma sphere_tangent_fderiv_eq_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f g : Phase → E) (O : Set Phase) (hO : IsOpen O) (y v : Phase)
    (hyO : y ∈ O) (hy : y ∈ unitThreeSphere) (hv : phaseDot y v=0)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (heq : ∀ z ∈ O, z ∈ unitThreeSphere → f z=g z) :
    fderiv ℝ f y v=fderiv ℝ g y v := by
  let c : ℝ → Phase := fun s => radialNormalize (y+s•v)
  have hc : HasDerivAt c v 0 := sphere_curve_hasDerivAt y v hy hv
  have hc0 : c 0=y := by simp [c,normalize_unit hy]
  have hfy : DifferentiableAt ℝ f (c 0) := by simpa only [hc0] using hf
  have hgy : DifferentiableAt ℝ g (c 0) := by simpa only [hc0] using hg
  have hdf := hfy.hasFDerivAt.comp_hasDerivAt 0 hc
  have hdg := hgy.hasFDerivAt.comp_hasDerivAt 0 hc
  have he : (f ∘ c) =ᶠ[𝓝 (0:ℝ)] (g ∘ c) := by
    have hn : ∀ᶠ s in 𝓝 (0:ℝ), c s ∈ O := by
      have hnO : O ∈ 𝓝 (c 0) := by simpa only [hc0] using hO.mem_nhds hyO
      have hh := hc.continuousAt.preimage_mem_nhds hnO
      exact hh
    filter_upwards [hn] with s hs
    exact heq (c s) hs (radial_normalization_contact_identity _
      (sphere_line_norm_positive y v hy hv s)).2.1
  have hd := (hdf.congr_of_eventuallyEq he.symm).unique hdg
  simpa only [hc0] using hd

lemma inverse_fixed_outside {E : Type*} (f r : E → E) (K : Set E)
    (hleft : ∀ y, r (f y)=y) (hfix : ∀ y, y ∉ K → f y=y) :
    ∀ y, y ∉ K → r y=y := by
  intro y hy
  simpa only [hfix y hy] using hleft y

lemma supported_preserves_superset {E : Type*} (f r : E → E) (K N : Set E)
    (hleft : ∀ y, r (f y)=y) (hfix : ∀ y, y ∉ K → f y=y)
    (hKN : K ⊆ N) : MapsTo f N N := by
  intro y hy
  by_cases hh : f y ∈ K
  · exact hKN hh
  · have hf := hfix (f y) hh
    have hi : Injective f := fun x z h => by simpa only [hleft] using congrArg r h
    exact (hi hf).symm ▸ hy

/-- The chart's local right inverse neighborhoods form an actual ambient open
set. Smoothness of the inverse is needed only at its sphere points. -/
lemma chart_ambient_open (C : V → Phase) (R : Phase → V) (N : Set V)
    (hlocal : ∀ x ∈ N, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y) :
    ∃ O : Set Phase, IsOpen O ∧ C '' N ⊆ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y := by
  let O := {y | ∃ U : Set Phase, IsOpen U ∧ y ∈ U ∧
    ∀ z ∈ U, z ∈ unitThreeSphere → R z ∈ N ∧ C (R z)=z}
  refine ⟨O,?_,?_,?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨U,hU,hy,hdata⟩
    exact mem_of_superset (hU.mem_nhds hy) (fun z hz => ⟨U,hU,hz,hdata⟩)
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨U,hU,hxU,hdata⟩ := hlocal x hx
    exact ⟨U,hU,hxU,hdata⟩
  · rintro y ⟨U,hU,hy,hdata⟩ hys
    exact hdata y hy hys

lemma chart_cutoff (C : V → Phase) (hC : ContDiff ℝ ∞ C)
    (K : Set V) (hK : IsCompact K) (O : Set Phase) (hO : IsOpen O)
    (hKO : C '' K ⊆ O) :
    ∃ χ : Phase → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ O ∧
      ∀ y ∈ C '' K, χ =ᶠ[𝓝 y] (fun _ => 1) := by
  have hCK := hK.image hC.continuous
  obtain ⟨L,hL,hCL,hLO⟩ := exists_compact_between hCK hO hKO
  obtain ⟨χ,hχC,hχout,-⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,Phase)) hCK.isClosed hCL (n := (⊤:ℕ∞))
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,?_,?_⟩
  · have hsupp : tsupport (χ : Phase → ℝ) ⊆ L := by
      apply closure_minimal _ hL.isClosed
      intro y hy
      by_contra hn
      exact hy (hχout y hn)
    exact hsupp.trans hLO
  · intro y hy
    exact hχC.filter_mono (nhds_le_nhdsSet hy)

/-- Localize the coordinate displacement, rather than the map itself. On the
sphere this is the exact chart-conjugate map or the identity. -/
def patch (C : V → Phase) (R : Phase → V) (O : Set Phase) (χ : Phase → ℝ)
    (f : ℝ → V → V) (t : ℝ) (y : Phase) : Phase := by
  classical
  exact y + if y ∈ O then χ y • (C (f t (R y))-C (R y)) else 0

lemma patch_smooth (C : V → Phase) (R : Phase → V) (N : Set V)
    (hC : ContDiff ℝ ∞ C)
    (hR : ∀ x ∈ N, ContDiffAt ℝ ∞ R (C x))
    (O : Set Phase) (hO : IsOpen O)
    (hdata : ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y)
    (χ : Phase → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχO : tsupport χ ⊆ O)
    (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2)) :
    ∀ t y, y ∈ unitThreeSphere →
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => patch C R O χ f p.1 p.2) (t,y) := by
  intro t y hy
  by_cases hyO : y ∈ O
  · have hRy : ContDiffAt ℝ ∞ R y := by
      have hh := hR (R y) (hdata y hyO hy).1
      rwa [(hdata y hyO hy).2] at hh
    have harg : ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (p.1,R p.2)) (t,y) :=
      contDiffAt_fst.prodMk (hRy.comp (t,y) contDiffAt_snd)
    have hs : ContDiffAt ℝ ∞ (fun p : ℝ × Phase => p.2+
        χ p.2 • (C (f p.1 (R p.2))-C (R p.2))) (t,y) :=
      contDiffAt_snd.add (((hχ.comp contDiff_snd).contDiffAt).smul
        (((hC.contDiffAt.comp (t,y) (hf.contDiffAt.comp (t,y) harg))).sub
          (hC.contDiffAt.comp (t,y) (hRy.comp (t,y) contDiffAt_snd))))
    apply hs.congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (hO.mem_nhds hyO)] with p hp
    change p.2 ∈ O at hp
    simp only [patch,if_pos hp]
  · have hn : y ∉ tsupport χ := fun h => hyO (hχO h)
    apply contDiffAt_snd.congr_of_eventuallyEq
    have hz := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (continuous_snd.continuousAt : ContinuousAt (Prod.snd : ℝ × Phase → Phase) (t,y))
    filter_upwards [hz] with p hp
    change χ p.2=0 at hp
    by_cases hpo : p.2 ∈ O <;> simp [patch,hpo,hp]

lemma patch_chart (C : V → Phase) (R : Phase → V) (N K : Set V)
    (hInv : ∀ x ∈ N, R (C x)=x)
    (O : Set Phase) (hNO : C '' N ⊆ O)
    (χ : Phase → ℝ) (hχ1 : ∀ y ∈ C '' K, χ y=1)
    (f : ℝ → V → V) (hfix : ∀ t x, x ∉ K → f t x=x) :
    ∀ t x, x ∈ N → patch C R O χ f t (C x)=C (f t x) := by
  intro t x hx
  rw [patch,if_pos (hNO ⟨x,hx,rfl⟩),hInv x hx]
  by_cases hxK : x ∈ K
  · rw [hχ1 (C x) ⟨x,hxK,rfl⟩,one_smul,add_sub_cancel]
  · rw [hfix t x hxK,sub_self,smul_zero,add_zero]

lemma patch_outside (C : V → Phase) (R : Phase → V) (N K : Set V)
    (O : Set Phase)
    (hdata : ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y)
    (χ : Phase → ℝ) (f : ℝ → V → V) (hfix : ∀ t x, x ∉ K → f t x=x) :
    ∀ t y, y ∈ unitThreeSphere → y ∉ C '' K → patch C R O χ f t y=y := by
  intro t y hy hn
  by_cases hyO : y ∈ O
  · have hRy : R y ∉ K := fun h => hn ⟨R y,h,(hdata y hyO hy).2⟩
    simp only [patch,if_pos hyO,hfix t (R y) hRy,sub_self,smul_zero,add_zero]
  · simp only [patch,if_neg hyO,add_zero]

def covector (a v : V) : ℝ := a 0*v 0+a 1*v 1+a 2*v 2

lemma chart_relative_open (C : V → Phase) (R : Phase → V) (N B : Set V)
    (hInv : ∀ x ∈ N, R (C x)=x) (hR : ∀ x ∈ N, ContDiffAt ℝ ∞ R (C x))
    (hB : IsOpen B) (hBN : B ⊆ N)
    (hlocal : ∀ x ∈ N, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y) :
    ∃ V0 : Set Phase, IsOpen V0 ∧ C '' B ⊆ V0 ∧
      ∀ y ∈ V0, y ∈ unitThreeSphere → R y ∈ B ∧ C (R y)=y := by
  let V0 := {y | ∃ O : Set Phase, IsOpen O ∧ y ∈ O ∧
    ∀ z ∈ O, z ∈ unitThreeSphere → R z ∈ B ∧ C (R z)=z}
  refine ⟨V0,?_,?_,?_⟩
  · rw [isOpen_iff_mem_nhds]
    rintro y ⟨O,hO,hy,hdata⟩
    exact mem_of_superset (hO.mem_nhds hy) (fun z hz => ⟨O,hO,hz,hdata⟩)
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨O,hO,hxO,hdata⟩ := hlocal x (hBN hx)
    have hpre : R ⁻¹' B ∈ 𝓝 (C x) :=
      (hR x (hBN hx)).continuousAt.preimage_mem_nhds (by simpa only [hInv x (hBN hx)] using hB.mem_nhds hx)
    obtain ⟨T,hTsub,hT,hxT⟩ := mem_nhds_iff.mp (inter_mem (hO.mem_nhds hxO) hpre)
    refine ⟨T,hT,hxT,?_⟩
    intro z hz hzs
    exact ⟨(hTsub hz).2,(hdata z (hTsub hz).1 hzs).2⟩
  · rintro y ⟨O,hO,hy,hdata⟩ hys
    exact hdata y hy hys

lemma patch_contact (C : V → Phase) (R : Phase → V) (N K : Set V)
    (hC : ContDiff ℝ ∞ C) (hK : IsCompact K)
    (hR : ∀ x ∈ N, ContDiffAt ℝ ∞ R (C x))
    (a : V → V) (r : V → ℝ) (hrpos : ∀ x ∈ N, 0 < r x)
    (hchart : ∀ x ∈ N, ∀ v, phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (a x) v)
    (O : Set Phase) (hO : IsOpen O)
    (hdata : ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y)
    (χ : Phase → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχO : tsupport χ ⊆ O)
    (hχ1 : ∀ y ∈ C '' K, χ =ᶠ[𝓝 y] (fun _ => 1))
    (f : ℝ → V → V) (hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2))
    (hfN : ∀ t, MapsTo (f t) N N) (hfix : ∀ t x, x ∉ K → f t x=x)
    (lam : ℝ → V → ℝ) (hpos : ∀ t x, x ∈ N → 0 < lam t x)
    (hpb : ∀ t x, x ∈ N → ∀ v,
      covector (a (f t x)) (fderiv ℝ (f t) x v)=lam t x*covector (a x) v) :
    ∀ t y, y ∈ unitThreeSphere → ∃ b : ℝ, 0 < b ∧ ∀ v, phaseDot y v=0 →
      phaseRadialContact (patch C R O χ f t y)
        (fderiv ℝ (patch C R O χ f t) y v)=b*phaseRadialContact y v := by
  intro t y hy
  have hs := patch_smooth C R N hC hR O hO hdata χ hχ hχO f hf t y hy
  have hslice : ContDiffAt ℝ ∞ (patch C R O χ f t) y :=
    hs.comp y (contDiffAt_const.prodMk contDiffAt_id)
  by_cases hyK : y ∈ C '' K
  · have hyO : y ∈ O := hχO (subset_tsupport χ
        (show y ∈ Function.support χ from by
          change χ y ≠ 0
          rw [(hχ1 y hyK).eq_of_nhds]
          norm_num))
    have hyN := (hdata y hyO hy).1
    have hCR := (hdata y hyO hy).2
    have hRy : ContDiffAt ℝ ∞ R y := by simpa only [hCR] using hR (R y) hyN
    have hft : ContDiff ℝ ∞ (f t) := hf.comp (contDiff_const.prodMk contDiff_id)
    obtain ⟨W,hWval,hW,hyW⟩ := eventually_nhds_iff.mp (hχ1 y hyK)
    have heq : ∀ z ∈ O ∩ W, z ∈ unitThreeSphere →
        patch C R O χ f t z=(C ∘ f t ∘ R) z := by
      intro z hz hzs
      simp only [patch,if_pos hz.1,hWval z hz.2,one_smul,Function.comp_apply,
        (hdata z hz.1 hzs).2,add_sub_cancel]
    have hpval : patch C R O χ f t y=C (f t (R y)) := heq y ⟨hyO,hyW⟩ hy
    refine ⟨r (f t (R y))*lam t (R y)/r (R y),
      div_pos (mul_pos (hrpos _ (hfN t hyN)) (hpos t _ hyN)) (hrpos _ hyN),?_⟩
    intro v hv
    have hDCR : fderiv ℝ C (R y) (fderiv ℝ R y v)=v := by
      have hh := sphere_tangent_fderiv_eq_local (C ∘ R) id O hO y v hyO hy hv
        ((hC.contDiffAt.comp y hRy).differentiableAt (by simp)) differentiableAt_id
        (fun z hz hzs => (hdata z hz hzs).2)
      rw [fderiv_comp y (hC.differentiable (by simp) _) (hRy.differentiableAt (by simp))] at hh
      simpa using hh
    have hD := sphere_tangent_fderiv_eq_local (patch C R O χ f t) (C ∘ f t ∘ R)
      (O ∩ W) (hO.inter hW) y v ⟨hyO,hyW⟩ hy hv
      (hslice.differentiableAt (by simp))
      ((hC.contDiffAt.comp y (hft.contDiffAt.comp y hRy)).differentiableAt (by simp)) heq
    have hDcomp : fderiv ℝ (C ∘ f t ∘ R) y v=
        fderiv ℝ C (f t (R y)) (fderiv ℝ (f t) (R y) (fderiv ℝ R y v)) := by
      change fderiv ℝ ((C ∘ f t) ∘ R) y v=_
      rw [fderiv_comp y ((hC.comp hft).differentiable (by simp) _) (hRy.differentiableAt (by simp)),
        fderiv_comp (R y) (hC.differentiable (by simp) _) (hft.differentiable (by simp) _)]
      rfl
    have hbase := hchart (R y) hyN (fderiv ℝ R y v)
    rw [hCR,hDCR] at hbase
    rw [hpval,hD,hDcomp,hchart _ (hfN t hyN),hpb t _ hyN]
    rw [hbase]
    field_simp [(hrpos (R y) hyN).ne']
  · refine ⟨1,by norm_num,?_⟩
    intro v hv
    have hclosed := (hK.image hC.continuous).isClosed
    have heq : ∀ z ∈ (C '' K)ᶜ, z ∈ unitThreeSphere → patch C R O χ f t z=id z := by
      intro z hz hzs
      exact patch_outside C R N K O hdata χ f hfix t z hzs hz
    have hd := sphere_tangent_fderiv_eq_local (patch C R O χ f t) id (C '' K)ᶜ
      hclosed.isOpen_compl y v hyK hy hv
      (hslice.differentiableAt (by simp)) differentiableAt_id heq
    rw [patch_outside C R N K O hdata χ f hfix t y hy hyK,hd]
    simp

theorem chart_family (C : V → Phase) (R : Phase → V) (N K : Set V)
    (hC : ContDiff ℝ ∞ C) (hK : IsCompact K) (hKN : K ⊆ N)
    (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (hR : ∀ x ∈ N, ContDiffAt ℝ ∞ R (C x)) (hInv : ∀ x ∈ N, R (C x)=x)
    (hlocal : ∀ x ∈ N, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y)
    (a : V → V) (r : V → ℝ) (hrpos : ∀ x ∈ N, 0 < r x)
    (hchart : ∀ x ∈ N, ∀ v, phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (a x) v)
    (f g : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (hgf : ∀ t x, g t (f t x)=x) (hfg : ∀ t x, f t (g t x)=x)
    (h0 : ∀ x, f 0 x=x) (hfix : ∀ t x, x ∉ K → f t x=x)
    (lam : ℝ → V → ℝ) (hpos : ∀ t x, x ∈ N → 0 < lam t x)
    (hpb : ∀ t x, x ∈ N → ∀ v,
      covector (a (f t x)) (fderiv ℝ (f t) x v)=lam t x*covector (a x) v) :
    ∃ A : Family,
      (∀ t x, x ∈ N → A.f t (C x)=C (f t x)) ∧
      (∀ t x, x ∈ N → A.r t (C x)=C (g t x)) ∧
      ∀ t y, y ∈ unitThreeSphere → y ∉ C '' K → A.f t y=y := by
  obtain ⟨O,hO,hNO,hdata⟩ := chart_ambient_open C R N hlocal
  obtain ⟨χ,hχ,hχO,hχ1⟩ := chart_cutoff C hC K hK O hO (image_mono hKN |>.trans hNO)
  have hχval : ∀ y ∈ C '' K, χ y=1 := fun y hy => (hχ1 y hy).eq_of_nhds
  have hgfix : ∀ t x, x ∉ K → g t x=x := fun t => inverse_fixed_outside (f t) (g t) K (hgf t) (hfix t)
  have hfN : ∀ t, MapsTo (f t) N N := fun t => supported_preserves_superset (f t) (g t) K N (hgf t) (hfix t) hKN
  have hgN : ∀ t, MapsTo (g t) N N := fun t => supported_preserves_superset (g t) (f t) K N (hfg t) (hgfix t) hKN
  let F := patch C R O χ f
  let G := patch C R O χ g
  have hFC : ∀ t x, x ∈ N → F t (C x)=C (f t x) := patch_chart C R N K hInv O hNO χ hχval f hfix
  have hGC : ∀ t x, x ∈ N → G t (C x)=C (g t x) := patch_chart C R N K hInv O hNO χ hχval g hgfix
  have hFout := patch_outside C R N K O hdata χ f hfix
  have hGout := patch_outside C R N K O hdata χ g hgfix
  have hFK : ∀ t y, y ∈ unitThreeSphere → y ∉ C '' N → F t y=y :=
    fun t y hy hn => hFout t y hy (fun h => hn (image_mono hKN h))
  have hGK : ∀ t y, y ∈ unitThreeSphere → y ∉ C '' N → G t y=y :=
    fun t y hy hn => hGout t y hy (fun h => hn (image_mono hKN h))
  have hFsmooth := patch_smooth C R N hC hR O hO hdata χ hχ hχO f hf
  have hGsmooth := patch_smooth C R N hC hR O hO hdata χ hχ hχO g hg
  let A : Family := {
    f := F
    r := G
    smooth := hFsmooth
    inv_smooth := fun t y hy => (hGsmooth t y hy).comp y (contDiffAt_const.prodMk contDiffAt_id)
    maps := by
      intro t y hy
      by_cases hh : y ∈ C '' N
      · obtain ⟨x,hx,rfl⟩ := hh
        rw [hFC t x hx]; exact hSphere _
      · rw [hFK t y hy hh]; exact hy
    inv_maps := by
      intro t y hy
      by_cases hh : y ∈ C '' N
      · obtain ⟨x,hx,rfl⟩ := hh
        rw [hGC t x hx]; exact hSphere _
      · rw [hGK t y hy hh]; exact hy
    left := by
      intro t y hy
      by_cases hh : y ∈ C '' N
      · obtain ⟨x,hx,rfl⟩ := hh
        rw [hFC t x hx,hGC t _ (hfN t hx),hgf]
      · rw [hFK t y hy hh,hGK t y hy hh]
    right := by
      intro t y hy
      by_cases hh : y ∈ C '' N
      · obtain ⟨x,hx,rfl⟩ := hh
        rw [hGC t x hx,hFC t _ (hgN t hx),hfg]
      · rw [hGK t y hy hh,hFK t y hy hh]
    start := by
      intro y hy
      by_cases hh : y ∈ C '' N
      · obtain ⟨x,hx,rfl⟩ := hh
        rw [hFC 0 x hx,h0]
      · exact hFK 0 y hy hh
    contact := patch_contact C R N K hC hK hR a r hrpos hchart O hO hdata χ hχ hχO hχ1
      f hf hfN hfix lam hpos hpb }
  exact ⟨A,hFC,hGC,hFout⟩

end
end ContactTopology.SphereTransfer


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection BirkhoffGlobalSection.HopfTransport Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem relative_chart_equivariant_extension
    (C : V → Phase) (R : Phase → V) (Nc : Set V) (hNc : IsOpen Nc)
    (hC : ContDiff ℝ ∞ C) (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (hR : ∀ x ∈ Nc, ContDiffAt ℝ ∞ R (C x)) (hInv : ∀ x ∈ Nc, R (C x)=x)
    (hlocal : ∀ x ∈ Nc, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ Nc ∧ C (R y)=y)
    (a : V → V) (ha : ContDiff ℝ ∞ a)
    (hQ : ∀ y, a y 0*(fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1)+
      a y 1*(fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2)+
      a y 2*(fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0) ≠ 0)
    (r : V → ℝ) (hrpos : ∀ x ∈ Nc, 0 < r x)
    (hchart : ∀ x ∈ Nc, ∀ v, phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (a x) v)
    (g : ℝ → V → V) (hg : ContDiff ℝ ∞ (fun p : ℝ × V => g p.1 p.2))
    (lam : ℝ → V → ℝ) (hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2))
    (N : Set V) (hN : IsOpen N) (hinj : ∀ s, InjOn (g s) N)
    (hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x)) (h0 : ∀ x ∈ N, g 0 x=x)
    (hpos : ∀ s x, x ∈ N → 0 < lam s x)
    (hpb : ∀ s x, x ∈ N → ∀ v,
      covector (a (g s x)) (fderiv ℝ (g s) x v)=lam s x*covector (a x) v)
    (D B : Set V) (hD : IsCompact D) (hDN : D ⊆ N) (hDNc : D ⊆ Nc)
    (hB : IsOpen B) (hBN : B ⊆ N) (hBNc : B ⊆ Nc)
    (hstationary : ∀ s x, x ∈ B → g s x=x)
    (hDfix : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ D, g s x=x)
    (hoverlap : (C '' D) ∩ ((fun y : Phase => -y) '' (C '' D)) ⊆ C '' B) :
    ∃ F : EquivariantSphereContactomorphism, ∃ I : EquivariantSphereContactIsotopy F,
    ∃ M : Set V, ∃ P : Set Phase,
      IsOpen M ∧ D ⊆ M ∧ M ⊆ N ∩ Nc ∧ IsCompact P ∧ P ⊆ unitThreeSphere ∧
      (∀ y ∈ P, -y ∉ P) ∧
      (∀ x ∈ M, F.toFun (C x)=C (g 1 x)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ D, (I.slice t).toFun (C x)=C x) ∧
      ∀ t y, y ∈ unitThreeSphere → y ∉ P ∪ ((fun z : Phase => -z) '' P) →
        (I.slice t).toFun y=y := by


  obtain ⟨V0,hV0,hBV0,hVdata⟩ := chart_relative_open C R Nc B hInv hR hB hBNc hlocal
  have hCD : IsCompact (C '' D) := hD.image hC.continuous
  obtain ⟨U,hU,hDU,hsep⟩ := involutive_support_separation (fun y : Phase => -y) continuous_neg
    neg_neg (C '' D) V0 hCD hV0 (hoverlap.trans hBV0)
  let W : Set V := Nc ∩ C ⁻¹' U
  have hW : IsOpen W := hNc.inter (hU.preimage hC.continuous)
  have hDW : D ⊆ W := fun x hx => ⟨hDNc hx,hDU ⟨x,hx,rfl⟩⟩
  have htD : Icc (0:ℝ) 1 ×ˢ D ⊆ (fun p : ℝ × V => g p.1 p.2) ⁻¹' W := by
    rintro ⟨s,x⟩ ⟨hs,hx⟩
    change g s x ∈ W
    rw [hDfix s hs x hx]
    exact hDW hx
  obtain ⟨J,T,hJ,hT,hIJ,hDT,hJT⟩ := generalized_tube_lemma isCompact_Icc hD
    (hW.preimage hg.continuous) htD
  let T0 := T ∩ (N ∩ Nc)
  have hT0 : IsOpen T0 := hT.inter (hN.inter hNc)
  have hDT0 : D ⊆ T0 := fun x hx => ⟨hDT hx,hDN hx,hDNc hx⟩
  obtain ⟨K,hK,hDK,hKT⟩ := exists_compact_between hD hT0 hDT0
  have hKN : K ⊆ N := fun x hx => (hKT hx).2.1
  have htrack : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ K, g s x ∈ W := by
    intro s hs x hx
    exact hJT (show (s,x) ∈ J ×ˢ T from ⟨hIJ hs,(hKT hx).1⟩)
  obtain ⟨ψ,ρ,Λ,Q,hψ,hρ,hΛ,hQcompact,hQW,hψ0,hρψ,hψρ,hout,hΛpos,hcontact,hmatch,hBfix⟩ :=
    ContactTopology.relative_compact_contact_embedding_isotopy_extension a ha g hg lam hlam N hN
      hinj hder h0 B hBN hstationary K W hK hKN hW htrack hQ hpos hpb
  let Q0 := Q \ B
  have hQ0 : IsCompact Q0 := hQcompact.diff hB
  have hQ0Nc : Q0 ⊆ Nc := fun x hx => (hQW hx.1).1
  have hout0 : ∀ t x, x ∉ Q0 → ψ t x=x := by
    intro t x hx
    by_cases hxQ : x ∈ Q
    · exact hBfix t x (by by_contra hn; exact hx ⟨hxQ,hn⟩)
    · exact hout t x hxQ
  let P := C '' Q0
  have hPU : P ⊆ U \ V0 := by
    rintro y ⟨x,hx,rfl⟩
    refine ⟨(hQW hx.1).2,?_⟩
    intro hh
    have hrx := (hVdata (C x) hh (hSphere x)).1
    rw [hInv x (hQ0Nc hx)] at hrx
    exact hx.2 hrx
  have hdis := hsep P hPU
  have hself : ∀ y ∈ P, -y ∉ P := by
    intro y hy hn
    exact Set.disjoint_left.mp hdis.2 (hPU hy).1 ⟨-y,hn,neg_neg y⟩
  have hny : ∀ x ∈ K, -C x ∉ P := by
    intro x hx hn
    have hxW : x ∈ W := by simpa only [h0 x (hKN hx)] using htrack 0 (by constructor <;> norm_num) x hx
    exact Set.disjoint_left.mp hdis.2 hxW.2 ⟨-C x,hn,neg_neg (C x)⟩
  let θ : ℝ → ℝ := Real.smoothTransition
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff
  have hθ01 : ∀ t, θ t ∈ Icc (0:ℝ) 1 := fun t =>
    ⟨Real.smoothTransition.nonneg t,Real.smoothTransition.le_one t⟩
  have hθ0 : θ 0=0 := Real.smoothTransition.zero
  have hθ1 : θ 1=1 := Real.smoothTransition.one
  let f := fun t => ψ (θ t)
  let q := fun t => ρ (θ t)
  let ell := fun t => Λ (θ t)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × V => (θ p.1,p.2)) :=
    (hθ.comp contDiff_fst).prodMk contDiff_snd
  obtain ⟨A,hAC,hAR,hAout⟩ := chart_family C R Nc Q0 hC hQ0 hQ0Nc hSphere hR hInv hlocal
    a r hrpos hchart f q (hψ.comp harg) (hρ.comp harg)
    (fun t x => hρψ (θ t) x) (fun t x => hψρ (θ t) x)
    (fun x => by simpa only [f,hθ0] using hψ0 x) (fun t x hx => hout0 (θ t) x hx)
    ell (fun t x _ => hΛpos (θ t) x) (fun t x _ v => hcontact (θ t) (hθ01 t) x v)
  let F := pairedSlice A P hAout hself 1
  let I := pairedIsotopy A P hAout hself
  refine ⟨F,I,interior K,P,isOpen_interior,hDK,?_,hQ0.image hC.continuous,?_,hself,?_,?_,?_⟩
  · intro x hx
    exact (hKT (interior_subset hx)).2
  · rintro y ⟨x,hx,rfl⟩
    exact hSphere x
  · intro x hx
    have hxK := interior_subset hx
    have hxNc := (hKT hxK).2.2
    change (pairedSlice A P hAout hself 1).toFun (C x)=_
    rw [paired_agrees A P hAout hself 1 (C x) (hSphere x) (hny x hxK),hAC 1 x hxNc]
    change C (ψ (θ 1) x)=_
    rw [hθ1,hmatch 1 (by constructor <;> norm_num) x hxK]
  · intro t ht x hx
    have hxK := interior_subset (hDK hx)
    change (pairedSlice A P hAout hself t).toFun (C x)=_
    rw [paired_agrees A P hAout hself t (C x) (hSphere x) (hny x hxK),hAC t x (hDNc hx)]
    change C (ψ (θ t) x)=C x
    rw [hmatch (θ t) (hθ01 t) x hxK,hDfix (θ t) (hθ01 t) x hx]
  · intro t y hy hn
    have hyn : y ∉ P := fun h => hn (Or.inl h)
    have hmyn : -y ∉ P := fun h => hn (Or.inr ⟨-y,h,neg_neg y⟩)
    change (pairedSlice A P hAout hself t).toFun y=y
    rw [paired_agrees A P hAout hself t y hy hmyn,hAout t y hy hyn]

end
end ContactTopology.SphereTransfer


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section

lemma sphere_parametrization_tangent (C : V → Phase) (hC : ContDiff ℝ ∞ C)
    (hSphere : ∀ x, C x ∈ unitThreeSphere) (x v : V) :
    phaseDot (C x) (fderiv ℝ C x v)=0 := by
  have hc : HasDerivAt (fun s : ℝ => x+s•v) v 0 := by
    convert! (hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v) using 1 <;> simp
  have hd := (hC.differentiable (by simp) (x+(0:ℝ)•v)).hasFDerivAt.comp_hasDerivAt 0
    (show HasDerivAt (fun s : ℝ => x+s•v) v 0 from hc)
  have hn := BirkhoffGlobalSection.HopfTransport.dot_self_hasDerivAt hd
  have heq : (fun s : ℝ => phaseDot (C (x+s•v)) (C (x+s•v)))=fun _ => (1:ℝ) := by
    funext s
    exact BirkhoffGlobalSection.HopfTransport.sphere_dot_self (hSphere _)
  dsimp only [Function.comp_apply] at hn
  rw [heq] at hn
  have hh := hn.unique (hasDerivAt_const (0:ℝ) (1:ℝ))
  simp only [zero_smul,add_zero] at hh
  linarith

lemma coordinate_contact_factor (C : V → Phase) (N : Set V)
    (hC : ContDiff ℝ ∞ C) (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (a : V → V) (r : V → ℝ) (hrpos : ∀ x ∈ N, 0 < r x)
    (hchart : ∀ x ∈ N, ∀ v,
      phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (a x) v)
    (G : EquivariantSphereContactomorphism)
    (e : OpenPartialHomeomorph V V)
    (he : ContDiffOn ℝ ∞ (e : V → V) e.source)
    (hsource : e.source ⊆ N) (htarget : e.target ⊆ N)
    (hmap : ∀ x ∈ e.source, C (e x)=G.toFun (C x)) :
    ∀ x ∈ e.source, ∃ L : ℝ, 0 < L ∧ ∀ v,
      covector (a (e x)) (fderiv ℝ (e : V → V) x v)=L*covector (a x) v := by
  intro x hx
  have hexN := htarget (e.map_source hx)
  obtain ⟨c,hc,hcpb⟩ := G.contact (C x) (hSphere x)
  have hs := (he x hx).contDiffAt (e.open_source.mem_nhds hx)
  have heq : (C ∘ (e : V → V)) =ᶠ[𝓝 x] (G.toFun ∘ C) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hmap y hy
  have hD := heq.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hC.differentiable (by simp) _) (hs.differentiableAt (by simp)),
    fderiv_comp x ((G.smooth (C x) (hSphere x)).differentiableAt (by simp))
      (hC.differentiable (by simp) x)] at hD
  refine ⟨c*r x/r (e x),div_pos (mul_pos hc (hrpos x (hsource hx))) (hrpos _ hexN),?_⟩
  intro v
  have hv := sphere_parametrization_tangent C hC hSphere x v
  have hp := hcpb (fderiv ℝ C x v) hv
  have hdv := congrArg (fun L : V →L[ℝ] Phase => L v) hD
  change fderiv ℝ C (e x) (fderiv ℝ (e : V → V) x v)=
    fderiv ℝ G.toFun (C x) (fderiv ℝ C x v) at hdv
  rw [← hdv,← hmap x hx,hchart (e x) hexN,hchart x (hsource hx)] at hp
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (hrpos (e x) hexN).ne').mpr
  nlinarith [hp]

/-- A pointwise positive pullback factor has an actual smooth representative,
obtained by evaluating on the nonzero coefficient vector. -/
lemma smooth_contact_factor (a : V → V) (ha : ContDiff ℝ ∞ a)
    (e : OpenPartialHomeomorph V V) (he : ContDiffOn ℝ ∞ (e : V → V) e.source)
    (haneq : ∀ x ∈ e.source, covector (a x) (a x) ≠ 0)
    (hpoint : ∀ x ∈ e.source, ∃ c : ℝ, 0 < c ∧ ∀ v,
      covector (a (e x)) (fderiv ℝ (e : V → V) x v)=c*covector (a x) v) :
    ∃ L : V → ℝ, ContDiffOn ℝ ∞ L e.source ∧
      (∀ x ∈ e.source, 0 < L x) ∧ ∀ x ∈ e.source, ∀ v,
        covector (a (e x)) (fderiv ℝ (e : V → V) x v)=L x*covector (a x) v := by
  let L : V → ℝ := fun x => covector (a (e x)) (fderiv ℝ (e : V → V) x (a x))/covector (a x) (a x)
  have hD : ContDiffOn ℝ ∞ (fun x => fderiv ℝ (e : V → V) x (a x)) e.source :=
    (he.fderiv_of_isOpen e.open_source (m := ∞) (by simp)).clm_apply ha.contDiffOn
  have hAE : ContDiffOn ℝ ∞ (fun x => a (e x)) e.source := ha.comp_contDiffOn he
  have hnum : ContDiffOn ℝ ∞ (fun x => covector (a (e x)) (fderiv ℝ (e : V → V) x (a x))) e.source := by
    unfold covector
    exact ((((contDiff_apply ℝ ℝ (0:Fin 3)).comp_contDiffOn hAE).mul ((contDiff_apply ℝ ℝ (0:Fin 3)).comp_contDiffOn hD)).add
      (((contDiff_apply ℝ ℝ (1:Fin 3)).comp_contDiffOn hAE).mul ((contDiff_apply ℝ ℝ (1:Fin 3)).comp_contDiffOn hD))).add
      (((contDiff_apply ℝ ℝ (2:Fin 3)).comp_contDiffOn hAE).mul ((contDiff_apply ℝ ℝ (2:Fin 3)).comp_contDiffOn hD))
  have hden : ContDiff ℝ ∞ (fun x => covector (a x) (a x)) := by
    unfold covector
    fun_prop
  have hL : ContDiffOn ℝ ∞ L e.source := hnum.div hden.contDiffOn haneq
  have hLc : ∀ x ∈ e.source, ∀ c : ℝ,
      (∀ v, covector (a (e x)) (fderiv ℝ (e : V → V) x v)=c*covector (a x) v) → L x=c := by
    intro x hx c hpb
    exact (div_eq_iff (haneq x hx)).mpr (hpb (a x))
  refine ⟨L,hL,?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,hpb⟩ := hpoint x hx
    rw [hLc x hx c hpb]
    exact hc
  · intro x hx v
    obtain ⟨c,hc,hpb⟩ := hpoint x hx
    rw [hLc x hx c hpb]
    exact hpb v

/-- An actual sphere contactomorphism gives a genuine local coordinate
homeomorphism on the chart overlap. No global smooth inverse chart is used. -/
theorem coordinate_partial_homeomorph (C : V → Phase) (R : Phase → V)
    (N : Set V) (hN : IsOpen N) (hC : ContDiff ℝ ∞ C)
    (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (hR : ∀ x ∈ N, ContDiffAt ℝ ∞ R (C x)) (hInv : ∀ x ∈ N, R (C x)=x)
    (hlocal : ∀ x ∈ N, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ N ∧ C (R y)=y)
    (G : EquivariantSphereContactomorphism) :
    ∃ e : OpenPartialHomeomorph V V,
      ContDiffOn ℝ ∞ (e : V → V) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : V → V) e.target ∧
      e.source ⊆ N ∧ e.target ⊆ N ∧
      (∀ x ∈ e.source, C (e x)=G.toFun (C x)) ∧
      (∀ x ∈ e.target, C (e.symm x)=G.invFun (C x)) ∧
      ∀ x ∈ N, G.toFun (C x)=C x → x ∈ e.source ∧ e x=x := by
  obtain ⟨O,hO,hNO,hdata⟩ := chart_ambient_open C R N hlocal
  let f : V → V := R ∘ G.toFun ∘ C
  let g : V → V := R ∘ G.invFun ∘ C
  have hGC : ContDiff ℝ ∞ (G.toFun ∘ C) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (G.smooth _ (hSphere x)).comp x hC.contDiffAt
  have hGIC : ContDiff ℝ ∞ (G.invFun ∘ C) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (G.inv_smooth _ (hSphere x)).comp x hC.contDiffAt
  let U := N ∩ (G.toFun ∘ C) ⁻¹' O
  let T := N ∩ (G.invFun ∘ C) ⁻¹' O
  have hU : IsOpen U := hN.inter (hO.preimage hGC.continuous)
  have hT : IsOpen T := hN.inter (hO.preimage hGIC.continuous)
  have hfN : ∀ x ∈ U, f x ∈ N ∧ C (f x)=G.toFun (C x) := by
    intro x hx
    exact hdata _ hx.2 (G.maps_sphere (hSphere x))
  have hgN : ∀ x ∈ T, g x ∈ N ∧ C (g x)=G.invFun (C x) := by
    intro x hx
    exact hdata _ hx.2 (G.inv_maps_sphere (hSphere x))
  have hfT : MapsTo f U T := by
    intro x hx
    refine ⟨(hfN x hx).1,?_⟩
    change G.invFun (C (f x)) ∈ O
    rw [(hfN x hx).2,G.left_inv _ (hSphere x)]
    exact hNO ⟨x,hx.1,rfl⟩
  have hgU : MapsTo g T U := by
    intro x hx
    refine ⟨(hgN x hx).1,?_⟩
    change G.toFun (C (g x)) ∈ O
    rw [(hgN x hx).2,G.right_inv _ (hSphere x)]
    exact hNO ⟨x,hx.1,rfl⟩
  have hgf : ∀ x ∈ U, g (f x)=x := by
    intro x hx
    change R (G.invFun (C (f x)))=x
    rw [(hfN x hx).2,G.left_inv _ (hSphere x),hInv x hx.1]
  have hfg : ∀ x ∈ T, f (g x)=x := by
    intro x hx
    change R (G.toFun (C (g x)))=x
    rw [(hgN x hx).2,G.right_inv _ (hSphere x),hInv x hx.1]
  have hf : ContDiffOn ℝ ∞ f U := by
    intro x hx
    have hh := hR (f x) (hfN x hx).1
    rw [(hfN x hx).2] at hh
    exact (hh.comp x hGC.contDiffAt).contDiffWithinAt
  have hg : ContDiffOn ℝ ∞ g T := by
    intro x hx
    have hh := hR (g x) (hgN x hx).1
    rw [(hgN x hx).2] at hh
    exact (hh.comp x hGIC.contDiffAt).contDiffWithinAt
  let e : OpenPartialHomeomorph V V := {
    toFun := f
    invFun := g
    source := U
    target := T
    map_source' := hfT
    map_target' := hgU
    left_inv' := fun {x} hx => hgf x hx
    right_inv' := fun {x} hx => hfg x hx
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hg.continuousOn
    open_source := hU
    open_target := hT }
  refine ⟨e,hf,hg,inter_subset_left,inter_subset_left,
    (fun x hx => (hfN x hx).2),(fun x hx => (hgN x hx).2),?_⟩
  intro x hx hfix
  refine ⟨⟨hx,?_⟩,?_⟩
  · change G.toFun (C x) ∈ O
    rw [hfix]
    exact hNO ⟨x,hx,rfl⟩
  · change R (G.toFun (C x))=x
    rw [hfix,hInv x hx]

end
end ContactTopology.SphereTransfer



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


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection Set Function
open scoped ContDiff
noncomputable section

def modelCoeff (y : V) : V := ![1+y 0^2-y 1^2,2*y 0*y 1,2*y 1]

lemma modelCoeff_smooth : ContDiff ℝ ∞ modelCoeff := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [modelCoeff] <;> fun_prop

lemma modelCoeff_deriv (y v : V) : fderiv ℝ modelCoeff y v=
    ![2*y 0*v 0-2*y 1*v 1,2*(v 0*y 1+y 0*v 1),2*v 1] := by
  let p (i : Fin 3) : V →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h0 := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) y).add
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)
  have h1 := (((p 0).hasFDerivAt (x := y)).const_mul 2).mul ((p 1).hasFDerivAt (x := y))
  have h2 := ((p 1).hasFDerivAt (x := y)).const_mul 2
  change HasFDerivAt (fun z : V => 1+z 0^2-z 1^2) _ y at h0
  change HasFDerivAt (fun z : V => 2*z 0*z 1) _ y at h1
  change HasFDerivAt (fun z : V => 2*z 1) _ y at h2
  have hd : HasFDerivAt modelCoeff (ContinuousLinearMap.pi
      ![fderiv ℝ (fun z : V => 1+z 0^2-z 1^2) y,
        fderiv ℝ (fun z : V => 2*z 0*z 1) y,
        fderiv ℝ (fun z : V => 2*z 1) y]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
    · exact h2.differentiableAt.hasFDerivAt
  rw [hd.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,h2.fderiv,p] <;> ring

lemma modelCoeff_contact (y : V) :
    modelCoeff y 0*(fderiv ℝ modelCoeff y (Pi.single 1 1) 2-fderiv ℝ modelCoeff y (Pi.single 2 1) 1)+
      modelCoeff y 1*(fderiv ℝ modelCoeff y (Pi.single 2 1) 0-fderiv ℝ modelCoeff y (Pi.single 0 1) 2)+
      modelCoeff y 2*(fderiv ℝ modelCoeff y (Pi.single 0 1) 1-fderiv ℝ modelCoeff y (Pi.single 1 1) 0) ≠ 0 := by
  simp only [modelCoeff_deriv]
  simp [modelCoeff]
  nlinarith [sq_nonneg (y 0),sq_nonneg (y 1)]

def diskSet : Set V := {y | y 0^2+y 1^2 ≤ 1 ∧ y 2=0}

lemma diskSet_compact : IsCompact diskSet := by
  have hn : Continuous (fun y : V => y 0^2+y 1^2) := by fun_prop
  have hclosed : IsClosed diskSet :=
    (isClosed_le hn continuous_const).inter (isClosed_eq (continuous_apply 2) continuous_const)
  apply (isCompact_Icc : IsCompact (Icc (![-1,-1,0] : V) ![1,1,0])).of_isClosed_subset hclosed
  intro y hy
  constructor <;> intro i <;> fin_cases i <;> dsimp <;>
    nlinarith [hy.1,hy.2,sq_nonneg (y 0),sq_nonneg (y 1)]

end
end ContactTopology.SphereTransfer




/-! Three-dimensional contact-form deformations. The explicit Moser field below
is the analytic local input to deformation arguments for convex surfaces. No
bypass existence or tight-solid-torus uniqueness is assumed or claimed here. -/
namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

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

def spatialD (A : ℝ × V → V) (p : ℝ × V) : V →L[ℝ] V :=
  (fderiv ℝ A p).comp (ContinuousLinearMap.inr ℝ ℝ V)

def velocity (A : ℝ × V → V) (p : ℝ × V) : V := fderiv ℝ A p (1,0)
def curl (A : ℝ × V → V) (p : ℝ × V) : V := curlLinear (spatialD A p)
def volume (A : ℝ × V → V) (p : ℝ × V) : ℝ := dot (A p) (curl A p)
def form (A : ℝ × V → V) (t : ℝ) : OneForm 3 := fun y => covector (A (t,y))
def moser (A : ℝ × V → V) (p : ℝ × V) : V :=
  (volume A p)⁻¹ • cross (A p) (velocity A p)
def rate (A : ℝ × V → V) (p : ℝ × V) : ℝ :=
  dot (curl A p) (velocity A p)/volume A p

lemma spatialD_eq (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y : V) :
    fderiv ℝ (fun z => A (t,z)) y = spatialD A (t,y) := by
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp y
    ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  exact hd.fderiv

lemma form_fderiv (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y u v : V) :
    fderiv ℝ (form A t) y u v = dot (spatialD A (t,y) u) v := by
  have hd := covector.hasFDerivAt.comp y
    ((hA.differentiable (by simp) (t,y)).hasFDerivAt.comp y
      ((hasFDerivAt_const (𝕜 := ℝ) t y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)))
  change HasFDerivAt (form A t) _ y at hd
  rw [hd.fderiv]
  exact covector_apply _ _

lemma form_time_deriv (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (t : ℝ) (y v : V) :
    formTimeDeriv (form A) t y v = dot (velocity A (t,y)) v := by
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  have hc := (covector.hasFDerivAt.comp_hasDerivAt t hd).clm_apply (hasDerivAt_const t v)
  change HasDerivAt (fun s => form A s y v) _ t at hc
  rw [formTimeDeriv,hc.deriv]
  simpa [velocity] using covector_apply (velocity A (t,y)) v

lemma curl_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (curl A) := by
  have hd := hA.fderiv_right (by simp : (∞:WithTop ℕ∞) + 1 ≤ ∞)
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [curl,curlLinear,spatialD] <;> fun_prop

lemma velocity_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (velocity A) :=
  (hA.fderiv_right (by simp)).clm_apply contDiff_const

lemma volume_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (volume A) := by
  have hc := curl_contDiff A hA
  change ContDiff ℝ ∞ (fun p => A p 0*curl A p 0+A p 1*curl A p 1+A p 2*curl A p 2)
  fun_prop

lemma moser_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) : ContDiff ℝ ∞ (moser A) := by
  have hv := velocity_contDiff A hA
  have hi := (volume_contDiff A hA).inv hvol
  apply hi.smul
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [cross] <;> fun_prop

lemma rate_contDiff (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) : ContDiff ℝ ∞ (rate A) := by
  have hc := curl_contDiff A hA
  have hv := velocity_contDiff A hA
  have hi := (volume_contDiff A hA).inv hvol
  change ContDiff ℝ ∞ (fun p =>
    (curl A p 0*velocity A p 0+curl A p 1*velocity A p 1+curl A p 2*velocity A p 2)*
      (volume A p)⁻¹)
  exact (show ContDiff ℝ ∞ (fun p =>
    curl A p 0*velocity A p 0+curl A p 1*velocity A p 1+curl A p 2*velocity A p 2) by fun_prop).mul hi

lemma moser_kernel (A : ℝ × V → V) (p : ℝ × V) : covector (A p) (moser A p) = 0 := by
  simp [covector_apply,moser,dot,cross]
  ring

lemma moser_lie_equation (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (t : ℝ) (y v : V) :
    formTimeDeriv (form A) t y v+
      lieDerivOneForm (fun z => moser A (t,z)) (form A t) y v =
        rate A (t,y)*form A t y v := by
  have hX := (moser_contDiff A hA hvol).comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z)))
  have hα := covector.contDiff.comp (hA.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z))))
  have hz : (fun z : V => form A t z (moser A (t,z))) = fun _ => 0 :=
    funext fun z => moser_kernel A (t,z)
  change ContDiff ℝ ∞ (form A t) at hα
  change ContDiff ℝ ∞ (fun z => moser A (t,z)) at hX
  have hd := (hα.differentiable (by simp) y).hasFDerivAt.clm_apply
    (hX.differentiable (by simp) y).hasFDerivAt
  have hd0 : fderiv ℝ (fun z : V => form A t z (moser A (t,z))) y v = 0 := by
    rw [hz]
    simp
  change HasFDerivAt (fun z => form A t z (moser A (t,z))) _ y at hd
  rw [hd.fderiv] at hd0
  change form A t y (fderiv ℝ (fun z => moser A (t,z)) y v)+
    fderiv ℝ (form A t) y v (moser A (t,y)) = 0 at hd0
  rw [form_fderiv A hA] at hd0
  have hm := (moser_algebra (A (t,y)) (velocity A (t,y)) (curl A (t,y)) v (hvol (t,y))).2
  change dot (velocity A (t,y)) v+dot (curlLinear (spatialD A (t,y)))
    (cross (moser A (t,y)) v) = rate A (t,y)*form A t y v at hm
  rw [← exterior_cross (spatialD A (t,y)) (moser A (t,y)) v] at hm
  rw [form_time_deriv A hA]
  dsimp [lieDerivOneForm]
  rw [form_fderiv A hA]
  change dot (velocity A (t,y)) v+ (dot (spatialD A (t,y) (moser A (t,y))) v+
    form A t y (fderiv ℝ (fun z => moser A (t,z)) y v)) = _
  change dot (velocity A (t,y)) v+(dot (spatialD A (t,y) (moser A (t,y))) v-
    dot (spatialD A (t,y) v) (moser A (t,y))) =
      rate A (t,y)*form A t y v at hm
  linarith


lemma smooth_inverse_of_bijective_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → E) (hf : ContDiff ℝ ∞ f) (hb : Function.Bijective f)
    (hi : ∀ x, Function.Injective (fderiv ℝ f x)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ (∀ x, g (f x) = x) ∧ (∀ x, f (g x) = x) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
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
  let : CompleteSpace V := FiniteDimensional.complete ℝ V
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


/-- The ambient flow part of the existing regular-level theorem can be used
with an empty regular level; no compactness of the ambient space is required. -/
lemma exists_ambient_flow (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0) :
    ∃ ψ : ℝ → V → V, ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  let F : V → (Fin 1 → ℝ) := fun _ _ => 1
  have hempty : levelSet F = ∅ := by
    ext y
    simp only [levelSet,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    have hh := congrFun h 0
    norm_num [F] at hh
  have hF : IsCompactRegularLevel F := by
    refine ⟨contDiff_const,?_,?_⟩
    · rw [hempty]
      exact isCompact_empty
    · intro y hy
      rw [hempty] at hy
      exact hy.elim
  obtain ⟨ψ,hψ,h0,hbij,hflow,_⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level F hF X hX hsupp (by
      intro t ht y hy
      rw [hempty] at hy
      exact hy.elim)
  exact ⟨ψ,hψ,h0,hbij,hflow⟩

lemma ambient_flow_fixes (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hy : ∀ t, X t y = 0) : ∀ t, ψ t y = y := by
  have hp : (fun s => ψ s y) 0 = y ∧
      ∀ t, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := ⟨h0 y,fun t => hflow t y⟩
  have hc : (fun _ : ℝ => y) 0 = y ∧
      ∀ t, HasDerivAt (fun _ : ℝ => y) (X t y) t := by
    refine ⟨rfl,?_⟩
    intro t
    rw [hy t]
    exact hasDerivAt_const t y
  have he : (fun s => ψ s y) = fun _ => y :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX hsupp 0 y).unique hp hc
  exact fun t => congrFun he t

theorem compact_supported_contact_deformation
    (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0)
    (K : Set V) (hK : IsCompact K)
    (hstationary : ∀ t y, y ∉ K → velocity A (t,y) = 0) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, y ∉ K → ψ t y = y) ∧
      (∀ y, (∀ s, velocity A (s,y) = 0) → ∀ t, ψ t y = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y, Injective (fderiv ℝ (ψ t) y)) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        pullback (ψ t) (form A t) y v = lam t y*form A 0 y v := by
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0 := by
    refine ⟨K,hK,?_⟩
    intro t y hy
    simp [X,moser,hstationary t y hy,cross]
  obtain ⟨ψ,hψ,h0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  let q : ℝ → V → ℝ := fun t y => rate A (t,ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => q p.1 p.2) :=
    (rate_contDiff A hA hvol).comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,hlam0,hpos,htransport⟩ :=
    ParameterizedCalculus.smooth_scalar_linear_transport q hq
  have hfix : ∀ y, (∀ s, velocity A (s,y) = 0) → ∀ t, ψ t y = y := by
    intro y hy
    apply ambient_flow_fixes X ψ hX hsupp h0 hflow y
    intro t
    simp [X,moser,hy t,cross]
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,?_,hfix,hpos,?_,?_⟩
  · intro t y hy
    exact hfix y (fun s => hstationary s y hy) t
  · exact FlowCalculus.smooth_flow_spatial_derivative_injective X ψ hX hψ h0 hflow
  · intro t ht y v
    have hform : IsSmoothFamily (form A) := covector.contDiff.comp hA
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ r) (form A r) y v)
          (q s y*pullback (ψ s) (form A s) y v) s := by
      intro s hs
      have hd := GrayStability.pullback_family_hasDerivAt (form A) hform X hX ψ hψ h0 hbij hflow s y v
      have he := moser_lie_equation A hA hvol s (ψ s y) (fderiv ℝ (ψ s) y v)
      change formTimeDeriv (form A) s (ψ s y) (fderiv ℝ (ψ s) y v)+
        lieDerivOneForm (X s) (form A s) (ψ s y) (fderiv ℝ (ψ s) y v) = _ at he
      rw [he] at hd
      exact hd
    have hinit : pullback (ψ 0) (form A 0) y v = form A 0 y v := by
      have hid : ψ 0 = id := funext h0
      simp [pullback,hid]
    simpa only [hinit] using htransport y (fun r => pullback (ψ r) (form A r) y v) hf t ht


lemma dot_self_pos (v : V) (hv : v ≠ 0) : 0 < dot v v := by
  have hn : 0 ≤ dot v v := by
    dsimp [dot]
    nlinarith [sq_nonneg (v 0),sq_nonneg (v 1),sq_nonneg (v 2)]
  by_contra h
  have hz : dot v v = 0 := le_antisymm (not_lt.mp h) hn
  dsimp [dot] at hz
  have h₀ : v 0 = 0 := by nlinarith [sq_nonneg (v 1),sq_nonneg (v 2)]
  have h₁ : v 1 = 0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 2)]
  have h₂ : v 2 = 0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
  apply hv
  ext i
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂

lemma contact_nondegenerate (a c u : V) (hvol : dot a c ≠ 0)
    (hu : dot a u = 0) (hne : u ≠ 0) :
    ∃ v : V, dot a v = 0 ∧ dot c (cross u v) ≠ 0 := by
  refine ⟨cross a u,?_,?_⟩
  · simp [dot,cross]
    ring
  · have he : dot c (cross u (cross a u)) = dot a c*dot u u-dot c u*dot a u := by
      simp [dot,cross]
      ring
    rw [he,hu,mul_zero,sub_zero]
    exact mul_ne_zero hvol (dot_self_pos u hne).ne'

lemma form_is_contact (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (t : ℝ) (y : V) :
    IsContactFormAt (fun _ : V => (0 : Fin 0 → ℝ)) (form A t) y := by
  have htan : ∀ v : V, v ∈ tangentSpace (fun _ : V => (0 : Fin 0 → ℝ)) y := by
    intro v
    simp [tangentSpace]
  refine ⟨⟨curl A (t,y),htan _,?_⟩,?_⟩
  · exact hvol (t,y)
  · intro u hu hne
    obtain ⟨v,hv,hb⟩ := contact_nondegenerate (A (t,y)) (curl A (t,y)) u (hvol (t,y)) hu.2 hne
    refine ⟨v,⟨htan v,hv⟩,?_⟩
    dsimp [extDerivOneForm]
    rw [form_fderiv A hA,form_fderiv A hA,exterior_cross]
    exact hb

/-- Flattened interpolation, constant outside the unit time interval. -/
def blend (a₀ a₁ : V → V) (p : ℝ × V) : V :=
  (1-Real.smoothTransition p.1) • a₀ p.2+Real.smoothTransition p.1 • a₁ p.2

lemma blend_contDiff (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁) :
    ContDiff ℝ ∞ (blend a₀ a₁) := by
  have hs : ContDiff ℝ ∞ (fun p : ℝ × V => Real.smoothTransition p.1) :=
    Real.smoothTransition.contDiff.comp contDiff_fst
  exact (contDiff_const.sub hs).smul (h₀.comp contDiff_snd) |>.add (hs.smul (h₁.comp contDiff_snd))

lemma curlLinear_combo (D₀ D₁ : V →L[ℝ] V) (r s : ℝ) :
    curlLinear (r • D₀+s • D₁) = r • curlLinear D₀+s • curlLinear D₁ := by
  ext i
  fin_cases i <;> simp [curlLinear] <;> ring

lemma blend_curl (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (t : ℝ) (y : V) :
    curl (blend a₀ a₁) (t,y) =
      (1-Real.smoothTransition t) • curlLinear (fderiv ℝ a₀ y)+
        Real.smoothTransition t • curlLinear (fderiv ℝ a₁ y) := by
  have hd := ((h₀.differentiable (by simp) y).hasFDerivAt.const_smul (1-Real.smoothTransition t)).add
    ((h₁.differentiable (by simp) y).hasFDerivAt.const_smul (Real.smoothTransition t))
  change HasFDerivAt (fun z => blend a₀ a₁ (t,z)) _ y at hd
  rw [curl,← spatialD_eq _ (blend_contDiff a₀ a₁ h₀ h₁),hd.fderiv,curlLinear_combo]

lemma dot_blend (a₀ a₁ c₀ c₁ : V) (s : ℝ) :
    dot ((1-s) • a₀+s • a₁) ((1-s) • c₀+s • c₁) =
      (1-s)*dot a₀ c₀+s*dot a₁ c₁-s*(1-s)*dot (a₁-a₀) (c₁-c₀) := by
  simp [dot]
  ring

lemma blend_volume_positive (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (hpos₀ : ∀ y, 0 < dot (a₀ y) (curlLinear (fderiv ℝ a₀ y)))
    (hpos₁ : ∀ y, 0 < dot (a₁ y) (curlLinear (fderiv ℝ a₁ y)))
    (hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0) :
    ∀ p, 0 < volume (blend a₀ a₁) p := by
  rintro ⟨t,y⟩
  rw [volume,blend_curl a₀ a₁ h₀ h₁]
  change 0 < dot ((1-Real.smoothTransition t) • a₀ y+Real.smoothTransition t • a₁ y) _
  rw [dot_blend,hnull,mul_zero,sub_zero]
  have hs₀ := Real.smoothTransition.nonneg t
  have hs₁ := Real.smoothTransition.le_one t
  have ha := hpos₀ y
  have hb := hpos₁ y
  by_cases hz : Real.smoothTransition t = 0
  · simpa [hz] using ha
  · have hp : 0 < Real.smoothTransition t := lt_of_le_of_ne hs₀ (Ne.symm hz)
    exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs₁) ha.le) (mul_pos hp hb)

lemma velocity_zero_of_constant (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (y : V) (hconst : ∀ t, A (t,y) = A (0,y)) : ∀ t, velocity A (t,y) = 0 := by
  intro t
  have hd := (hA.differentiable (by simp) (t,y)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  change HasDerivAt (fun s => A (s,y)) (velocity A (t,y)) t at hd
  have he : (fun s => A (s,y)) = fun _ => A (0,y) := funext hconst
  rw [he] at hd
  exact hd.unique (hasDerivAt_const t (A (0,y)))

lemma blend_stationary (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (y : V) (hy : a₁ y = a₀ y) : ∀ t, velocity (blend a₀ a₁) (t,y) = 0 := by
  apply velocity_zero_of_constant _ (blend_contDiff a₀ a₁ h₀ h₁) y
  intro t
  simp only [blend,hy]
  ext i
  simp
  ring

theorem relative_integrable_contact_interpolation
    (a₀ a₁ : V → V) (h₀ : ContDiff ℝ ∞ a₀) (h₁ : ContDiff ℝ ∞ a₁)
    (hpos₀ : ∀ y, 0 < dot (a₀ y) (curlLinear (fderiv ℝ a₀ y)))
    (hpos₁ : ∀ y, 0 < dot (a₁ y) (curlLinear (fderiv ℝ a₁ y)))
    (hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0)
    (K : Set V) (hK : IsCompact K) (heq : ∀ y, y ∉ K → a₁ y = a₀ y) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, y ∉ K → ψ t y = y) ∧
      (∀ y, a₁ y = a₀ y → ∀ t, ψ t y = y) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y, Injective (fderiv ℝ (ψ t) y)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        dot (blend a₀ a₁ (t,ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*dot (a₀ y) v) ∧
      ∀ y v, dot (a₁ (ψ 1 y)) (fderiv ℝ (ψ 1) y v) = lam 1 y*dot (a₀ y) v := by
  have hA := blend_contDiff a₀ a₁ h₀ h₁
  have hvol : ∀ p, volume (blend a₀ a₁) p ≠ 0 :=
    fun p => (blend_volume_positive a₀ a₁ h₀ h₁ hpos₀ hpos₁ hnull p).ne'
  obtain ⟨ψ,ρ,lam,hψ,hρ,hlam,hinit,hρψ,hψρ,hfix,hstat,hpos,hinj,hpb⟩ :=
    compact_supported_contact_deformation (blend a₀ a₁) hA hvol K hK (by
      intro t y hy
      exact blend_stationary a₀ a₁ h₀ h₁ y (heq y hy) t)
  have hstart : ∀ y, blend a₀ a₁ (0,y) = a₀ y := by intro y; simp [blend]
  have hend : ∀ y, blend a₀ a₁ (1,y) = a₁ y := by intro y; simp [blend]
  have hp : ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
      dot (blend a₀ a₁ (t,ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*dot (a₀ y) v := by
    intro t ht y v
    simpa only [pullback,form,covector_apply,hstart] using hpb t ht y v
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,hinit,hρψ,hψρ,hfix,?_,hpos,hinj,hp,?_⟩
  · intro y hy
    exact hstat y (blend_stationary a₀ a₁ h₀ h₁ y hy)
  · intro y v
    simpa only [hend] using hp 1 (by simp) y v


abbrev P := Fin 2 → ℝ

/-- A horizontal one-form with a cutoff in the normal coordinate. -/
def horizontalTaper (b : P → P) (χ : ℝ → ℝ) (y : V) : V :=
  ![χ (y 2)*b ![y 0,y 1] 0,χ (y 2)*b ![y 0,y 1] 1,0]

lemma horizontalTaper_contDiff (b : P → P) (χ : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (horizontalTaper b χ) := by
  have hx : ContDiff ℝ ∞ (fun y : V => (![y 0,y 1] : P)) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hbc := hb.comp hx
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [horizontalTaper] <;> fun_prop

lemma horizontalTaper_integrable (b : P → P) (χ : ℝ → ℝ)
    (hb : ContDiff ℝ ∞ b) (hχ : ContDiff ℝ ∞ χ) (y : V) :
    dot (horizontalTaper b χ y) (curlLinear (fderiv ℝ (horizontalTaper b χ) y)) = 0 := by
  let d := horizontalTaper b χ
  have hd : Differentiable ℝ d := (horizontalTaper_contDiff b χ hb hχ).differentiable (by simp)
  have hlast : ∀ v, fderiv ℝ d y v 2 = 0 := by
    intro v
    have hh := (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp y (hd y).hasFDerivAt
    have he : (fun z : V => d z 2) = fun _ => (0:ℝ) := rfl
    change HasFDerivAt (fun z : V => d z 2) _ y at hh
    have hf := hh.fderiv
    rw [he] at hf
    have hv := congrArg (fun L : V →L[ℝ] ℝ => L v) hf
    simpa using hv.symm
  let c : ℝ → V := fun s => ![y 0,y 1,s]
  have hc : HasDerivAt c (Pi.single 2 1) (y 2) := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c] using hasDerivAt_const (y 2) (y 0)
    · simpa [c] using hasDerivAt_const (y 2) (y 1)
    · convert! (hasDerivAt_id (𝕜 := ℝ) (y 2)) using 1
  have hcy : c (y 2) = y := by ext i; fin_cases i <;> rfl
  have hleft := (hd (c (y 2))).hasFDerivAt.comp_hasDerivAt (y 2) hc
  rw [hcy] at hleft
  have heq : (d ∘ c) = fun s => χ s • (![b ![y 0,y 1] 0,b ![y 0,y 1] 1,0] : V) := by
    ext s i
    fin_cases i <;> simp [d,horizontalTaper,c]
  have hright := (hχ.differentiable (by simp) (y 2)).hasDerivAt.smul_const
    (![b ![y 0,y 1] 0,b ![y 0,y 1] 1,0] : V)
  rw [← heq] at hright
  have hz := hleft.unique hright
  dsimp [dot,curlLinear]
  rw [hlast,hlast,hz]
  simp [horizontalTaper]
  ring

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-- A compactly supported smooth flow preserves a vertical fibre whenever its
vector field is vertical on that fibre. The fibre itself need not be compact. -/
lemma flow_preserves_vertical_fibre (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hvertical : ∀ t z, X t ![y 0,y 1,z] 0 = 0 ∧ X t ![y 0,y 1,z] 1 = 0) :
    ∀ t, ψ t y 0 = y 0 ∧ ψ t y 1 = y 1 := by
  let Z : ℝ → ℝ → ℝ := fun t z => X t ![y 0,y 1,z] 2
  have hchart : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1,(![y 0,y 1,p.2] : V))) := by
    apply contDiff_fst.prodMk
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Z p.1 p.2) :=
    (contDiff_apply ℝ ℝ 2).comp (hX.comp hchart)
  obtain ⟨K,hK,hKX⟩ := hsupp
  have hZsupp : ∃ C : Set ℝ, IsCompact C ∧ ∀ t z, z ∉ C → Z t z = 0 := by
    refine ⟨(fun v : V => v 2) '' K,hK.image (continuous_apply 2),?_⟩
    intro t z hz
    have hn : (![y 0,y 1,z] : V) ∉ K := by
      intro h
      exact hz ⟨![y 0,y 1,z],h,rfl⟩
    have he := congrFun (hKX t ![y 0,y 1,z] hn) 2
    exact he
  obtain ⟨γ,hγ,_⟩ := FlowCalculus.exists_unique_global_trajectory_of_compact_support Z hZ hZsupp 0 (y 2)
  let c : ℝ → V := fun t => ![y 0,y 1,γ t]
  have hc0 : c 0 = y := by
    ext i
    fin_cases i <;> simp [c,hγ.1]
  have hc : ∀ t, HasDerivAt c (X t (c t)) t := by
    intro t
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c,(hvertical t (γ t)).1] using hasDerivAt_const t (y 0)
    · simpa [c,(hvertical t (γ t)).2] using hasDerivAt_const t (y 1)
    · exact hγ.2 t
  have he : (fun t => ψ t y) = c :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX ⟨K,hK,hKX⟩ 0 y).unique
      ⟨h0 y,fun t => hflow t y⟩ ⟨hc0,hc⟩
  intro t
  have ht := congrFun he t
  exact ⟨congrFun ht 0,congrFun ht 1⟩

lemma moser_vertical_on_zero_fibre (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (y : V) (hzero : ∀ t z, A (t,![y 0,y 1,z]) 2 = 0) :
    ∀ t z, moser A (t,![y 0,y 1,z]) 0 = 0 ∧ moser A (t,![y 0,y 1,z]) 1 = 0 := by
  intro t z
  have hv : velocity A (t,![y 0,y 1,z]) 2 = 0 := by
    have hd := (hA.differentiable (by simp) (t,![y 0,y 1,z])).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t (![y 0,y 1,z] : V)))
    have hs := (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hd
    change HasDerivAt (fun s => A (s,![y 0,y 1,z]) 2) (velocity A (t,![y 0,y 1,z]) 2) t at hs
    have he : (fun s => A (s,![y 0,y 1,z]) 2) = fun _ => 0 := funext fun s => hzero s z
    rw [he] at hs
    exact hs.unique (hasDerivAt_const t (0:ℝ))
  constructor <;> simp [moser,cross,hzero,hv]

lemma moser_flow_preserves_zero_fibre (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (ψ : ℝ → V → V)
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → moser A (t,y) = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t)
    (y : V) (hzero : ∀ t z, A (t,![y 0,y 1,z]) 2 = 0) :
    ∀ t, ψ t y 0 = y 0 ∧ ψ t y 1 = y 1 :=
  flow_preserves_vertical_fibre (fun t y => moser A (t,y)) ψ (moser_contDiff A hA hvol)
    hsupp h0 hflow y (moser_vertical_on_zero_fibre A hA y hzero)

/-- The same fibre is mapped onto itself, not just into itself. Completeness
of the scalar normal equation gives a preimage for every point of the fibre. -/
lemma flow_surjective_on_vertical_fibre (X ψ : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → X t y = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t)
    (y : V) (hvertical : ∀ t z, X t ![y 0,y 1,z] 0 = 0 ∧ X t ![y 0,y 1,z] 1 = 0)
    (t : ℝ) : ∃ v : V, v 0 = y 0 ∧ v 1 = y 1 ∧ ψ t v = y := by
  let Z : ℝ → ℝ → ℝ := fun s z => X s ![y 0,y 1,z] 2
  have hchart : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1,(![y 0,y 1,p.2] : V))) := by
    apply contDiff_fst.prodMk
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hZ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Z p.1 p.2) :=
    (contDiff_apply ℝ ℝ 2).comp (hX.comp hchart)
  obtain ⟨K,hK,hKX⟩ := hsupp
  have hZsupp : ∃ C : Set ℝ, IsCompact C ∧ ∀ s z, z ∉ C → Z s z = 0 := by
    refine ⟨(fun v : V => v 2) '' K,hK.image (continuous_apply 2),?_⟩
    intro s z hz
    have hn : (![y 0,y 1,z] : V) ∉ K := by
      intro h
      exact hz ⟨![y 0,y 1,z],h,rfl⟩
    exact congrFun (hKX s ![y 0,y 1,z] hn) 2
  obtain ⟨γ,hγ,_⟩ := FlowCalculus.exists_unique_global_trajectory_of_compact_support Z hZ hZsupp t (y 2)
  let c : ℝ → V := fun s => ![y 0,y 1,γ s]
  have hct : c t = y := by
    ext i
    fin_cases i <;> simp [c,hγ.1]
  have hc : ∀ s, HasDerivAt c (X s (c s)) s := by
    intro s
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c,(hvertical s (γ s)).1] using hasDerivAt_const s (y 0)
    · simpa [c,(hvertical s (γ s)).2] using hasDerivAt_const s (y 1)
    · exact hγ.2 s
  have he : (fun s => ψ s (c 0)) = c :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support X hX ⟨K,hK,hKX⟩ 0 (c 0)).unique
      ⟨h0 (c 0),fun s => hflow s (c 0)⟩ ⟨rfl,hc⟩
  exact ⟨c 0,rfl,rfl,(congrFun he t).trans hct⟩

/-- Both directions of transport preserve the zero dividing cylinder for a
common normal coefficient u(x,y), including at its singular zero points. -/
theorem moser_flow_preserves_dividing_cylinder
    (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A) (hvol : ∀ p, volume A p ≠ 0)
    (u : P → ℝ) (hnormal : ∀ t y, A (t,y) 2 = u ![y 0,y 1])
    (ψ ρ : ℝ → V → V)
    (hsupp : ∃ K : Set V, IsCompact K ∧ ∀ t y, y ∉ K → moser A (t,y) = 0)
    (h0 : ∀ y, ψ 0 y = y)
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t)
    (hρψ : ∀ t y, ρ t (ψ t y) = y) :
    ∀ t y, u ![y 0,y 1] = 0 →
      (ψ t y 0 = y 0 ∧ ψ t y 1 = y 1) ∧
      (ρ t y 0 = y 0 ∧ ρ t y 1 = y 1) := by
  intro t y hy
  have hz : ∀ s z, A (s,![y 0,y 1,z]) 2 = 0 := by
    intro s z
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one] using (hnormal s ![y 0,y 1,z]).trans hy
  have hv := moser_vertical_on_zero_fibre A hA y hz
  have hforward := flow_preserves_vertical_fibre (fun s v => moser A (s,v)) ψ
    (moser_contDiff A hA hvol) hsupp h0 hflow y hv t
  obtain ⟨v,hv₀,hv₁,hvψ⟩ := flow_surjective_on_vertical_fibre (fun s v => moser A (s,v)) ψ
    (moser_contDiff A hA hvol) hsupp h0 hflow y hv t
  have hr : ρ t y = v := by rw [← hvψ,hρψ]
  exact ⟨hforward,by simpa only [hr] using And.intro hv₀ hv₁⟩

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def cutoffBase (z : ℝ) : ℝ := Real.smoothTransition (z+2)*Real.smoothTransition (2-z)

lemma cutoffBase_contDiff : ContDiff ℝ ∞ cutoffBase := by
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hs.comp (contDiff_id.add contDiff_const)).mul
    (hs.comp (contDiff_const.sub contDiff_id))

lemma cutoffBase_bounds (z : ℝ) : 0 ≤ cutoffBase z ∧ cutoffBase z ≤ 1 := by
  have h₀ := Real.smoothTransition.nonneg (z+2)
  have h₁ := Real.smoothTransition.le_one (z+2)
  have h₂ := Real.smoothTransition.nonneg (2-z)
  have h₃ := Real.smoothTransition.le_one (2-z)
  exact ⟨mul_nonneg h₀ h₂,by dsimp [cutoffBase]; nlinarith [mul_nonneg (sub_nonneg.mpr h₁) h₂]⟩

lemma cutoffBase_one (z : ℝ) (hz : |z| ≤ 1) : cutoffBase z = 1 := by
  have hl := (abs_le.mp hz).1
  have hr := (abs_le.mp hz).2
  simp [cutoffBase,Real.smoothTransition.one_of_one_le (show 1 ≤ z+2 by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ 2-z by linarith)]

lemma cutoffBase_zero (z : ℝ) (hz : 2 ≤ |z|) : cutoffBase z = 0 := by
  rcases (le_abs.mp hz) with hl | hr
  · simp [cutoffBase,Real.smoothTransition.zero_of_nonpos (show 2-z ≤ 0 by linarith)]
  · simp [cutoffBase,Real.smoothTransition.zero_of_nonpos (show z+2 ≤ 0 by linarith)]

lemma cutoffBase_compact : HasCompactSupport cutoffBase := by
  apply HasCompactSupport.intro' (K := Icc (-2:ℝ) 2) isCompact_Icc isClosed_Icc
  intro z hz
  apply cutoffBase_zero
  by_contra h
  have ha := abs_lt.mp (not_le.mp h)
  exact hz ⟨by linarith [ha.1],by linarith [ha.2]⟩

lemma exists_slow_cutoff (ε : ℝ) (hε : 0 < ε) :
    ∃ χ : ℝ → ℝ, ∃ L : ℝ,
      ContDiff ℝ ∞ χ ∧ 1 ≤ L ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z, |z| ≤ 1 → χ z = 1) ∧
      (∀ z, 2*L ≤ |z| → χ z = 0) ∧
      ∀ z, |deriv χ z| < ε := by
  obtain ⟨B,hB⟩ := (cutoffBase_contDiff.continuous_deriv (by simp)).abs.bddAbove_range_of_hasCompactSupport
    cutoffBase_compact.deriv.abs
  let L : ℝ := (|B|+1)/ε+1
  have hL₁ : 1 ≤ L := by
    dsimp [L]
    have hp : 0 ≤ (|B|+1)/ε := div_nonneg (by positivity) hε.le
    linarith
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hL₁
  have hBL : B < ε*L := by
    dsimp [L]
    have hm : ε*((|B|+1)/ε) = |B|+1 := by field_simp
    nlinarith [le_abs_self B]
  let χ : ℝ → ℝ := fun z => cutoffBase (z/L)
  have hχ : ContDiff ℝ ∞ χ := cutoffBase_contDiff.comp (contDiff_id.div_const L)
  have hzero : ∀ z, 2*L ≤ |z| → χ z = 0 := by
    intro z hz
    apply cutoffBase_zero
    rw [abs_div,abs_of_pos hL]
    exact (le_div_iff₀ hL).mpr (by linarith)
  have hcompact : HasCompactSupport χ := by
    apply HasCompactSupport.intro' (K := Icc (-2*L) (2*L)) isCompact_Icc isClosed_Icc
    intro z hz
    apply hzero
    by_contra h
    have ha := abs_lt.mp (not_le.mp h)
    exact hz ⟨by linarith [ha.1],by linarith [ha.2]⟩
  refine ⟨χ,L,hχ,hL₁,hcompact,fun z => cutoffBase_bounds (z/L),?_,hzero,?_⟩
  · intro z hz
    apply cutoffBase_one
    rw [abs_div,abs_of_pos hL]
    exact (div_le_iff₀ hL).mpr (by linarith)
  · intro z
    have hd := (cutoffBase_contDiff.differentiable (by simp) (z/L)).hasDerivAt.comp z
      ((hasDerivAt_id z).div_const L)
    change HasDerivAt χ _ z at hd
    rw [hd.deriv]
    change |deriv cutoffBase (z/L)*(1/L)| < ε
    rw [abs_mul,abs_div,abs_one,abs_of_pos hL]
    have hb : |deriv cutoffBase (z/L)| ≤ B := hB ⟨z/L,rfl⟩
    have he : |deriv cutoffBase (z/L)|/L < ε := (div_lt_iff₀ hL).mpr (by nlinarith)
    simpa [div_eq_mul_inv] using he

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def xyMap : V →L[ℝ] P := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ),ContinuousLinearMap.proj 1]

@[simp] lemma xyMap_apply (y : V) : xyMap y = ![y 0,y 1] := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e0 : xyMap (Pi.single 0 1) = Pi.single 0 1 := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e1 : xyMap (Pi.single 1 1) = Pi.single 1 1 := by ext i; fin_cases i <;> simp [xyMap]
@[simp] lemma xyMap_e2 : xyMap (Pi.single 2 1) = 0 := by ext i; fin_cases i <;> simp [xyMap]

def invariantCoefficients (u : P → ℝ) (β : P → P) (y : V) : V :=
  ![β (xyMap y) 0,β (xyMap y) 1,u (xyMap y)]

def collarCoefficients (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ) (y : V) : V :=
  ![β₀ (xyMap y) 0+χ (y 2)*(β₁ (xyMap y) 0-β₀ (xyMap y) 0),
    β₀ (xyMap y) 1+χ (y 2)*(β₁ (xyMap y) 1-β₀ (xyMap y) 1),u (xyMap y)]

def invariantVolume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)

def cutoffError (β₀ β₁ : P → P) (x : P) : ℝ :=
  β₀ x 1*(β₁ x 0-β₀ x 0)-β₀ x 0*(β₁ x 1-β₀ x 1)

lemma invariantCoefficients_contDiff (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (invariantCoefficients u β) := by
  have huc := hu.comp xyMap.contDiff
  have hβc := hβ.comp xyMap.contDiff
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [invariantCoefficients] <;> fun_prop

lemma collarCoefficients_contDiff (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) : ContDiff ℝ ∞ (collarCoefficients u β₀ β₁ χ) := by
  have huc := hu.comp xyMap.contDiff
  have hβc₀ := h₀.comp xyMap.contDiff
  have hβc₁ := h₁.comp xyMap.contDiff
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [collarCoefficients] <;> fun_prop

lemma invariantVolume_contDiff (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) : ContDiff ℝ ∞ (invariantVolume u β) := by
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hdβ : ContDiff ℝ ∞ (fderiv ℝ β) := hβ.fderiv_right (by simp)
  unfold invariantVolume
  fun_prop

lemma cutoffError_contDiff (β₀ β₁ : P → P) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁) :
    ContDiff ℝ ∞ (cutoffError β₀ β₁) := by unfold cutoffError; fun_prop

lemma collarCoefficients_fderiv (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) (y v : V) :
    fderiv ℝ (collarCoefficients u β₀ β₁ χ) y v =
      ![fderiv ℝ β₀ (xyMap y) (xyMap v) 0+
          (deriv χ (y 2)*v 2)*(β₁ (xyMap y) 0-β₀ (xyMap y) 0)+
          χ (y 2)*(fderiv ℝ β₁ (xyMap y) (xyMap v) 0-fderiv ℝ β₀ (xyMap y) (xyMap v) 0),
        fderiv ℝ β₀ (xyMap y) (xyMap v) 1+
          (deriv χ (y 2)*v 2)*(β₁ (xyMap y) 1-β₀ (xyMap y) 1)+
          χ (y 2)*(fderiv ℝ β₁ (xyMap y) (xyMap v) 1-fderiv ℝ β₀ (xyMap y) (xyMap v) 1),
        fderiv ℝ u (xyMap y) (xyMap v)] := by
  have hb₀ := (h₀.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hb₁ := (h₁.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hb₀₀ := (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₀
  have hb₀₁ := (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₀
  have hb₁₀ := (ContinuousLinearMap.proj 0 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₁
  have hb₁₁ := (ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt.comp y hb₁
  have hr := (hχ.differentiable (by simp) (y 2)).hasDerivAt.hasFDerivAt.comp y
    (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt
  have hU := (hu.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hd₀ := hb₀₀.add (hr.mul (hb₁₀.sub hb₀₀))
  have hd₁ := hb₀₁.add (hr.mul (hb₁₁.sub hb₀₁))
  let f₀ : V → ℝ := fun q => β₀ (xyMap q) 0+χ (q 2)*(β₁ (xyMap q) 0-β₀ (xyMap q) 0)
  let f₁ : V → ℝ := fun q => β₀ (xyMap q) 1+χ (q 2)*(β₁ (xyMap q) 1-β₀ (xyMap q) 1)
  change HasFDerivAt f₀ _ y at hd₀
  change HasFDerivAt f₁ _ y at hd₁
  have hD : HasFDerivAt (collarCoefficients u β₀ β₁ χ)
      (ContinuousLinearMap.pi ![fderiv ℝ f₀ y,fderiv ℝ f₁ y,
        (fderiv ℝ u (xyMap y)).comp xyMap]) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · change HasFDerivAt f₀ (fderiv ℝ f₀ y) y
      exact hd₀.differentiableAt.hasFDerivAt
    · change HasFDerivAt f₁ (fderiv ℝ f₁ y) y
      exact hd₁.differentiableAt.hasFDerivAt
    · exact hU
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [hd₀.fderiv,hd₁.fderiv] <;> ring

lemma collar_volume_formula (u : P → ℝ) (β₀ β₁ : P → P) (χ : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hχ : ContDiff ℝ ∞ χ) (y : V) :
    dot (collarCoefficients u β₀ β₁ χ y)
      (curlLinear (fderiv ℝ (collarCoefficients u β₀ β₁ χ) y)) =
      (1-χ (y 2))*invariantVolume u β₀ (xyMap y)+χ (y 2)*invariantVolume u β₁ (xyMap y)+
        deriv χ (y 2)*cutoffError β₀ β₁ (xyMap y) := by
  dsimp [dot,curlLinear]
  rw [collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ,
    collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ,
    collarCoefficients_fderiv u β₀ β₁ χ hu h₀ h₁ hχ]
  simp only [xyMap_e0,xyMap_e1,xyMap_e2,map_zero]
  simp [invariantVolume,cutoffError,collarCoefficients]
  ring

lemma invariant_volume_formula (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (y : V) :
    dot (invariantCoefficients u β y) (curlLinear (fderiv ℝ (invariantCoefficients u β) y)) =
      invariantVolume u β (xyMap y) := by
  have he : collarCoefficients u β β (fun _ => 0) = invariantCoefficients u β := by
    ext q i
    fin_cases i <;> simp [collarCoefficients,invariantCoefficients]
  simpa only [he,deriv_const,mul_zero,zero_mul,add_zero,sub_zero,one_mul] using
    collar_volume_formula u β β (fun _ => 0) hu hβ hβ contDiff_const y

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma exists_positive_collar_cutoff (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (K : Set P) (hK : IsCompact K) (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    ∃ χ : ℝ → ℝ, ∃ L : ℝ,
      ContDiff ℝ ∞ χ ∧ 1 ≤ L ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ (∀ z, |z| ≤ 1 → χ z = 1) ∧
      (∀ z, 2*L ≤ |z| → χ z = 0) ∧
      (∀ y, 0 < dot (collarCoefficients u β₀ β₁ χ y)
        (curlLinear (fderiv ℝ (collarCoefficients u β₀ β₁ χ) y))) ∧
      ∃ C : Set V, IsCompact C ∧
        ∀ y, y ∉ C → horizontalTaper (fun x => β₁ x-β₀ x) χ y = 0 := by
  obtain ⟨m₀,hm₀,hbound₀⟩ := hK.exists_forall_le'
    (invariantVolume_contDiff u β₀ hu h₀).continuous.continuousOn (fun x _ => hpos₀ x)
  obtain ⟨m₁,hm₁,hbound₁⟩ := hK.exists_forall_le'
    (invariantVolume_contDiff u β₁ hu h₁).continuous.continuousOn (fun x _ => hpos₁ x)
  let m : ℝ := min m₀ m₁
  have hm : 0 < m := lt_min hm₀ hm₁
  obtain ⟨B,hB⟩ := hK.bddAbove_image (cutoffError_contDiff β₀ β₁ h₀ h₁).continuous.abs.continuousOn
  let M : ℝ := |B|+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : ∀ x ∈ K, |cutoffError β₀ β₁ x| ≤ M := by
    intro x hx
    have hb := hB ⟨x,hx,rfl⟩
    dsimp [M]
    linarith [le_abs_self B]
  let ε : ℝ := m/(2*M)
  have hε : 0 < ε := div_pos hm (mul_pos (by norm_num) hM)
  obtain ⟨χ,L,hχ,hL,hcompact,hrange,hone,hzero,hderiv⟩ := exists_slow_cutoff ε hε
  refine ⟨χ,L,hχ,hL,hrange,hone,hzero,?_,?_⟩
  · intro y
    rw [collar_volume_formula u β₀ β₁ χ hu h₀ h₁ hχ]
    have hr₀ := (hrange (y 2)).1
    have hr₁ := (hrange (y 2)).2
    by_cases hx : xyMap y ∈ K
    · have ha : m ≤ invariantVolume u β₀ (xyMap y) :=
        (min_le_left _ _).trans (hbound₀ _ hx)
      have hb : m ≤ invariantVolume u β₁ (xyMap y) :=
        (min_le_right _ _).trans (hbound₁ _ hx)
      have hbase : m ≤ (1-χ (y 2))*invariantVolume u β₀ (xyMap y)+
          χ (y 2)*invariantVolume u β₁ (xyMap y) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hr₁) (sub_nonneg.mpr ha),
          mul_nonneg hr₀ (sub_nonneg.mpr hb)]
      have herr : |deriv χ (y 2)*cutoffError β₀ β₁ (xyMap y)| < ε*M := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (hE _ hx) (abs_nonneg _)).trans_lt
          (mul_lt_mul_of_pos_right (hderiv _) hM)
      have hEM : ε*M = m/2 := by dsimp [ε]; field_simp
      rw [hEM] at herr
      linarith [(abs_lt.mp herr).1]
    · have hz : cutoffError β₀ β₁ (xyMap y) = 0 := by
        dsimp only [cutoffError]
        rw [heq _ hx]
        ring
      rw [hz,mul_zero,add_zero]
      have ha := hpos₀ (xyMap y)
      have hb := hpos₁ (xyMap y)
      by_cases hr : χ (y 2) = 0
      · simpa [hr] using ha
      · have hp : 0 < χ (y 2) := lt_of_le_of_ne hr₀ (Ne.symm hr)
        exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hr₁) ha.le) (mul_pos hp hb)
  · let join : P × ℝ → V := fun q => ![q.1 0,q.1 1,q.2]
    have hjoin : Continuous join := by
      apply continuous_pi
      intro i
      fin_cases i <;> dsimp [join] <;> fun_prop
    refine ⟨join '' (K ×ˢ Icc (-2*L) (2*L)),(hK.prod isCompact_Icc).image hjoin,?_⟩
    intro y hy
    by_cases hx : xyMap y ∈ K
    · have hz : 2*L ≤ |y 2| := by
        by_contra hn
        have ha := abs_lt.mp (not_le.mp hn)
        apply hy
        refine ⟨(xyMap y,y 2),⟨hx,by constructor <;> linarith [ha.1,ha.2]⟩,?_⟩
        ext i
        fin_cases i <;> simp [join]
      simp [horizontalTaper,hzero _ hz]
    · have hh := heq _ hx
      rw [xyMap_apply] at hh
      simp [horizontalTaper,hh]

lemma given_moser_flow_pullback (A : ℝ × V → V) (hA : ContDiff ℝ ∞ A)
    (hvol : ∀ p, volume A p ≠ 0) (ψ : ℝ → V → V)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hbij : ∀ t, Bijective (ψ t))
    (hflow : ∀ t y, HasDerivAt (fun s => ψ s y) (moser A (t,ψ t y)) t) :
    ∃ lam : ℝ → V → ℝ, ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ t y, 0 < lam t y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ y v,
        pullback (ψ t) (form A t) y v = lam t y*form A 0 y v := by
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  let q : ℝ → V → ℝ := fun t y => rate A (t,ψ t y)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × V => q p.1 p.2) :=
    (rate_contDiff A hA hvol).comp (contDiff_fst.prodMk hψ)
  obtain ⟨lam,hlam,_,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  refine ⟨lam,hlam,hpos,?_⟩
  intro t ht y v
  have hform : IsSmoothFamily (form A) := covector.contDiff.comp hA
  have hf : ∀ s ∈ Icc (0:ℝ) 1,
      HasDerivAt (fun r => pullback (ψ r) (form A r) y v)
        (q s y*pullback (ψ s) (form A s) y v) s := by
    intro s hs
    have hd := GrayStability.pullback_family_hasDerivAt (form A) hform X hX ψ hψ h0 hbij hflow s y v
    have he := moser_lie_equation A hA hvol s (ψ s y) (fderiv ℝ (ψ s) y v)
    change formTimeDeriv (form A) s (ψ s y) (fderiv ℝ (ψ s) y v)+
      lieDerivOneForm (X s) (form A s) (ψ s y) (fderiv ℝ (ψ s) y v) = _ at he
    rw [he] at hd
    exact hd
  have hinit : pullback (ψ 0) (form A 0) y v = form A 0 y v := by
    have hid : ψ 0 = id := funext h0
    simp [pullback,hid]
  simpa only [hinit] using htransport y (fun r => pullback (ψ r) (form A r) y v) hf t ht

theorem global_invariant_collar_realization (u : P → ℝ) (β₀ β₁ : P → P)
    (hu : ContDiff ℝ ∞ u) (h₀ : ContDiff ℝ ∞ β₀) (h₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < invariantVolume u β₀ x) (hpos₁ : ∀ x, 0 < invariantVolume u β₁ x)
    (K : Set P) (hK : IsCompact K) (heq : ∀ x, x ∉ K → β₁ x = β₀ x) :
    ∃ H G : ℝ → V → V, ∃ σ : ℝ → V → ℝ, ∃ C : Set V,
      ContDiff ℝ ∞ (fun p : ℝ × V => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => G p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => σ p.1 p.2) ∧
      IsCompact C ∧ (∀ y, H 0 y = y) ∧
      (∀ t y, H t (G t y) = y) ∧ (∀ t y, G t (H t y) = y) ∧
      (∀ t y, y ∉ C → H t y = y) ∧
      (∀ t y, 0 < σ t y) ∧
      (∀ t y, u (xyMap y) = 0 →
        (H t y 0 = y 0 ∧ H t y 1 = y 1) ∧ (G t y 0 = y 0 ∧ G t y 1 = y 1)) ∧
      ∀ y, |y 2| ≤ 1 → ∀ v,
        dot (invariantCoefficients u β₀ (H 1 y)) (fderiv ℝ (H 1) y v) =
          σ 1 y*dot (invariantCoefficients u β₁ y) v := by
  obtain ⟨χ,L,hχ,hL,hrange,hone,hzero,hpositive,C,hC,hsupport⟩ :=
    exists_positive_collar_cutoff u β₀ β₁ hu h₀ h₁ hpos₀ hpos₁ K hK heq
  let a₀ := invariantCoefficients u β₀
  let a₁ := collarCoefficients u β₀ β₁ χ
  have ha₀ : ContDiff ℝ ∞ a₀ := invariantCoefficients_contDiff u β₀ hu h₀
  have ha₁ : ContDiff ℝ ∞ a₁ := collarCoefficients_contDiff u β₀ β₁ χ hu h₀ h₁ hχ
  have heqa : a₁ = fun y => a₀ y+horizontalTaper (fun x => β₁ x-β₀ x) χ y := by
    ext y i
    fin_cases i <;> simp [a₀,a₁,collarCoefficients,invariantCoefficients,horizontalTaper]
  have hnull : ∀ y, dot (a₁ y-a₀ y)
      (curlLinear (fderiv ℝ a₁ y)-curlLinear (fderiv ℝ a₀ y)) = 0 := by
    intro y
    have hd := horizontalTaper_contDiff (fun x => β₁ x-β₀ x) χ (h₁.sub h₀) hχ
    have hder := ((ha₀.differentiable (by simp) y).hasFDerivAt.add
      (hd.differentiable (by simp) y).hasFDerivAt).fderiv
    change fderiv ℝ (fun z => a₀ z+horizontalTaper (fun x => β₁ x-β₀ x) χ z) y = _ at hder
    rw [← heqa] at hder
    have hc : curlLinear (fderiv ℝ a₁ y) = curlLinear (fderiv ℝ a₀ y)+
        curlLinear (fderiv ℝ (horizontalTaper (fun x => β₁ x-β₀ x) χ) y) := by
      rw [hder]
      simpa using curlLinear_combo (fderiv ℝ a₀ y)
        (fderiv ℝ (horizontalTaper (fun x => β₁ x-β₀ x) χ) y) 1 1
    rw [hc,heqa]
    simpa only [add_sub_cancel_left,add_sub_cancel_right] using
      horizontalTaper_integrable (fun x => β₁ x-β₀ x) χ (h₁.sub h₀) hχ y
  let A := blend a₀ a₁
  have hA : ContDiff ℝ ∞ A := blend_contDiff a₀ a₁ ha₀ ha₁
  have hvol : ∀ p, volume A p ≠ 0 := by
    apply fun p => (blend_volume_positive a₀ a₁ ha₀ ha₁ ?_ hpositive hnull p).ne'
    intro y
    rw [invariant_volume_formula u β₀ hu h₀]
    exact hpos₀ _
  let X : ℝ → V → V := fun t y => moser A (t,y)
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := moser_contDiff A hA hvol
  have hXout : ∀ t y, y ∉ C → X t y = 0 := by
    intro t y hy
    have he : a₁ y = a₀ y := by
      rw [heqa]
      dsimp only
      rw [hsupport y hy,add_zero]
    have hv := blend_stationary a₀ a₁ ha₀ ha₁ y he t
    simp [X,moser,A,hv,cross]
  have hsupp : ∃ D : Set V, IsCompact D ∧ ∀ t y, y ∉ D → X t y = 0 := ⟨C,hC,hXout⟩
  obtain ⟨ψ,hψ,hψ0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ hψ0 hbij hflow
  obtain ⟨lam,hlam,hpos,hpb⟩ := given_moser_flow_pullback A hA hvol ψ hψ hψ0 hbij hflow
  let σ : ℝ → V → ℝ := fun t y => (lam t (ρ t y))⁻¹
  have hσ : ContDiff ℝ ∞ (fun p : ℝ × V => σ p.1 p.2) :=
    (hlam.comp (contDiff_fst.prodMk hρ)).inv (fun p => (hpos p.1 (ρ p.1 p.2)).ne')
  have hnormal : ∀ t y, A (t,y) 2 = u (xyMap y) := by
    intro t y
    simp [A,blend,a₀,a₁,collarCoefficients,invariantCoefficients]
    ring
  have hdiv := moser_flow_preserves_dividing_cylinder A hA hvol u (by
    intro t y
    rw [hnormal,xyMap_apply]) ψ ρ hsupp hψ0 hflow hρψ
  have hfix : ∀ t y, y ∉ C → ψ t y = y := by
    intro t y hy
    exact ambient_flow_fixes X ψ hX hsupp hψ0 hflow y (fun s => hXout s y hy) t
  refine ⟨ρ,ψ,σ,C,hρ,hψ,hσ,hC,?_,hρψ,hψρ,?_,?_,?_,?_⟩
  · intro y
    simpa only [hψ0] using hψρ 0 y
  · intro t y hy
    have hh := hρψ t y
    rw [hfix t y hy] at hh
    exact hh
  · intro t y
    exact inv_pos.mpr (hpos t (ρ t y))
  · intro t y hy
    rw [xyMap_apply] at hy
    exact (hdiv t y hy).symm
  · intro y hy v
    have hψs : ContDiff ℝ ∞ (ψ 1) := hψ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ (fun z : V => ((1:ℝ),z)))
    have hρs : ContDiff ℝ ∞ (ρ 1) := hρ.comp (contDiff_const.prodMk contDiff_id :
      ContDiff ℝ ∞ (fun z : V => ((1:ℝ),z)))
    have hchain : fderiv ℝ (ψ 1) (ρ 1 y) (fderiv ℝ (ρ 1) y v) = v := by
      have hd := fderiv_comp y (hψs.differentiable (by simp) _) (hρs.differentiable (by simp) _)
      have hid : ψ 1 ∘ ρ 1 = id := funext (hψρ 1)
      have hh := congrArg (fun T : V →L[ℝ] V => T v) hd
      simpa [hid,id_eq] using hh.symm
    have hp := hpb 1 (by simp) (ρ 1 y) (fderiv ℝ (ρ 1) y v)
    have hstart : ∀ z, A (0,z) = a₀ z := by intro z; simp [A,blend]
    change dot (A (1,ψ 1 (ρ 1 y))) (fderiv ℝ (ψ 1) (ρ 1 y) (fderiv ℝ (ρ 1) y v)) =
      lam 1 (ρ 1 y)*dot (A (0,ρ 1 y)) (fderiv ℝ (ρ 1) y v) at hp
    rw [hψρ,hchain,hstart] at hp
    have hend : A (1,y) = invariantCoefficients u β₁ y := by
      simp [A,blend,a₁,collarCoefficients,invariantCoefficients,hone _ hy]
    rw [hend] at hp
    change dot (a₀ (ρ 1 y)) (fderiv ℝ (ρ 1) y v) =
      (lam 1 (ρ 1 y))⁻¹*dot (invariantCoefficients u β₁ y) v
    rw [hp,← mul_assoc,inv_mul_cancel₀ (hpos 1 (ρ 1 y)).ne',one_mul]

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def planarCharacteristic (u : P → ℝ) (β : P → P) (x : P) : P :=
  (u x/invariantVolume u β x) • ![β x 1,-β x 0]

lemma planarCharacteristic_boundary_tangent (u : P → ℝ) (β : P → P) (x : P)
    (hLegendrian : β x 0*(-x 1)+β x 1*x 0 = 0) :
    x 0*planarCharacteristic u β x 0+x 1*planarCharacteristic u β x 1 = 0 := by
  dsimp [planarCharacteristic]
  nlinarith [mul_eq_zero_of_right (u x/invariantVolume u β x) hLegendrian]

/-- The coefficient-level contact Hamiltonian field. -/
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
lemma invariant_compression_field_formula (u : P → ℝ) (β : P → P)
    (h : ℝ → ℝ) (y : V) (hQ : invariantVolume u β (xyMap y) ≠ 0) :
    let x := xyMap y
    let c : V := ![fderiv ℝ u x (Pi.single 1 1),-fderiv ℝ u x (Pi.single 0 1),
      fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0]
    let g : V := ![h (y 2)*fderiv ℝ u x (Pi.single 0 1),
      h (y 2)*fderiv ℝ u x (Pi.single 1 1),deriv h (y 2)*u x]
    hamiltonianAlgebra (invariantCoefficients u β y) c (h (y 2)*u x) g =
      ![deriv h (y 2)*planarCharacteristic u β x 0,
        deriv h (y 2)*planarCharacteristic u β x 1,h (y 2)] := by
  dsimp only
  have hvol : dot (invariantCoefficients u β y)
      ![fderiv ℝ u (xyMap y) (Pi.single 1 1),-fderiv ℝ u (xyMap y) (Pi.single 0 1),
        fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0] =
      invariantVolume u β (xyMap y) := by
    simp [dot,invariantCoefficients,invariantVolume]
    ring
  unfold hamiltonianAlgebra
  rw [hvol]
  ext i
  fin_cases i
  · simp [invariantCoefficients,planarCharacteristic,cross,div_eq_mul_inv]
    ring
  · simp [invariantCoefficients,planarCharacteristic,cross,div_eq_mul_inv]
    ring
  · change (invariantVolume u β (xyMap y))⁻¹ * _ = h (y 2)
    have hn : (h (y 2)*u (xyMap y))*
          (fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0)+
        (cross (invariantCoefficients u β y)
          ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
            h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)]) 2 =
        h (y 2)*invariantVolume u β (xyMap y) := by
      simp [cross,invariantCoefficients,invariantVolume]
      ring
    change (invariantVolume u β (xyMap y))⁻¹ *
      ((h (y 2)*u (xyMap y))*
        (fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0)+
        (cross (invariantCoefficients u β y)
          ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
            h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)]) 2) = h (y 2)
    rw [hn]
    calc (invariantVolume u β (xyMap y))⁻¹*(h (y 2)*invariantVolume u β (xyMap y)) =
        h (y 2)*((invariantVolume u β (xyMap y))⁻¹*invariantVolume u β (xyMap y)) := by ring
      _ = h (y 2) := by rw [inv_mul_cancel₀ hQ,mul_one]

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

lemma invariant_curl_formula (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (y : V) :
    curlLinear (fderiv ℝ (invariantCoefficients u β) y) =
      ![fderiv ℝ u (xyMap y) (Pi.single 1 1),-fderiv ℝ u (xyMap y) (Pi.single 0 1),
        fderiv ℝ β (xyMap y) (Pi.single 0 1) 1-fderiv ℝ β (xyMap y) (Pi.single 1 1) 0] := by
  have he : collarCoefficients u β β (fun _ => 0) = invariantCoefficients u β := by
    ext q i
    fin_cases i <;> simp [collarCoefficients,invariantCoefficients]
  have hD := collarCoefficients_fderiv u β β (fun _ => 0) hu hβ hβ contDiff_const y
  rw [he] at hD
  ext i
  fin_cases i <;> dsimp [curlLinear] <;> rw [hD,hD] <;>
    simp only [xyMap_e0,xyMap_e1,xyMap_e2,map_zero] <;> simp

def normalHamiltonian (u : P → ℝ) (h : ℝ → ℝ) (y : V) : ℝ := h (y 2)*u (xyMap y)

lemma normalHamiltonian_gradient (u : P → ℝ) (h : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h) (y : V) :
    gradient3 (normalHamiltonian u h) y =
      ![h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 0 1),
        h (y 2)*fderiv ℝ u (xyMap y) (Pi.single 1 1),deriv h (y 2)*u (xyMap y)] := by
  have hr := (hh.differentiable (by simp) (y 2)).hasDerivAt.hasFDerivAt.comp y
    (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt
  have hU := (hu.differentiable (by simp) (xyMap y)).hasFDerivAt.comp y xyMap.hasFDerivAt
  have hd := hr.mul hU
  change HasFDerivAt (normalHamiltonian u h) _ y at hd
  unfold gradient3
  rw [hd.fderiv]
  ext i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      xyMap_e0,xyMap_e1,xyMap_e2,map_zero] <;> simp [mul_comm]

def compressionField (u : P → ℝ) (β : P → P) (h : ℝ → ℝ) (y : V) : V :=
  ![deriv h (y 2)*planarCharacteristic u β (xyMap y) 0,
    deriv h (y 2)*planarCharacteristic u β (xyMap y) 1,h (y 2)]

theorem compressionField_is_contact (u : P → ℝ) (β : P → P) (h : ℝ → ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (hh : ContDiff ℝ ∞ h)
    (hpositive : ∀ x, 0 < invariantVolume u β x) :
    ContDiff ℝ ∞ (compressionField u β h) ∧
      ∀ y, ∃ μ : ℝ, ∀ v,
        lieDerivOneForm (compressionField u β h) (fun z => covector (invariantCoefficients u β z)) y v =
          μ*covector (invariantCoefficients u β y) v := by
  let a := invariantCoefficients u β
  let H := normalHamiltonian u h
  have ha : ContDiff ℝ ∞ a := invariantCoefficients_contDiff u β hu hβ
  have hH : ContDiff ℝ ∞ H :=
    (hh.comp (contDiff_apply ℝ ℝ 2)).mul (hu.comp xyMap.contDiff)
  have hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0 := by
    intro y
    rw [invariant_volume_formula u β hu hβ]
    exact (hpositive _).ne'
  have he : hamiltonianField a H = compressionField u β h := by
    funext y
    dsimp only [hamiltonianField,a,H]
    rw [invariant_curl_formula u β hu hβ,normalHamiltonian_gradient u h hu hh]
    simpa only [normalHamiltonian,compressionField] using
      invariant_compression_field_formula u β h y (hpositive _).ne'
  constructor
  · rw [← he]
    exact hamiltonianField_contDiff a H ha hH hQ
  · intro y
    refine ⟨dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/dot (a y) (curlLinear (fderiv ℝ a y)),?_⟩
    intro v
    rw [← he]
    exact hamiltonianField_lie a H ha hH hQ y v

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def diskSq (x : P) : ℝ := x 0^2+x 1^2
def diskCutoff (x : P) : ℝ := Real.smoothTransition (4-diskSq x)

lemma diskSq_contDiff : ContDiff ℝ ∞ diskSq := by unfold diskSq; fun_prop
lemma diskCutoff_contDiff : ContDiff ℝ ∞ diskCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub diskSq_contDiff)

lemma diskCutoff_one (x : P) (hx : diskSq x < 2) : diskCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma diskCutoff_compact : HasCompactSupport diskCutoff := by
  apply HasCompactSupport.intro' (K := Icc (![-2,-2]:P) ![2,2]) isCompact_Icc isClosed_Icc
  intro x hx
  by_cases hr : 4 ≤ diskSq x
  · exact Real.smoothTransition.zero_of_nonpos (by linarith)
  · have hs : diskSq x < 4 := not_le.mp hr
    have h₀ : -2 ≤ x 0 ∧ x 0 ≤ 2 := by dsimp [diskSq] at hs; constructor <;> nlinarith [sq_nonneg (x 1)]
    have h₁ : -2 ≤ x 1 ∧ x 1 ≤ 2 := by dsimp [diskSq] at hs; constructor <;> nlinarith [sq_nonneg (x 0)]
    apply (hx ?_).elim
    constructor
    · intro i
      fin_cases i
      · exact h₀.1
      · exact h₁.1
    · intro i
      fin_cases i
      · exact h₀.2
      · exact h₁.2


def normalSpeed (ε z : ℝ) : ℝ := expNegInvGlue (ε^2-z^2)/expNegInvGlue (ε^2)

lemma normalSpeed_contDiff (ε : ℝ) : ContDiff ℝ ∞ (normalSpeed ε) :=
  (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))).div_const _

lemma normalSpeed_nonneg (ε z : ℝ) : 0 ≤ normalSpeed ε z :=
  div_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)

lemma normalSpeed_zero (ε z : ℝ) (hε : 0 < ε) (hz : ε ≤ |z|) : normalSpeed ε z = 0 := by
  have hs : ε^2 ≤ z^2 := by nlinarith [sq_nonneg (|z|-ε),sq_abs z]
  simp [normalSpeed,expNegInvGlue.zero_of_nonpos (show ε^2-z^2 ≤ 0 by linarith)]

lemma normalSpeed_pos (ε z : ℝ) (hε : 0 < ε) (hz : |z| < ε) : 0 < normalSpeed ε z := by
  have hs : 0 < ε^2-z^2 := by
    have ha := abs_lt.mp hz
    nlinarith [mul_pos (sub_pos.mpr ha.2) (by linarith : 0 < ε+z)]
  exact div_pos (expNegInvGlue.pos_of_pos hs) (expNegInvGlue.pos_of_pos (sq_pos_of_pos hε))

lemma normalSpeed_at_zero (ε : ℝ) (hε : 0 < ε) : normalSpeed ε 0 = 1 := by
  simp [normalSpeed,(expNegInvGlue.pos_of_pos (sq_pos_of_pos hε)).ne']

lemma normalSpeed_deriv_zero (ε z : ℝ) (hε : 0 < ε) (hz : ε ≤ |z|) :
    deriv (normalSpeed ε) z = 0 := by
  have hmin : IsLocalMin (normalSpeed ε) z := Eventually.of_forall fun w => by
    rw [normalSpeed_zero ε z hε hz]
    exact normalSpeed_nonneg ε w
  exact hmin.deriv_eq_zero

lemma normalSpeed_compact (ε : ℝ) (hε : 0 < ε) : HasCompactSupport (normalSpeed ε) := by
  apply HasCompactSupport.intro' (K := Icc (-ε) ε) isCompact_Icc isClosed_Icc
  intro z hz
  apply normalSpeed_zero ε z hε
  by_contra hn
  exact hz (abs_le.mp (not_le.mp hn).le)

def localizedHamiltonian (u : P → ℝ) (ε : ℝ) (y : V) : ℝ :=
  diskCutoff (xyMap y)*normalHamiltonian u (normalSpeed ε) y

lemma localizedHamiltonian_contDiff (u : P → ℝ) (hu : ContDiff ℝ ∞ u) (ε : ℝ) :
    ContDiff ℝ ∞ (localizedHamiltonian u ε) :=
  (diskCutoff_contDiff.comp xyMap.contDiff).mul
    (((normalSpeed_contDiff ε).comp (contDiff_apply ℝ ℝ 2)).mul (hu.comp xyMap.contDiff))

lemma localizedHamiltonian_compact (u : P → ℝ) (ε : ℝ) (hε : 0 < ε) :
    HasCompactSupport (localizedHamiltonian u ε) := by
  let join : P × ℝ → V := fun q => ![q.1 0,q.1 1,q.2]
  have hjoin : Continuous join := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp [join] <;> fun_prop
  let C := join '' (tsupport diskCutoff ×ˢ Icc (-ε) ε)
  have hC : IsCompact C := (diskCutoff_compact.prod isCompact_Icc).image hjoin
  apply HasCompactSupport.intro' hC hC.isClosed
  intro y hy
  by_cases hx : xyMap y ∈ tsupport diskCutoff
  · have hz : ε ≤ |y 2| := by
      by_contra hn
      apply hy
      refine ⟨(xyMap y,y 2),⟨hx,abs_le.mp (not_le.mp hn).le⟩,?_⟩
      ext i
      fin_cases i <;> simp [join]
    simp [localizedHamiltonian,normalHamiltonian,normalSpeed_zero ε (y 2) hε hz]
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [localizedHamiltonian,hz,zero_mul]

lemma hamiltonianField_compact (a : V → V) (H : V → ℝ) (hH : HasCompactSupport H) :
    HasCompactSupport (hamiltonianField a H) := by
  apply HasCompactSupport.intro' hH (isClosed_tsupport H)
  intro y hy
  have hv := image_eq_zero_of_notMem_tsupport hy
  have hd := fderiv_of_notMem_tsupport ℝ hy
  simp [hamiltonianField,hamiltonianAlgebra,gradient3,hv,hd,cross]

lemma localizedHamiltonian_agrees (u : P → ℝ) (ε : ℝ) (y : V) (hy : diskSq (xyMap y) ≤ 1) :
    localizedHamiltonian u ε =ᶠ[𝓝 y] normalHamiltonian u (normalSpeed ε) := by
  have ho : IsOpen {z : V | diskSq (xyMap z) < 2} :=
    isOpen_lt (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const
  filter_upwards [ho.mem_nhds (show diskSq (xyMap y) < 2 by linarith)] with z hz
  simp only [localizedHamiltonian,diskCutoff_one _ hz,one_mul]

lemma localizedField_agrees (u : P → ℝ) (β : P → P) (ε : ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hpos : ∀ x, 0 < invariantVolume u β x) (y : V) (hy : diskSq (xyMap y) ≤ 1) :
    hamiltonianField (invariantCoefficients u β) (localizedHamiltonian u ε) y =
      compressionField u β (normalSpeed ε) y := by
  have he := localizedHamiltonian_agrees u ε y hy
  have hg : gradient3 (localizedHamiltonian u ε) y = gradient3 (normalHamiltonian u (normalSpeed ε)) y := by
    unfold gradient3
    rw [he.fderiv_eq]
  unfold hamiltonianField
  rw [he.eq_of_nhds,hg,invariant_curl_formula u β hu hβ,
    normalHamiltonian_gradient u (normalSpeed ε) hu (normalSpeed_contDiff ε)]
  simpa only [normalHamiltonian,compressionField] using
    invariant_compression_field_formula u β (normalSpeed ε) y (hpos _).ne'

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def hamiltonianRate (a : V → V) (H : V → ℝ) (y : V) : ℝ :=
  dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)/dot (a y) (curlLinear (fderiv ℝ a y))

lemma hamiltonianRate_contDiff (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ContDiff ℝ ∞ (hamiltonianRate a H) := by
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
  have hn : ContDiff ℝ ∞ (fun y => dot (curlLinear (fderiv ℝ a y)) (gradient3 H y)) := by
    unfold dot
    fun_prop
  exact hn.div hq hQ

lemma hamiltonian_derivative (a : V → V) (H : V → ℝ)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) (y : V) :
    fderiv ℝ H y (hamiltonianField a H y) = hamiltonianRate a H y*H y := by
  have hX := hamiltonian_algebra (a y) (curlLinear (fderiv ℝ a y)) (gradient3 H y)
    (hamiltonianField a H y) (H y) (hQ y)
  have hz : cross (hamiltonianField a H y) (hamiltonianField a H y) = 0 := by
    ext i
    fin_cases i <;> simp [cross] <;> ring
  have he := hX.2
  change dot (gradient3 H y) (hamiltonianField a H y)+
    dot (curlLinear (fderiv ℝ a y)) (cross (hamiltonianField a H y) (hamiltonianField a H y)) = _ at he
  rw [gradient3_pair,hz] at he
  have hvalue : dot (a y) (hamiltonianField a H y) = H y := hX.1
  have hz0 : dot (curlLinear (fderiv ℝ a y)) (0:V) = 0 := by simp [dot]
  rw [hz0,add_zero,hvalue] at he
  exact he

/-- Complete compactly supported contact flow, with a conformal factor and
Hamiltonian transport at EVERY real time, obtained by rescaling unit time. -/
theorem integrate_hamiltonian_all_time (a : V → V) (H : V → ℝ)
    (ha : ContDiff ℝ ∞ a) (hH : ContDiff ℝ ∞ H) (hcH : HasCompactSupport H)
    (hQ : ∀ y, dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    ∃ ψ ρ : ℝ → V → V, ∃ lam : ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => ρ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ y, ψ 0 y = y) ∧ (∀ t, Bijective (ψ t)) ∧
      (∀ t y, ρ t (ψ t y) = y) ∧ (∀ t y, ψ t (ρ t y) = y) ∧
      (∀ t y, HasDerivAt (fun s => ψ s y) (hamiltonianField a H (ψ t y)) t) ∧
      (∀ t y, 0 < lam t y) ∧
      (∀ t y v, covector (a (ψ t y)) (fderiv ℝ (ψ t) y v) = lam t y*covector (a y) v) ∧
      ∀ t y, H (ψ t y) = lam t y*H y := by
  let X : ℝ → V → V := fun _ y => hamiltonianField a H y
  have hXs := hamiltonianField_contDiff a H ha hH hQ
  have hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2) := hXs.comp contDiff_snd
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ t y, y ∉ C → X t y = 0 := by
    refine ⟨tsupport (hamiltonianField a H),hamiltonianField_compact a H hcH,?_⟩
    intro t y hy
    exact image_eq_zero_of_notMem_tsupport hy
  obtain ⟨ψ,hψ,h0,hbij,hflow⟩ := exists_ambient_flow X hX hsupp
  obtain ⟨ρ,hρ,hρψ,hψρ⟩ := smooth_joint_flow_inverse X ψ hX hψ h0 hbij hflow
  let α : OneForm 3 := fun y => covector (a y)
  let μ := hamiltonianRate a H
  have hμ : ContDiff ℝ ∞ μ := hamiltonianRate_contDiff a H ha hH hQ
  let q : ℝ → (ℝ × V) → ℝ := fun s p => p.1*μ (ψ (s*p.1) p.2)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => (p.1*p.2.1,p.2.2)) := by fun_prop
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => q p.1 p.2) :=
    (contDiff_fst.comp contDiff_snd).mul (hμ.comp (hψ.comp harg))
  obtain ⟨Λ,hΛ,hΛ0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  let lam : ℝ → V → ℝ := fun t y => Λ 1 (t,y)
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) :=
    hΛ.comp (contDiff_const.prodMk contDiff_id)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp ha
  have hη : IsSmoothFamily (fun _ => α) := hα.comp contDiff_snd
  have hdiff : ∀ t y v, HasDerivAt (fun s => pullback (ψ s) α y v)
      (μ (ψ t y)*pullback (ψ t) α y v) t := by
    intro t y v
    have hd := GrayStability.pullback_family_hasDerivAt (fun _ => α) hη X hX ψ hψ h0 hbij hflow t y v
    simp only [formTimeDeriv,deriv_const,zero_add] at hd
    have hl := hamiltonianField_lie a H ha hH hQ (ψ t y) (fderiv ℝ (ψ t) y v)
    change lieDerivOneForm (X t) α (ψ t y) (fderiv ℝ (ψ t) y v) = _ at hl
    rw [hl] at hd
    exact hd
  have hHdiff : ∀ t y, HasDerivAt (fun s => H (ψ s y)) (μ (ψ t y)*H (ψ t y)) t := by
    intro t y
    have hd := (hH.differentiable (by simp) (ψ t y)).hasFDerivAt.comp_hasDerivAt t (hflow t y)
    rw [hamiltonian_derivative a H hQ] at hd
    exact hd
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hbij,hρψ,hψρ,hflow,fun t y => hpos 1 (t,y),?_,?_⟩
  · intro T y v
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => pullback (ψ (r*T)) α y v)
          (q s (T,y)*pullback (ψ (s*T)) α y v) s := by
      intro s hs
      have hd := (hdiff (s*T) y v).comp s ((hasDerivAt_id s).mul_const T)
      convert! hd using 1 <;> dsimp [q] <;> ring
    have hh := htransport (T,y) (fun s => pullback (ψ (s*T)) α y v) hf 1 (by simp)
    have hid : ψ 0 = id := funext h0
    simpa [lam,pullback,hid] using hh
  · intro T y
    have hf : ∀ s ∈ Icc (0:ℝ) 1,
        HasDerivAt (fun r => H (ψ (r*T) y)) (q s (T,y)*H (ψ (s*T) y)) s := by
      intro s hs
      have hd := (hHdiff (s*T) y).comp s ((hasDerivAt_id s).mul_const T)
      convert! hd using 1 <;> dsimp [q] <;> ring
    have hh := htransport (T,y) (fun s => H (ψ (s*T) y)) hf 1 (by simp)
    simpa [lam,h0] using hh

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def center : V →L[ℝ] V := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ),ContinuousLinearMap.proj 1,0]
@[simp] lemma center_apply (y : V) : center y = ![y 0,y 1,0] := by ext i; fin_cases i <;> simp [center]
@[simp] lemma xyMap_center (y : V) : xyMap (center y) = xyMap y := by ext i; fin_cases i <;> simp [center]
@[simp] lemma center_two (y : V) : center y 2 = 0 := by simp [center]


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

def surfaceDisk : Set V := {y | diskSq (xyMap y) ≤ 1 ∧ y 2=0}

lemma surfaceDisk_compact : IsCompact surfaceDisk := by
  have hc : IsClosed surfaceDisk :=
    (isClosed_le (diskSq_contDiff.continuous.comp xyMap.continuous) continuous_const).inter
      (isClosed_eq (continuous_apply 2) continuous_const)
  apply isCompact_Icc.of_isClosed_subset hc (s := Icc (![-1,-1,-1]:V) ![1,1,1])
  intro y hy
  have hs : y 0^2+y 1^2 ≤ 1 := hy.1
  constructor <;> intro i <;> fin_cases i
  · dsimp; nlinarith [sq_nonneg (y 1)]
  · dsimp; nlinarith [sq_nonneg (y 0)]
  · simpa [hy.2]
  · dsimp; nlinarith [sq_nonneg (y 1)]
  · dsimp; nlinarith [sq_nonneg (y 0)]
  · simpa [hy.2]


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma exists_ambient_flow_fin {n : ℕ} (X : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => X p.1 p.2))
    (hsupp : ∃ K : Set (Fin n → ℝ), IsCompact K ∧ ∀ t y, y ∉ K → X t y=0) :
    ∃ ψ : ℝ → (Fin n → ℝ) → (Fin n → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℝ) => ψ p.1 p.2) ∧
      (∀ y, ψ 0 y=y) ∧ (∀ t, Bijective (ψ t)) ∧
      ∀ t y, HasDerivAt (fun s => ψ s y) (X t (ψ t y)) t := by
  let F : (Fin n → ℝ) → (Fin 1 → ℝ) := fun _ _ => 1
  have hempty : levelSet F=∅ := by
    ext y
    simp only [levelSet,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro h
    have hh := congrFun h 0
    norm_num [F] at hh
  have hF : IsCompactRegularLevel F := by
    refine ⟨contDiff_const,?_,?_⟩
    · rw [hempty]; exact isCompact_empty
    · intro y hy; rw [hempty] at hy; exact hy.elim
  obtain ⟨ψ,hψ,h0,hbij,hd,_⟩ :=
    FlowCalculus.compact_supported_flow_preserves_regular_level F hF X hX hsupp (by
      intro t ht y hy; rw [hempty] at hy; exact hy.elim)
  exact ⟨ψ,hψ,h0,hbij,hd⟩

lemma exists_ambient_flow_pair (Z : (ℝ × V) → (ℝ × V)) (hZ : ContDiff ℝ ∞ Z)
    (hcZ : HasCompactSupport Z) :
    ∃ Φ : ℝ → (ℝ × V) → (ℝ × V),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => Φ p.1 p.2) ∧
      (∀ y, Φ 0 y=y) ∧ (∀ t, Bijective (Φ t)) ∧
      ∀ t y, HasDerivAt (fun s => Φ s y) (Z (Φ t y)) t := by
  let E : (ℝ × V) ≃L[ℝ] (Fin 4 → ℝ) := Fin.consEquivL ℝ (fun _ : Fin 4 => ℝ)
  let T : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun y => E (Z (E.symm y))
  have hT : ContDiff ℝ ∞ T := E.contDiff.comp (hZ.comp E.symm.contDiff)
  have hC : IsCompact (E '' tsupport Z) := hcZ.image E.continuous
  have hs : ∀ (t : ℝ) (y : Fin 4 → ℝ), y ∉ E '' tsupport Z → T y=0 := by
    intro t y hy
    have hz : E.symm y ∉ tsupport Z := by
      intro hh
      exact hy ⟨E.symm y,hh,E.apply_symm_apply y⟩
    simp [T,image_eq_zero_of_notMem_tsupport hz]
  obtain ⟨Ψ,hΨ,h0,hbij,hd⟩ := exists_ambient_flow_fin (fun _ => T)
    (hT.comp contDiff_snd) ⟨E '' tsupport Z,hC,hs⟩
  let Φ : ℝ → (ℝ × V) → (ℝ × V) := fun t y => E.symm (Ψ t (E y))
  refine ⟨Φ,E.symm.contDiff.comp (hΨ.comp (contDiff_fst.prodMk (E.contDiff.comp contDiff_snd))),
    fun y => by simp [Φ,h0],fun t => E.symm.bijective.comp ((hbij t).comp E.bijective),?_⟩
  intro t y
  have hh := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hd t (E y))
  convert! hh using 1 <;> simp [Φ,T]

theorem exists_smooth_frozen_flows (X : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hsupp : ∃ C : Set V, IsCompact C ∧ ∀ s y, y ∉ C → X s y=0) :
    ∃ ψ ρ : ℝ → ℝ → V → V,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ψ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ρ p.1 p.2.1 p.2.2) ∧
      (∀ s y, ψ s 0 y=y) ∧
      (∀ s t y, ρ s t (ψ s t y)=y) ∧ (∀ s t y, ψ s t (ρ s t y)=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ t y,
        HasDerivAt (fun r => ψ s r y) (X s (ψ s t y)) t := by
  obtain ⟨C,hC,hc⟩ := hsupp
  let Z : (ℝ × V) → (ℝ × V) := fun p => (0,cutoffBase p.1 • X p.1 p.2)
  have hZ : ContDiff ℝ ∞ Z := contDiff_const.prodMk ((cutoffBase_contDiff.comp contDiff_fst).smul hX)
  have hCZ : HasCompactSupport Z := by
    apply HasCompactSupport.intro (isCompact_Icc.prod hC)
    intro p hp
    by_cases hpar : p.1 ∈ Icc (-2:ℝ) 2
    · have hy : p.2 ∉ C := fun hh => hp ⟨hpar,hh⟩
      simp [Z,hc p.1 p.2 hy]
    · have hlarge : 2 ≤ |p.1| := by
        simp only [mem_Icc,not_and_or,not_le] at hpar
        rcases hpar with hh|hh
        · rw [abs_of_neg (by linarith)]; linarith
        · exact le_trans (le_of_lt hh) (le_abs_self _)
      simp [Z,cutoffBase_zero p.1 hlarge]
  obtain ⟨Φ,hΦ,h0,hbij,hd⟩ := exists_ambient_flow_pair Z hZ hCZ
  obtain ⟨R,hR,hRΦ,hΦR⟩ := smooth_joint_flow_inverse (fun _ => Z) Φ (hZ.comp contDiff_snd) hΦ h0 hbij hd
  have hfirst (t : ℝ) (p : ℝ × V) : (Φ t p).1=p.1 := by
    have hh (r : ℝ) : HasDerivAt (fun q => (Φ q p).1) 0 r := by
      have hd' := (ContinuousLinearMap.fst ℝ ℝ V).hasFDerivAt.comp_hasDerivAt r (hd r p)
      convert! hd' using 1 <;> simp [Z]
    have heq := is_const_of_deriv_eq_zero (fun r => (hh r).differentiableAt)
      (fun r => (hh r).deriv) t 0
    simpa only [h0] using heq
  have hRfirst (t : ℝ) (p : ℝ × V) : (R t p).1=p.1 := by
    have hh := hfirst t (R t p)
    rw [hΦR t p] at hh
    exact hh.symm
  let ψ : ℝ → ℝ → V → V := fun s t y => (Φ t (s,y)).2
  let ρ : ℝ → ℝ → V → V := fun s t y => (R t (s,y)).2
  have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => (p.2.1,(p.1,p.2.2))) := by fun_prop
  refine ⟨ψ,ρ,(hΦ.comp harg).snd,(hR.comp harg).snd,fun s y => by simp [ψ,h0],?_,?_,?_⟩
  · intro s t y
    have hh := congrArg Prod.snd (hRΦ t (s,y))
    change (R t (s,(Φ t (s,y)).2)).2=y
    have hp : (s,(Φ t (s,y)).2)=Φ t (s,y) := by
      exact Prod.ext (hfirst t (s,y)).symm rfl
    rw [hp]
    exact hh
  · intro s t y
    have hh := congrArg Prod.snd (hΦR t (s,y))
    change (Φ t (s,(R t (s,y)).2)).2=y
    have hp : (s,(R t (s,y)).2)=R t (s,y) := by
      exact Prod.ext (hRfirst t (s,y)).symm rfl
    rw [hp]
    exact hh
  · intro s hs t y
    have hh := (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt t (hd t (s,y))
    have hk : cutoffBase s=1 := cutoffBase_one s (by rw [abs_of_nonneg hs.1]; exact hs.2)
    convert! hh using 1 <;> simp only [Z,hfirst t (s,y),hk,one_smul] <;> rfl

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem integrate_contact_field_family (α : V → V →L[ℝ] ℝ) (hα : ContDiff ℝ ∞ α)
    (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (hsupp : ∃ C : Set V, IsCompact C ∧ ∀ s y, y ∉ C → X s y=0)
    (hLie : ∀ s y v, lieDerivOneForm (X s) α y v=μ s y*α y v) :
    ∃ ψ ρ : ℝ → ℝ → V → V, ∃ lam : ℝ → ℝ → V → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ψ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => ρ p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => lam p.1 p.2.1 p.2.2) ∧
      (∀ s y, ψ s 0 y=y) ∧
      (∀ s t y, ρ s t (ψ s t y)=y) ∧ (∀ s t y, ψ s t (ρ s t y)=y) ∧
      (∀ s t y, 0 < lam s t y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ t y, HasDerivAt (fun r => ψ s r y) (X s (ψ s t y)) t) ∧
        (∀ t y v, α (ψ s t y) (fderiv ℝ (ψ s t) y v)=lam s t y*α y v) ∧
        ∀ t y, α (ψ s t y) (X s (ψ s t y))=lam s t y*α y (X s y) := by
  obtain ⟨ψ,ρ,hψ,hρ,h0,hρψ,hψρ,hd⟩ := exists_smooth_frozen_flows X hX hsupp
  let q : ℝ → (ℝ × (ℝ × V)) → ℝ := fun r p => p.2.1*μ p.1 (ψ p.1 (r*p.2.1) p.2.2)
  have hq : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => q p.1 p.2) := by
    have harg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) =>
        (p.2.1,(p.1*p.2.2.1,p.2.2.2))) := by fun_prop
    have hsarg : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => p.2.1) := by fun_prop
    exact (by fun_prop : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × (ℝ × V)) => p.2.2.1)).mul
      (hμ.comp (hsarg.prodMk (hψ.comp harg)))
  obtain ⟨Λ,hΛ,hΛ0,hpos,htransport⟩ := ParameterizedCalculus.smooth_scalar_linear_transport q hq
  let lam : ℝ → ℝ → V → ℝ := fun s t y => Λ 1 (s,(t,y))
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × V) => lam p.1 p.2.1 p.2.2) :=
    hΛ.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨ψ,ρ,lam,hψ,hρ,hlam,h0,hρψ,hψρ,fun s t y => hpos _ _,?_⟩
  intro s hs
  have hψs : ContDiff ℝ ∞ (fun p : ℝ × V => ψ s p.1 p.2) :=
    hψ.comp (f := fun p : ℝ × V => (s,p)) (contDiff_const.prodMk contDiff_id)
  have hXs : ContDiff ℝ ∞ (X s) := hX.comp (f := fun y : V => (s,y)) (contDiff_const.prodMk contDiff_id)
  have hXf : ContDiff ℝ ∞ (fun p : ℝ × V => X s p.2) := hXs.comp contDiff_snd
  have hbij (t : ℝ) : Bijective (ψ s t) :=
    ⟨(Function.LeftInverse.injective (hρψ s t)),Function.RightInverse.surjective (hψρ s t)⟩
  have hpbd (t : ℝ) (y v : V) : HasDerivAt (fun r => pullback (ψ s r) α y v)
      (μ s (ψ s t y)*pullback (ψ s t) α y v) t := by
    have hh := GrayStability.pullback_family_hasDerivAt (fun _ => α) (hα.comp contDiff_snd)
      (fun _ => X s) hXf (ψ s) hψs (h0 s) hbij (hd s hs) t y v
    simp only [formTimeDeriv,deriv_const,zero_add] at hh
    rw [hLie] at hh
    exact hh
  let H : V → ℝ := fun y => α y (X s y)
  have hH : ContDiff ℝ ∞ H := hα.clm_apply hXs
  have hHd (t : ℝ) (y : V) : HasDerivAt (fun r => H (ψ s r y))
      (μ s (ψ s t y)*H (ψ s t y)) t := by
    have hh := ((hα.differentiable (by simp) _).hasFDerivAt.clm_apply
      (hXs.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t (hd s hs t y)
    have hl := hLie s (ψ s t y) (X s (ψ s t y))
    change fderiv ℝ α (ψ s t y) (X s (ψ s t y)) (X s (ψ s t y))+
      α (ψ s t y) (fderiv ℝ (X s) (ψ s t y) (X s (ψ s t y)))=_ at hl
    convert! hh using 1
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.flip_apply,ContinuousLinearMap.comp_apply]
    dsimp only [H]
    linarith
  refine ⟨hd s hs,?_,?_⟩
  · intro T y v
    have hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt
        (fun a => pullback (ψ s (a*T)) α y v) (q r (s,(T,y))*pullback (ψ s (r*T)) α y v) r := by
      intro r hr
      have hh := (hpbd (r*T) y v).comp r ((hasDerivAt_id r).mul_const T)
      convert! hh using 1 <;> dsimp only [q] <;> ring
    have hh := htransport (s,(T,y)) (fun r => pullback (ψ s (r*T)) α y v) hf 1 (by simp)
    have hid : ψ s 0=id := funext (h0 s)
    simpa [lam,pullback,hid] using hh
  · intro T y
    have hf : ∀ r ∈ Icc (0:ℝ) 1, HasDerivAt
        (fun a => H (ψ s (a*T) y)) (q r (s,(T,y))*H (ψ s (r*T) y)) r := by
      intro r hr
      have hh := (hHd (r*T) y).comp r ((hasDerivAt_id r).mul_const T)
      convert! hh using 1 <;> dsimp only [q] <;> ring
    have hh := htransport (s,(T,y)) (fun r => H (ψ s (r*T) y)) hf 1 (by simp)
    simpa only [H,lam,one_mul,zero_mul,h0] using hh

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

lemma smooth_injective_derivative_local_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (p : E) (hinj : Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ p ∈ e.source := by
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F p).toLinearMap
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt F (A : E →L[ℝ] E) p := (hF.differentiable (by simp) p).hasFDerivAt
  exact ⟨hF.contDiffAt.toOpenPartialHomeomorph F hd (by simp),
    hF.contDiffAt.toOpenPartialHomeomorph_coe hd (by simp),
    hF.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)⟩

/-- Local invertibility and injectivity on a compact set give one genuine smooth
chart around the entire compact set, inside any prescribed good open domain. -/
theorem compact_smooth_embedding_chart_general (F : E → E) (hF : ContDiff ℝ ∞ F)
    (S W : Set E) (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W)
    (hinj : InjOn F S) (hder : ∀ p ∈ W, Injective (fderiv ℝ F p)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = F ∧ S ⊆ e.source ∧
      e.source ⊆ W ∧ ∀ y ∈ e.target, ContDiffAt ℝ ∞ e.symm y := by
  have hloc : ∀ p ∈ S, ∃ O ∈ 𝓝 p, InjOn F O := by
    intro p hp
    obtain ⟨e,he,hp⟩ := smooth_injective_derivative_local_chart_general F hF p (hder p (hSW hp))
    exact ⟨e.source,e.open_source.mem_nhds hp,he ▸ e.injOn⟩
  obtain ⟨O,hO,hSO,hOi⟩ := hinj.exists_isOpen_superset hS (fun _ _ => hF.continuous.continuousAt) hloc
  let U := O ∩ W
  have hU : IsOpen U := hO.inter hW
  have hUi : InjOn F U := hOi.mono inter_subset_left
  have hopen : IsOpenMap (U.domRestrict F) := by
    apply IsOpenMap.of_nhds_le
    intro x
    obtain ⟨e,he,hx⟩ := smooth_injective_derivative_local_chart_general F hF x (hder x x.property.2)
    have hm : map F (𝓝 x.val) = 𝓝 (F x.val) := by
      simpa only [he] using e.map_nhds_eq hx
    have hs : map (fun x : U => (x : E)) (𝓝 x) = 𝓝 (x : E) :=
      hU.isOpenEmbedding_subtypeVal.map_nhds_eq x
    change 𝓝 (F x.val) ≤ map (fun z : U => F z.val) (𝓝 x)
    rw [show (fun z : U => F z.val) = F ∘ Subtype.val from rfl,← map_map,hs,hm]
  let e : OpenPartialHomeomorph E E := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hUi.toPartialEquiv F U) hF.continuous.continuousOn hopen hU
  have he : (e : E → E) = F := rfl
  refine ⟨e,he,fun x hx => ⟨hSO hx,hSW hx⟩,inter_subset_right,?_⟩
  intro y hy
  have hp : e.symm y ∈ W := (e.map_target hy).2
  let A : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ F (e.symm y)).toLinearMap
    ⟨hder _ hp,LinearMap.injective_iff_surjective.mp (hder _ hp)⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt e (A : E →L[ℝ] E) (e.symm y) := (hF.differentiable (by simp) _).hasFDerivAt
  exact e.contDiffAt_symm hy hd hF.contDiffAt

end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma autonomous_flow_add (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t s y, ψ (t+s) y = ψ t (ψ s y) := by
  have hX' : ContDiff ℝ ∞ (fun p : ℝ × V => X p.2) := hX.comp contDiff_snd
  have hsupp : ∃ C : Set V, IsCompact C ∧ ∀ (t : ℝ) y, y ∉ C → X y = 0 :=
    ⟨tsupport X,hcX,fun _ _ hy => image_eq_zero_of_notMem_tsupport hy⟩
  intro t s y
  have hshift : (fun r => ψ (r+s) y) 0 = ψ s y ∧
      ∀ r, HasDerivAt (fun v => ψ (v+s) y) (X (ψ (r+s) y)) r := by
    refine ⟨by simp,?_⟩
    intro r
    have harg : HasDerivAt (fun v : ℝ => v+s) (1:ℝ) r := by
      convert! (hasDerivAt_id (𝕜 := ℝ) r).add_const s using 1
    convert! (hd (r+s) y).scomp r harg using 1 <;> simp
  have he : (fun r => ψ (r+s) y) = fun r => ψ r (ψ s y) :=
    (FlowCalculus.exists_unique_global_trajectory_of_compact_support (fun _ z => X z) hX' hsupp 0 (ψ s y)).unique
      hshift ⟨h0 _,fun r => hd r _⟩
  exact congrFun he t

lemma autonomous_flow_neg (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t y, ψ (-t) (ψ t y) = y := by
  intro t y
  simpa [h0] using (autonomous_flow_add X hX hcX ψ h0 hd (-t) t y).symm


def flowCollar (ψ : ℝ → V → V) (y : V) : V := ψ (y 2) (center y)

lemma flowCollar_contDiff (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2)) :
    ContDiff ℝ ∞ (flowCollar ψ) := hψ.comp ((contDiff_apply ℝ ℝ 2).prodMk center.contDiff)

lemma autonomous_flow_transports_field (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y) (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) :
    ∀ t y, fderiv ℝ (ψ t) y (X y) = X (ψ t y) := by
  intro t y
  have hs : ContDiff ℝ ∞ (ψ t) := hψ.comp (contDiff_const.prodMk contDiff_id :
    ContDiff ℝ ∞ (fun z : V => (t,z)))
  have harg : HasDerivAt (fun s : ℝ => t+s) (1:ℝ) 0 := by
    convert! (hasDerivAt_id (𝕜 := ℝ) 0).const_add t using 1
  have hleft := (hd (t+0) y).scomp 0 harg
  have hright := (hs.differentiable (by simp) (ψ 0 y)).hasFDerivAt.comp_hasDerivAt 0 (hd 0 y)
  have he : (fun s => ψ (t+s) y) = fun s => ψ t (ψ s y) :=
    funext fun s => autonomous_flow_add X hX hcX ψ h0 hd t s y
  change HasDerivAt (fun s => ψ (t+s) y) _ 0 at hleft
  rw [he] at hleft
  have hh := hleft.unique hright
  simpa [h0] using hh.symm

lemma flowCollar_fderiv (X : V → V) (ψ : ℝ → V → V)
    (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t) (y v : V) :
    fderiv ℝ (flowCollar ψ) y v =
      v 2 • X (flowCollar ψ y)+fderiv ℝ (ψ (y 2)) (center y) (center v) := by
  let t := y 2
  let x := center y
  let D := fderiv ℝ (fun p : ℝ × V => ψ p.1 p.2) (t,x)
  have hJ := (hψ.differentiable (by simp) (t,x)).hasFDerivAt
  have hT := hJ.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have ht : D (1,0) = X (ψ t x) := hT.unique (hd t x)
  have hsp := hJ.comp x ((hasFDerivAt_const (𝕜 := ℝ) t x).prodMk (hasFDerivAt_id (𝕜 := ℝ) x))
  have hspace : ∀ w : V, D (0,w) = fderiv ℝ (ψ t) x w := by
    intro w
    have hh := congrArg (fun L : V →L[ℝ] V => L w) hsp.fderiv
    exact hh.symm
  have hF := hJ.comp y ((ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).hasFDerivAt.prodMk center.hasFDerivAt)
  change HasFDerivAt (flowCollar ψ) _ y at hF
  rw [hF.fderiv]
  change D (v 2,center v) = _
  have hp : (v 2,center v) = v 2 • ((1:ℝ),(0:V))+(0,center v) := by ext <;> simp
  rw [hp,map_add,map_smul,ht,hspace]
  rfl


lemma transverse_flowCollar_derivative
    (X : V → V) (hX : ContDiff ℝ ∞ X) (hcX : HasCompactSupport X)
    (ψ : ℝ → V → V) (hψ : ContDiff ℝ ∞ (fun p : ℝ × V => ψ p.1 p.2))
    (h0 : ∀ y, ψ 0 y = y)
    (hd : ∀ t y, HasDerivAt (fun s => ψ s y) (X (ψ t y)) t)
    (y : V) (hn : X (center y) 2 ≠ 0) :
    Injective (fderiv ℝ (flowCollar ψ) y) := by
  have hinj := FlowCalculus.smooth_flow_spatial_derivative_injective (fun _ z => X z) ψ
    (hX.comp contDiff_snd) hψ h0 hd (y 2) (center y)
  have htrans := autonomous_flow_transports_field X hX hcX ψ hψ h0 hd (y 2) (center y)
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [flowCollar_fderiv X ψ hψ hd] at hv
  have he : fderiv ℝ (ψ (y 2)) (center y) (center v+v 2 • X (center y)) = 0 := by
    rw [map_add,map_smul,htrans]
    simpa only [flowCollar,add_comm] using hv
  have hk : center v+v 2 • X (center y) = 0 := hinj (by simpa only [map_zero] using he)
  have hz : v 2 = 0 := by
    have hh := congrFun hk 2
    change center v 2+v 2*X (center y) 2 = 0 at hh
    simp only [center_two,zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_right hn
  simp only [hz,zero_smul,add_zero] at hk
  ext i
  fin_cases i
  · simpa using congrFun hk 0
  · simpa using congrFun hk 1
  · exact hz


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma parameter_lift_derivative_injective (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2))
    (s : ℝ) (y : V) (hi : Injective (fderiv ℝ (f s) y)) :
    Injective (fderiv ℝ (fun p : ℝ × V => (p.1,f p.1 p.2)) (s,y)) := by
  let J : (ℝ × V) → V := fun p => f p.1 p.2
  have hJ := (hf.differentiable (by simp) (s,y)).hasFDerivAt
  have hF := (hasFDerivAt_fst (𝕜 := ℝ) (p := (s,y))).prodMk hJ
  have hsp := hJ.comp y ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  have hspace (v : V) : fderiv ℝ J (s,y) (0,v)=fderiv ℝ (f s) y v := by
    have hh := congrArg (fun D : V →L[ℝ] V => D v) hsp.fderiv
    exact hh.symm
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  rw [hF.fderiv] at hv
  have hfst : v.1=0 := congrArg Prod.fst hv
  have hsnd : fderiv ℝ J (s,y) v=0 := congrArg Prod.snd hv
  have hvp : v=(0,v.2) := Prod.ext hfst rfl
  rw [hvp,hspace] at hsnd
  have hv2 : v.2=0 := hi (by simpa only [map_zero] using hsnd)
  exact Prod.ext hfst hv2

theorem exists_contact_collar_family (u : P → ℝ) (β : P → P)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (X : ℝ → V → V) (μ : ℝ → V → ℝ)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (hμ : ContDiff ℝ ∞ (fun p : ℝ × V => μ p.1 p.2))
    (C W : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (hW : IsOpen W) (hDW : surfaceDisk ⊆ W)
    (hLie : ∀ s y v, lieDerivOneForm (X s) (fun z => covector (invariantCoefficients u β z)) y v=
      μ s y*covector (invariantCoefficients u β y) v)
    (hplane : ∀ s y, y ∈ W → y 2=0 → X s y 2=1 ∧
      covector (invariantCoefficients u β y) (X s y)=u (xyMap y)) :
    ∃ f : ℝ → V → V, ∃ lam : ℝ → V → ℝ, ∃ N : Set V,
    ∃ E : OpenPartialHomeomorph (ℝ × V) (ℝ × V),
      ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) ∧
      (∀ s y, 0 < lam s y) ∧ IsOpen N ∧ surfaceDisk ⊆ N ∧
      (∀ y ∈ N, center y ∈ W) ∧
      (E : (ℝ × V) → (ℝ × V))=(fun p => (p.1,f p.1 p.2)) ∧
      Icc (0:ℝ) 1 ×ˢ N ⊆ E.source ∧
      (∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) ∧
      (∀ s y, y 2=0 → f s y=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ y ∈ N, Injective (fderiv ℝ (f s) y)) ∧
        (∀ y ∈ N, ∀ v, covector (invariantCoefficients u β (f s y)) (fderiv ℝ (f s) y v)=
          lam s y*covector (invariantCoefficients u β y) v) ∧
        ∀ y, y 2=0 → ∀ (t : ℝ), HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V)))
          (X s (f s (y+t • (Pi.single 2 1 : V)))) t := by
  let α : V → V →L[ℝ] ℝ := fun y => covector (invariantCoefficients u β y)
  have hα : ContDiff ℝ ∞ α := covector.contDiff.comp (invariantCoefficients_contDiff u β hu hβ)
  obtain ⟨ψ,ρ,Λ,hψ,hρ,hΛ,h0,hρψ,hψρ,hpos,hdata⟩ :=
    integrate_contact_field_family α hα X μ hX hμ ⟨C,hC,hc⟩ hLie
  let f : ℝ → V → V := fun s => flowCollar (ψ s)
  let lam : ℝ → V → ℝ := fun s y => Λ s (y 2) (center y)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × V => (p.1,(p.2 2,center p.2))) := by fun_prop
  have hf : ContDiff ℝ ∞ (fun p : ℝ × V => f p.1 p.2) := hψ.comp harg
  have hlam : ContDiff ℝ ∞ (fun p : ℝ × V => lam p.1 p.2) := hΛ.comp harg
  have hfix (s : ℝ) (y : V) (hy : y 2=0) : f s y=y := by
    simp only [f,flowCollar,hy,h0,center_apply]
    ext i
    fin_cases i <;> simp [hy]
  have hfs (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × V => ψ s p.1 p.2) :=
    hψ.comp (f := fun p : ℝ × V => (s,p)) (contDiff_const.prodMk contDiff_id)
  have hder (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (y : V) (hy : center y ∈ W) :
      Injective (fderiv ℝ (f s) y) := by
    have hXs : ContDiff ℝ ∞ (X s) := hX.comp (f := fun z : V => (s,z)) (contDiff_const.prodMk contDiff_id)
    have hcX : HasCompactSupport (X s) := HasCompactSupport.intro hC (hc s)
    exact transverse_flowCollar_derivative (X s) hXs hcX (ψ s) (hfs s) (h0 s) (hdata s hs).1 y
      (by rw [(hplane s (center y) hy (center_two y)).1]; norm_num)
  let F : (ℝ × V) → (ℝ × V) := fun p => (p.1,f p.1 p.2)
  have hF : ContDiff ℝ ∞ F := contDiff_fst.prodMk hf
  let S : Set (ℝ × V) := Icc (0:ℝ) 1 ×ˢ surfaceDisk
  have hS : IsCompact S := isCompact_Icc.prod surfaceDisk_compact
  have hcent (y : V) (hy : y ∈ surfaceDisk) : center y=y := by
    rw [center_apply]
    ext i
    fin_cases i <;> simp [hy.2]
  have hFS : ∀ p ∈ S, F p=p := by
    intro p hp
    exact Prod.ext rfl (hfix _ _ hp.2.2)
  have hiS : InjOn F S := by
    intro p hp q hq heq
    simpa only [hFS p hp,hFS q hq] using heq
  let U : Set (ℝ × V) := {p | IsUnit (fderiv ℝ F p)}
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (by simp)
  have hU : IsOpen U := Units.isOpen.preimage hDF.continuous
  have hSU : S ⊆ U := by
    intro p hp
    have hh := parameter_lift_derivative_injective f hf p.1 p.2
      (hder p.1 hp.1 p.2 (by rw [hcent p.2 hp.2]; exact hDW hp.2))
    exact ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hh,LinearMap.injective_iff_surjective.mp hh⟩
  obtain ⟨E,hE,hSE,hEU,hR⟩ := compact_smooth_embedding_chart_general F hF S U hS hU hSU hiS
    (fun p hp => (ContinuousLinearMap.isUnit_iff_bijective.mp hp).1)
  obtain ⟨A,B,hA,hB,hIA,hDB,hAB⟩ := generalized_tube_lemma isCompact_Icc surfaceDisk_compact E.open_source hSE
  let N := B ∩ center ⁻¹' W
  have hN : IsOpen N := hB.inter (hW.preimage center.continuous)
  have hDN : surfaceDisk ⊆ N := fun y hy => ⟨hDB hy,by change center y ∈ W; rw [hcent y hy]; exact hDW hy⟩
  refine ⟨f,lam,N,E,hf,hlam,fun s y => hpos _ _ _,hN,hDN,fun _ hy => hy.2,hE,?_,hR,hfix,?_⟩
  · intro p hp
    exact hAB ⟨hIA hp.1,hp.2.1⟩
  · intro s hs
    refine ⟨fun y hy => hder s hs y hy.2,?_,?_⟩
    · intro y hy v
      obtain ⟨hd,hpb,hH⟩ := hdata s hs
      rw [flowCollar_fderiv (X s) (ψ s) (hfs s) hd,map_add,map_smul]
      change v 2*α (flowCollar (ψ s) y) (X s (flowCollar (ψ s) y))+
        α (ψ s (y 2) (center y)) (fderiv ℝ (ψ s (y 2)) (center y) (center v))=_
      rw [hpb]
      have hH' := hH (y 2) (center y)
      change α (flowCollar (ψ s) y) (X s (flowCollar (ψ s) y))=_ at hH'
      rw [hH',(hplane s (center y) hy.2 (center_two y)).2]
      simp [α,lam,covector_apply,dot,invariantCoefficients]
      ring
    · intro y hy t
      have heq (r : ℝ) : f s (y+r • (Pi.single 2 1 : V))=ψ s r y := by
        have ht : (y+r • (Pi.single 2 1 : V)) 2=r := by simp [hy]
        have hc' : center (y+r • (Pi.single 2 1 : V))=y := by
          rw [center_apply]
          ext i
          fin_cases i <;> simp [hy]
        simp only [f,flowCollar,ht,hc']
      simpa only [heq] using (hdata s hs).1 t y


end
end ContactTopology.ConvexDeformation

namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma center_add_normal (y : V) : center y+y 2 • (Pi.single 2 1 : V)=y := by
  ext i
  fin_cases i <;> simp [center]

theorem collar_endpoints_near_disk
    (e : OpenPartialHomeomorph V V) (he : ContDiffOn ℝ ∞ (e : V → V) e.source)
    (hD : surfaceDisk ⊆ e.source) (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (X f : ℝ → V → V) (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (C W : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (hW : IsOpen W) (hDW : surfaceDisk ⊆ W)
    (hAgree : ∀ s, ∀ y ∈ W, X s y=(1-s) • (Pi.single 2 1 : V)+
      s • fderiv ℝ (e : V → V) (e.symm y) (Pi.single 2 1))
    (hf : ∀ s y, y 2=0 → f s y=y)
    (hODE : ∀ s ∈ Icc (0:ℝ) 1, ∀ y, y 2=0 → ∀ (t : ℝ),
      HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V))) (X s (f s (y+t • (Pi.single 2 1 : V)))) t) :
    ∃ N : Set V, IsOpen N ∧ surfaceDisk ⊆ N ∧ N ⊆ e.source ∧
      ∀ y ∈ N, f 0 y=y ∧ f 1 y=e y := by
  let T := W ∩ (e.source ∩ e ⁻¹' W)
  have hT : IsOpen T := hW.inter (e.isOpen_inter_preimage hW)
  have hDT : surfaceDisk ⊆ T := by
    intro y hy
    refine ⟨hDW hy,hD hy,?_⟩
    change e y ∈ W
    rw [hfix y (hD hy) hy.2]
    exact hDW hy
  let J : (V × ℝ) → V := fun p => center p.1+p.2 • (Pi.single 2 1 : V)
  have hJ : Continuous J := (center.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hDT0 : surfaceDisk ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' T := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    change y ∈ surfaceDisk at hy
    have hy0 : y 2=0 := hy.2
    have ht0 : t=0 := ht
    have hc' : center y=y := by
      ext i
      fin_cases i <;> simp [center,hy0]
    change center y+t • (Pi.single 2 1 : V) ∈ T
    rw [ht0,zero_smul,add_zero,hc']
    exact hDT hy
  obtain ⟨A,B,hA,hB,hDA,h0B,hAB⟩ := generalized_tube_lemma surfaceDisk_compact isCompact_singleton
    (hT.preimage hJ) hDT0
  have hzB : (0:ℝ) ∈ B := h0B (by simp)
  obtain ⟨δ,hδ,hδB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hzB)
  let N : Set V := {y | center y ∈ A ∧ |y 2| < δ}
  have hN : IsOpen N := (hA.preimage center.continuous).inter
    (isOpen_lt ((continuous_apply 2).abs) continuous_const)
  have hDN : surfaceDisk ⊆ N := by
    intro y hy
    have hc' : center y=y := by
      ext i
      fin_cases i <;> simp [center,hy.2]
    exact ⟨by rw [hc']; exact hDA hy,by simpa only [hy.2,abs_zero] using hδ⟩
  have hstrip (y : V) (hy : y ∈ N) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      center y+t • (Pi.single 2 1 : V) ∈ T := by
    have htB : t ∈ B := hδB (by simpa [Metric.mem_ball,Real.dist_eq,abs_lt] using ht)
    have hh := hAB (show (center y,t) ∈ A ×ˢ B from ⟨hy.1,htB⟩)
    change center (center y)+t • (Pi.single 2 1 : V) ∈ T at hh
    have hcc : center (center y)=center y := by simp [center_apply]
    simpa only [J,hcc] using hh
  have hNS : N ⊆ e.source := by
    intro y hy
    have ht : y 2 ∈ Ioo (-δ) δ := abs_lt.mp hy.2
    have hh := (hstrip y hy (y 2) ht).2.1
    simpa only [center_add_normal] using hh
  obtain ⟨K,hK⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  have hlin (p : V) (t : ℝ) : HasDerivAt (fun r : ℝ => p+r • (Pi.single 2 1 : V)) (Pi.single 2 1 : V) t := by
    convert! (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (Pi.single 2 1 : V)) using 1 <;> simp
  have hX0 (z : V) (hz : z ∈ W) : X 0 z=Pi.single 2 1 := by simpa using hAgree 0 z hz
  have hX1 (z : V) (hz : z ∈ T) : X 1 (e z)=fderiv ℝ (e : V → V) z (Pi.single 2 1) := by
    have hh := hAgree 1 (e z) hz.2.2
    simpa only [sub_self,zero_smul,one_smul,zero_add,e.left_inv hz.2.1] using hh
  refine ⟨N,hN,hDN,hNS,?_⟩
  intro y hy
  let p := center y
  have hp : p 2=0 := center_two y
  have hzero : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hpt : p ∈ T := by simpa only [zero_smul,add_zero] using hstrip y hy 0 hzero
  have hfg0 : f 0 p=p := hf 0 p hp
  have hfg1 : f 1 p=p := hf 1 p hp
  have hep : e p=p := hfix p hpt.2.1 hp
  have heq0 : EqOn (fun t => f 0 (p+t • (Pi.single 2 1 : V)))
      (fun t => p+t • (Pi.single 2 1 : V)) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X 0) (s := fun _ => Set.univ)
      (fun _ _ => (hK 0 (by simp)).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE 0 (by simp) p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hX0 _ (hstrip y hy t ht).1]
      exact hlin p t
    · simpa only [zero_smul,add_zero] using hfg0
  have heq1 : EqOn (fun t => f 1 (p+t • (Pi.single 2 1 : V)))
      (fun t => e (p+t • (Pi.single 2 1 : V))) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X 1) (s := fun _ => Set.univ)
      (fun _ _ => (hK 1 (by simp)).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE 1 (by simp) p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hX1 _ (hstrip y hy t ht)]
      have hEp := he.contDiffAt (e.open_source.mem_nhds (hstrip y hy t ht).2.1)
      exact (hEp.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t (hlin p t)
    · simpa only [zero_smul,add_zero,hep] using hfg1
  have ht : y 2 ∈ Ioo (-δ) δ := abs_lt.mp hy.2
  exact ⟨by simpa only [p,center_add_normal] using heq0 ht,
    by simpa only [p,center_add_normal] using heq1 ht⟩

end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma inverse_contact_pullback (α : V → V →L[ℝ] ℝ) (F G : V → V)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (hFG : ∀ y, F (G y)=y)
    (L : V → ℝ) (hpos : ∀ y, 0 < L y)
    (hpb : ∀ y v, α (F y) (fderiv ℝ F y v)=L y*α y v) :
    ∀ y v, α (G y) (fderiv ℝ G y v)=(L (G y))⁻¹*α y v := by
  intro y v
  have heq : F ∘ G=id := funext hFG
  have hd := fderiv_comp y (hF.differentiable (by simp) _) (hG.differentiable (by simp) y)
  rw [heq] at hd
  have hv : fderiv ℝ F (G y) (fderiv ℝ G y v)=v := by
    have hh := congrArg (fun D : V →L[ℝ] V => D v) hd
    simpa using hh.symm
  have hp := hpb (G y) (fderiv ℝ G y v)
  rw [hFG,hv] at hp
  have hn := (hpos (G y)).ne'
  apply (eq_inv_mul_iff_mul_eq₀ hn).mpr
  exact hp.symm


end
end ContactTopology.ConvexDeformation


namespace ContactTopology.ConvexDeformation
open Set Function Filter GrayStability Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem collar_stationary_near_compact (X f : ℝ → V → V)
    (hX : ContDiff ℝ ∞ (fun p : ℝ × V => X p.1 p.2))
    (C : Set V) (hC : IsCompact C) (hc : ∀ s y, y ∉ C → X s y=0)
    (B S : Set V) (hB : IsOpen B) (hS : IsCompact S) (hSB : S ⊆ B)
    (hSplane : ∀ y ∈ S, y 2=0)
    (hvertical : ∀ s, ∀ y ∈ B, X s y=Pi.single 2 1)
    (hf : ∀ s y, y 2=0 → f s y=y)
    (hODE : ∀ s ∈ Icc (0:ℝ) 1, ∀ y, y 2=0 → ∀ (t : ℝ),
      HasDerivAt (fun r : ℝ => f s (y+r • (Pi.single 2 1 : V)))
        (X s (f s (y+t • (Pi.single 2 1 : V)))) t) :
    ∃ V0 : Set V, IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ B ∧
      ∀ s ∈ Icc (0:ℝ) 1, ∀ y ∈ V0, f s y=y := by
  let J : (V × ℝ) → V := fun p => center p.1+p.2 • (Pi.single 2 1 : V)
  have hJ : Continuous J := (center.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)
  have hS0 : S ×ˢ ({0}:Set ℝ) ⊆ J ⁻¹' B := by
    rintro ⟨y,t⟩ ⟨hy,ht⟩
    change y ∈ S at hy
    have hy0 := hSplane y hy
    have ht0 : t=0 := ht
    have hcent : center y=y := by ext i; fin_cases i <;> simp [center,hy0]
    change center y+t • (Pi.single 2 1 : V) ∈ B
    rw [ht0,zero_smul,add_zero,hcent]
    exact hSB hy
  obtain ⟨A,T,hA,hT,hSA,h0T,hAT⟩ := generalized_tube_lemma hS isCompact_singleton (hB.preimage hJ) hS0
  have hzT : (0:ℝ) ∈ T := h0T (by simp)
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hzT)
  let V0 : Set V := {y | center y ∈ A ∧ |y 2| < δ}
  have hV0 : IsOpen V0 := (hA.preimage center.continuous).inter
    (isOpen_lt (continuous_apply 2).abs continuous_const)
  have hSV0 : S ⊆ V0 := by
    intro y hy
    have hy0 := hSplane y hy
    have hcent : center y=y := by ext i; fin_cases i <;> simp [center,hy0]
    exact ⟨by rw [hcent]; exact hSA hy,by simpa only [hy0,abs_zero] using hδ⟩
  have hstrip (y : V) (hy : y ∈ V0) (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      center y+t • (Pi.single 2 1 : V) ∈ B := by
    have htT : t ∈ T := hδT (by simpa [Metric.mem_ball,Real.dist_eq,abs_lt] using ht)
    have hh := hAT (show (center y,t) ∈ A ×ˢ T from ⟨hy.1,htT⟩)
    change center (center y)+t • (Pi.single 2 1 : V) ∈ B at hh
    have hcc : center (center y)=center y := by simp [center_apply]
    simpa only [hcc] using hh
  have hV0B : V0 ⊆ B := by
    intro y hy
    have hh := hstrip y hy (y 2) (abs_lt.mp hy.2)
    simpa only [center_add_normal] using hh
  obtain ⟨L,hL⟩ := FlowCalculus.uniform_spatial_lipschitz_of_compact_support X hX ⟨C,hC,hc⟩ 0 1
  refine ⟨V0,hV0,hSV0,hV0B,?_⟩
  intro s hs y hy
  let p := center y
  have hp : p 2=0 := center_two y
  have hzero : (0:ℝ) ∈ Ioo (-δ) δ := by constructor <;> linarith
  have hlin (t : ℝ) : HasDerivAt (fun r : ℝ => p+r • (Pi.single 2 1 : V)) (Pi.single 2 1 : V) t := by
    convert! (hasDerivAt_const t p).add ((hasDerivAt_id t).smul_const (Pi.single 2 1 : V)) using 1 <;> simp
  have heq : EqOn (fun t => f s (p+t • (Pi.single 2 1 : V)))
      (fun t => p+t • (Pi.single 2 1 : V)) (Ioo (-δ) δ) := by
    apply ODE_solution_unique_of_mem_Ioo (v := fun _ => X s) (s := fun _ => Set.univ)
      (fun _ _ => (hL s hs).lipschitzOnWith) hzero
    · intro t ht
      exact ⟨hODE s hs p hp t,mem_univ _⟩
    · intro t ht
      refine ⟨?_,mem_univ _⟩
      rw [hvertical s _ (hstrip y hy t ht)]
      exact hlin t
    · simpa only [zero_smul,add_zero] using hf s p hp
  simpa only [p,center_add_normal] using heq (abs_lt.mp hy.2)

end
end ContactTopology.ConvexDeformation


open Set Filter Topology
open scoped ContDiff

theorem ContactTopology.relative_disk_contact_embedding_family_internal
    (u : (Fin 2 → ℝ) → ℝ) (β : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β)
    (hQ : ∀ x, β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
      u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) ≠ 0)
    (e : OpenPartialHomeomorph (Fin 3 → ℝ) (Fin 3 → ℝ))
    (he : ContDiffOn ℝ ∞ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : (Fin 3 → ℝ) → (Fin 3 → ℝ)) e.target)
    (hD : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ e.source)
    (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : (Fin 3 → ℝ) → ℝ) (hL : ContDiffOn ℝ ∞ L e.source)
    (hpositive : ∀ y ∈ e.source, 0 < L y)
    (S Brel : Set (Fin 3 → ℝ)) (hS : IsCompact S)
    (hSD : S ⊆ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0})
    (hBrel : IsOpen Brel) (hSB : S ⊆ Brel) (hBe : Brel ⊆ e.source)
    (hBfix : ∀ y ∈ Brel, e y=y)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ U) :
    let A : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    (∀ y ∈ e.source, ∀ v, B (A (e y)) (fderiv ℝ (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) y v)=L y*B (A y) v) →
    ∃ f : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ), ∃ lam : ℝ → (Fin 3 → ℝ) → ℝ,
    ∃ N : Set (Fin 3 → ℝ),
    ∃ E : OpenPartialHomeomorph (ℝ × (Fin 3 → ℝ)) (ℝ × (Fin 3 → ℝ)), ∃ V0 : Set (Fin 3 → ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => f p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2) ∧
      (∀ s y, 0 < lam s y) ∧ IsOpen N ∧
      {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ N ∧ N ⊆ e.source ∧
      (E : (ℝ × (Fin 3 → ℝ)) → (ℝ × (Fin 3 → ℝ)))=(fun p => (p.1,f p.1 p.2)) ∧
      Icc (0:ℝ) 1 ×ˢ N ⊆ E.source ∧
      (∀ p ∈ E.target, ContDiffAt ℝ ∞ E.symm p) ∧
      (∀ s y, y 2=0 → f s y=y) ∧
      (∀ y ∈ N, f 0 y=y ∧ f 1 y=e y) ∧
      IsOpen V0 ∧ S ⊆ V0 ∧ V0 ⊆ N ∧ (∀ s ∈ Icc (0:ℝ) 1, ∀ y ∈ V0, f s y=y) ∧
      ∀ s ∈ Icc (0:ℝ) 1,
        (∀ y ∈ N, f s y ∈ U) ∧
        (∀ y ∈ N, Function.Injective (fderiv ℝ (f s) y)) ∧
        (∀ y ∈ N, ∀ z ∈ N, f s y=f s z → y=z) ∧
        ∀ y ∈ N, ∀ v, B (A (f s y)) (fderiv ℝ (f s) y v)=lam s y*B (A y) v := by


  dsimp only
  intro hpb
  obtain ⟨X,μ,C,W,hX,hμ,hC,hc,hW,hDW,hWE,hLie,hAgree,hplane⟩ :=
    ContactTopology.local_fixed_surface_contact_field_homotopy u β hu hβ hQ e he hG hD hfix L hL hpositive hpb
  let a := ContactTopology.ConvexDeformation.invariantCoefficients u β
  have ha := ContactTopology.ConvexDeformation.invariantCoefficients_contDiff u β hu hβ
  have hcoef : a = (fun y : Fin 3 → ℝ => ![β ![y 0,y 1] 0,β ![y 0,y 1] 1,u ![y 0,y 1]]) := by
    funext y
    simp only [a,ContactTopology.ConvexDeformation.invariantCoefficients,
      ContactTopology.ConvexDeformation.xyMap_apply]
  have hLie' : ∀ s y v, GrayStability.lieDerivOneForm (X s)
      (fun z => ContactTopology.ConvexDeformation.covector (a z)) y v=
      μ s y*ContactTopology.ConvexDeformation.covector (a y) v := by
    intro s y v
    have hd := ContactTopology.ConvexDeformation.covector.hasFDerivAt.comp y (ha.differentiable (by simp) y).hasFDerivAt
    change HasFDerivAt (fun z => ContactTopology.ConvexDeformation.covector (a z)) _ y at hd
    unfold GrayStability.lieDerivOneForm
    rw [hd.fderiv]
    change ContactTopology.ConvexDeformation.covector (fderiv ℝ a y (X s y)) v+
      ContactTopology.ConvexDeformation.covector (a y) (fderiv ℝ (X s) y v)=
      μ s y*ContactTopology.ConvexDeformation.covector (a y) v
    rw [hcoef]
    simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hLie s y v
  have hplane' : ∀ s y, y ∈ W → y 2=0 → X s y 2=1 ∧
      ContactTopology.ConvexDeformation.covector (a y) (X s y)=u (ContactTopology.ConvexDeformation.xyMap y) := by
    intro s y hy hy0
    simpa only [hcoef,ContactTopology.ConvexDeformation.xyMap_apply,
      ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot] using hplane s y hy hy0
  obtain ⟨f,lam,N0,E,hf,hlam,hpos,hN0,hDN0,hcenter,hE,hEN0,hR,hfplane,hdata⟩ :=
    ContactTopology.ConvexDeformation.exists_contact_collar_family u β hu hβ X μ hX hμ C W hC hc hW hDW hLie' hplane'
  have hvertical : ∀ s, ∀ z ∈ Brel ∩ W, X s z=Pi.single 2 1 := by
    intro s z hz
    have hEz : e z=z := hBfix z hz.1
    have hGz : e.symm z=z := by
      have hh := e.left_inv (hBe hz.1)
      simpa only [hEz] using hh
    have hgerm : (e : (Fin 3 → ℝ) → (Fin 3 → ℝ)) =ᶠ[𝓝 z] id := by
      filter_upwards [hBrel.mem_nhds hz.1] with q hq
      exact hBfix q hq
    rw [hAgree s z hz.2,hGz,hgerm.fderiv_eq]
    ext i
    fin_cases i <;> simp <;> ring
  obtain ⟨V2,hV2,hSV2,hV2BW,hV2fix⟩ := ContactTopology.ConvexDeformation.collar_stationary_near_compact
    X f hX C hC hc (Brel ∩ W) S (hBrel.inter hW) hS
    (fun z hz => ⟨hSB hz,hDW (hSD hz)⟩) (fun z hz => (hSD hz).2) hvertical hfplane
    (fun s hs => (hdata s hs).2.2)
  obtain ⟨N1,hN1,hDN1,hN1e,hend⟩ := ContactTopology.ConvexDeformation.collar_endpoints_near_disk
    e he hD hfix X f hX C W hC hc hW hDW hAgree hfplane (fun s hs => (hdata s hs).2.2)
  have hSU : Icc (0:ℝ) 1 ×ˢ ContactTopology.ConvexDeformation.surfaceDisk ⊆
      (fun p : ℝ × (Fin 3 → ℝ) => f p.1 p.2) ⁻¹' U := by
    intro p hp
    change f p.1 p.2 ∈ U
    rw [hfplane p.1 p.2 hp.2.2]
    exact hDU hp.2
  obtain ⟨A2,B2,hA2,hB2,hIA2,hDB2,hAB2⟩ := generalized_tube_lemma isCompact_Icc
    ContactTopology.ConvexDeformation.surfaceDisk_compact (hU.preimage hf.continuous) hSU
  let N := (N0 ∩ N1) ∩ B2
  have hN : IsOpen N := (hN0.inter hN1).inter hB2
  have hDN : ContactTopology.ConvexDeformation.surfaceDisk ⊆ N :=
    fun y hy => ⟨⟨hDN0 hy,hDN1 hy⟩,hDB2 hy⟩
  let V0 := V2 ∩ N
  refine ⟨f,lam,N,E,V0,hf,hlam,hpos,hN,hDN,
    fun y hy => hN1e hy.1.2,hE,?_,hR,hfplane,fun y hy => hend y hy.1.2,
    hV2.inter hN,fun y hy => ⟨hSV2 hy,hDN (hSD hy)⟩,inter_subset_right,
    fun s hs y hy => hV2fix s hs y hy.1,?_⟩
  · intro p hp
    exact hEN0 ⟨hp.1,hp.2.1.1⟩
  · intro s hs
    refine ⟨fun y hy => hAB2 (show (s,y) ∈ A2 ×ˢ B2 from ⟨hIA2 hs,hy.2⟩),
      fun y hy => (hdata s hs).1 y hy.1.1,?_,?_⟩
    · intro y hy z hz heq
      have hxy : E (s,y)=E (s,z) := by
        rw [hE]
        exact Prod.ext rfl heq
      have hh := E.injOn (show (s,y) ∈ E.source from hEN0 ⟨hs,hy.1.1⟩)
        (show (s,z) ∈ E.source from hEN0 ⟨hs,hz.1.1⟩) hxy
      exact congrArg Prod.snd hh
    · intro y hy v
      have hh := (hdata s hs).2.1 y hy.1.1 v
      simpa only [ContactTopology.ConvexDeformation.covector_apply,ContactTopology.ConvexDeformation.dot,
        ContactTopology.ConvexDeformation.invariantCoefficients,ContactTopology.ConvexDeformation.xyMap_apply] using hh


open Set
open scoped ContDiff


namespace ContactTopology.Hemisphere
open ConvexDeformation BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
noncomputable section
def beta (x : P) : P := ![1+x 0^2-x 1^2, 2*x 0*x 1]
def normal (x : P) : ℝ := 2*x 1

lemma beta_contDiff : ContDiff ℝ ∞ beta := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [beta] <;> fun_prop

lemma normal_contDiff : ContDiff ℝ ∞ normal := by unfold normal; fun_prop

lemma normal_fderiv (x v : P) : fderiv ℝ normal x v = 2*v 1 := by
  have hd := ((ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul 2
  change HasFDerivAt normal _ x at hd
  rw [hd.fderiv]
  simp

lemma beta_fderiv (x v : P) : fderiv ℝ beta x v =
    ![2*x 0*v 0-2*x 1*v 1,2*v 0*x 1+2*x 0*v 1] := by
  let p (i : Fin 2) : P →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h0 := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).add
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)
  have h1 := (((p 0).hasFDerivAt (x := x)).const_mul 2).mul ((p 1).hasFDerivAt (x := x))
  change HasFDerivAt (fun z : P => 1+z 0^2-z 1^2) _ x at h0
  change HasFDerivAt (fun z : P => 2*z 0*z 1) _ x at h1
  have hD : HasFDerivAt beta (ContinuousLinearMap.pi
      ![fderiv ℝ (fun z : P => 1+z 0^2-z 1^2) x,
        fderiv ℝ (fun z : P => 2*z 0*z 1) x]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,p] <;> ring

lemma model_volume (x : P) : invariantVolume normal beta x=2*(1+x 0^2+3*x 1^2) := by
  simp [invariantVolume,normal_fderiv,beta_fderiv,beta,normal]
  ring

lemma model_positive (x : P) : 0 < invariantVolume normal beta x := by
  rw [model_volume]
  positivity


end
end ContactTopology.Hemisphere


open BirkhoffGlobalSection Set
open scoped ContDiff


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma modelCoeff_self_nonzero (x : V) : covector (modelCoeff x) (modelCoeff x) ≠ 0 := by
  have he : covector (modelCoeff x) (modelCoeff x)=(1+x 0^2+x 1^2)^2 := by
    simp [covector,modelCoeff]
    ring
  rw [he]
  apply pow_ne_zero
  nlinarith [sq_nonneg (x 0),sq_nonneg (x 1)]

theorem relative_coordinate_disk_model
    (C : V → Phase) (R : Phase → V) (Nc : Set V) (hNc : IsOpen Nc)
    (hC : ContDiff ℝ ∞ C) (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (hR : ∀ x ∈ Nc, ContDiffAt ℝ ∞ R (C x)) (hInv : ∀ x ∈ Nc, R (C x)=x)
    (hlocal : ∀ x ∈ Nc, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ Nc ∧ C (R y)=y)
    (hDchart : diskSet ⊆ Nc)
    (r : V → ℝ) (hrpos : ∀ x ∈ Nc, 0 < r x)
    (hchart : ∀ x ∈ Nc, ∀ v,
      phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (modelCoeff x) v)
    (G : EquivariantSphereContactomorphism)
    (hGdisk : ∀ x ∈ diskSet, G.toFun (C x)=C x)
    (Vb : Set Phase) (hVb : IsOpen Vb)
    (hboundary : ∀ x : V, x 0^2+x 1^2=1 → x 2=0 → C x ∈ Vb)
    (hGidentity : ∀ y ∈ Vb, y ∈ unitThreeSphere → G.toFun y=y) :
    ∃ e : OpenPartialHomeomorph V V, ∃ L : V → ℝ, ∃ Brel : Set V,
      ContDiffOn ℝ ∞ (e : V → V) e.source ∧
      ContDiffOn ℝ ∞ (e.symm : V → V) e.target ∧
      diskSet ⊆ e.source ∧ e.source ⊆ Nc ∧
      (∀ x ∈ e.source, x 2=0 → e x=x) ∧
      ContDiffOn ℝ ∞ L e.source ∧ (∀ x ∈ e.source, 0 < L x) ∧
      (∀ x ∈ e.source, ∀ v,
        covector (modelCoeff (e x)) (fderiv ℝ (e : V → V) x v)=L x*covector (modelCoeff x) v) ∧
      IsOpen Brel ∧ {x : V | x 0^2+x 1^2=1 ∧ x 2=0} ⊆ Brel ∧ Brel ⊆ e.source ∧
      (∀ x ∈ Brel, e x=x) ∧ ∀ x ∈ e.source, C (e x)=G.toFun (C x) := by
  obtain ⟨e0,he0,hg0,hs0,ht0,hCe0,hCg0,hfixed⟩ :=
    coordinate_partial_homeomorph C R Nc hNc hC hSphere hR hInv hlocal G
  have hpoint := coordinate_contact_factor C Nc hC hSphere modelCoeff r hrpos hchart G e0 he0 hs0 ht0 hCe0
  obtain ⟨L,hL,hpos,hpb⟩ := smooth_contact_factor modelCoeff modelCoeff_smooth e0 he0
    (fun x _ => modelCoeff_self_nonzero x) hpoint
  let U : Set V := {x | x 0^2+x 1^2 < 1} ∪ C ⁻¹' Vb
  have hU : IsOpen U := (isOpen_lt (by fun_prop) continuous_const).union (hVb.preimage hC.continuous)
  let e := e0.restrOpen U hU
  have hsource : e.source=e0.source ∩ U := rfl
  have hecoe : (e : V → V)=(e0 : V → V) := rfl
  have hgcoe : (e.symm : V → V)=(e0.symm : V → V) := rfl
  have hse0 : e.source ⊆ e0.source := inter_subset_left
  have hte0 : e.target ⊆ e0.target := inter_subset_left
  have hDsource : diskSet ⊆ e.source := by
    intro x hx
    refine ⟨(hfixed x (hDchart hx) (hGdisk x hx)).1,?_⟩
    by_cases hh : x 0^2+x 1^2 < 1
    · exact Or.inl hh
    · exact Or.inr (hboundary x (le_antisymm hx.1 (le_of_not_gt hh)) hx.2)
  have hboundaryFixed : ∀ x ∈ e.source, C x ∈ Vb → e x=x := by
    intro x hx hv
    exact (hfixed x (hs0 (hse0 hx)) (hGidentity (C x) hv (hSphere x))).2
  let Brel := e.source ∩ C ⁻¹' Vb
  have hBrel : IsOpen Brel := e.open_source.inter (hVb.preimage hC.continuous)
  refine ⟨e,L,Brel,he0.mono hse0,hg0.mono hte0,hDsource,hse0.trans hs0,?_,hL.mono hse0,
    (fun x hx => hpos x (hse0 hx)),(fun x hx v => hpb x (hse0 hx) v),hBrel,?_,inter_subset_left,?_,?_⟩
  · intro x hx hx0
    rcases hx.2 with hh | hh
    · exact (hfixed x (hs0 hx.1) (hGdisk x ⟨hh.le,hx0⟩)).2
    · exact hboundaryFixed x hx hh
  · intro x hx
    exact ⟨hDsource ⟨hx.1.le,hx.2⟩,hboundary x hx.1 hx.2⟩
  · intro x hx
    exact hboundaryFixed x hx.1 hx.2
  · intro x hx
    exact hCe0 x (hse0 hx)

end
end ContactTopology.SphereTransfer


namespace ContactTopology.SphereTransfer
open BirkhoffGlobalSection Set Function Filter
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem given_chart_local_realization
    (C : V → Phase) (R : Phase → V) (Nc : Set V) (hNc : IsOpen Nc)
    (hC : ContDiff ℝ ∞ C) (hSphere : ∀ x, C x ∈ unitThreeSphere)
    (hR : ∀ x ∈ Nc, ContDiffAt ℝ ∞ R (C x)) (hInv : ∀ x ∈ Nc, R (C x)=x)
    (hlocal : ∀ x ∈ Nc, ∃ O : Set Phase, IsOpen O ∧ C x ∈ O ∧
      ∀ y ∈ O, y ∈ unitThreeSphere → R y ∈ Nc ∧ C (R y)=y)
    (hDchart : diskSet ⊆ Nc)
    (r : V → ℝ) (hrpos : ∀ x ∈ Nc, 0 < r x)
    (hchart : ∀ x ∈ Nc, ∀ v,
      phaseRadialContact (C x) (fderiv ℝ C x v)=r x*covector (modelCoeff x) v)
    (hoverlap : (C '' diskSet) ∩ ((fun y : Phase => -y) '' (C '' diskSet)) ⊆
      C '' {x : V | x 0^2+x 1^2=1 ∧ x 2=0})
    (e : OpenPartialHomeomorph V V)
    (he : ContDiffOn ℝ ∞ (e : V → V) e.source)
    (hG : ContDiffOn ℝ ∞ (e.symm : V → V) e.target)
    (hD : diskSet ⊆ e.source) (hfix : ∀ y ∈ e.source, y 2=0 → e y=y)
    (L : V → ℝ) (hL : ContDiffOn ℝ ∞ L e.source) (hpositive : ∀ y ∈ e.source, 0 < L y)
    (hpb : ∀ y ∈ e.source, ∀ v,
      covector (modelCoeff (e y)) (fderiv ℝ (e : V → V) y v)=L y*covector (modelCoeff y) v)
    (Brel : Set V) (hBrel : IsOpen Brel) (hBe : Brel ⊆ e.source)
    (hboundary : {y : V | y 0^2+y 1^2=1 ∧ y 2=0} ⊆ Brel)
    (hBfix : ∀ y ∈ Brel, e y=y) :
    ∃ E : EquivariantSphereContactomorphism, ∃ J : EquivariantSphereContactIsotopy E,
    ∃ M : Set V,
      IsOpen M ∧ diskSet ⊆ M ∧ M ⊆ e.source ∩ Nc ∧
      (∀ x ∈ M, E.toFun (C x)=C (e x)) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ diskSet, (J.slice t).toFun (C x)=C x := by
  let u := ContactTopology.Hemisphere.normal
  let β := ContactTopology.Hemisphere.beta
  have hu := ContactTopology.Hemisphere.normal_contDiff
  have hβ := ContactTopology.Hemisphere.beta_contDiff
  have hQ (x : Fin 2 → ℝ) :
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
      u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) ≠ 0 :=
    (ContactTopology.Hemisphere.model_positive x).ne'
  let S : Set V := {y | y 0^2+y 1^2=1 ∧ y 2=0}
  have hSclosed : IsClosed S :=
    (isClosed_eq (by fun_prop : Continuous (fun y : V => y 0^2+y 1^2)) continuous_const).inter
      (isClosed_eq (continuous_apply 2) continuous_const)
  have hSD : S ⊆ diskSet := fun y hy => ⟨hy.1.le,hy.2⟩
  have hS : IsCompact S := diskSet_compact.of_isClosed_subset hSclosed hSD
  obtain ⟨f,lam,N,E0,V0,hf,hlam,hpos,hN,hDN,hNe,hE0,hEN,hR0,hplane,hend,hV0,hSV0,hV0N,hV0fixed,hdata⟩ :=
    ContactTopology.relative_disk_contact_embedding_family_internal u β hu hβ hQ e he hG hD hfix L hL hpositive
      S Brel hS hSD hBrel hboundary hBe hBfix Set.univ isOpen_univ (fun _ _ => mem_univ _) hpb
  let θ : ℝ → ℝ := Real.smoothTransition
  have hθ : ContDiff ℝ ∞ θ := Real.smoothTransition.contDiff
  have hθ01 (s : ℝ) : θ s ∈ Icc (0:ℝ) 1 := ⟨Real.smoothTransition.nonneg s,Real.smoothTransition.le_one s⟩
  have hθ0 : θ 0=0 := Real.smoothTransition.zero
  have hθ1 : θ 1=1 := Real.smoothTransition.one
  let g : ℝ → V → V := fun s => f (θ s)
  let ell : ℝ → V → ℝ := fun s => lam (θ s)
  have harg : ContDiff ℝ ∞ (fun p : ℝ × V => (θ p.1,p.2)) :=
    (hθ.comp contDiff_fst).prodMk contDiff_snd
  have hg := hf.comp harg
  have hell := hlam.comp harg
  have hinj : ∀ s, InjOn (g s) N := by
    intro s x hx y hy heq
    exact (hdata (θ s) (hθ01 s)).2.2.1 x hx y hy heq
  have hder : ∀ s x, x ∈ N → Injective (fderiv ℝ (g s) x) :=
    fun s x hx => (hdata (θ s) (hθ01 s)).2.1 x hx
  have hg0 : ∀ x ∈ N, g 0 x=x := by
    intro x hx
    simpa only [g,hθ0] using (hend x hx).1
  let B := V0 ∩ Nc
  have hB : IsOpen B := hV0.inter hNc
  have hBg : ∀ s x, x ∈ B → g s x=x := fun s x hx => hV0fixed (θ s) (hθ01 s) x hx.1
  have hDg : ∀ s ∈ Icc (0:ℝ) 1, ∀ x ∈ diskSet, g s x=x := fun s _ x hx => hplane (θ s) x hx.2
  have hoverlapB : (C '' diskSet) ∩ ((fun y : Phase => -y) '' (C '' diskSet)) ⊆ C '' B := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := hoverlap hy
    exact ⟨x,⟨hSV0 hx,hDchart (hSD hx)⟩,rfl⟩
  obtain ⟨E,J,M,P,hM,hDM,hMN,hP,hPs,hsep,hmatch,hDfixed,hout⟩ :=
    relative_chart_equivariant_extension C R Nc hNc hC hSphere hR hInv hlocal
      modelCoeff modelCoeff_smooth modelCoeff_contact r hrpos hchart
      g hg ell hell N hN hinj hder hg0 (fun s x _ => hpos (θ s) x)
      (fun s x hx v => (hdata (θ s) (hθ01 s)).2.2.2 x hx v)
      diskSet B diskSet_compact hDN hDchart hB (fun x hx => hV0N hx.1) inter_subset_right hBg hDg hoverlapB
  refine ⟨E,J,M,hM,hDM,(fun x hx => ⟨hNe (hMN hx).1,(hMN hx).2⟩),?_,hDfixed⟩
  intro x hx
  have hfx : g 1 x=e x := by simpa only [g,hθ1] using (hend x (hMN hx).1).2
  simpa only [hfx] using hmatch x hx

end
end ContactTopology.SphereTransfer


open BirkhoffGlobalSection Set
open scoped ContDiff

theorem solution
    (F G : EquivariantSphereContactomorphism)
    (Vb : Set Phase) (hVb : IsOpen Vb)
    (hboundary : ∀ u : Plane, u 0^2+u 1^2=1 → F.toFun ![u 0,u 1,0,0] ∈ Vb)
    (hGidentity : ∀ y ∈ Vb, y ∈ unitThreeSphere → G.toFun y=y) :
    let d : Plane → Phase := fun u =>
      ![2*u 0/(1+(u 0^2+u 1^2)),2*u 1/(1+(u 0^2+u 1^2)),
        (1-(u 0^2+u 1^2))/(1+(u 0^2+u 1^2)),0]
    (∀ u : Plane, u 0^2+u 1^2 ≤ 1 → G.toFun (F.toFun (d u))=F.toFun (d u)) →
    ∃ H : EquivariantSphereContactomorphism,
    ∃ K : ℝ → EquivariantSphereContactomorphism, ∃ U : Set Phase,
      IsOpen U ∧ (∀ y ∈ U, -y ∈ U) ∧
      (∀ u : Plane, u 0^2+u 1^2 ≤ 1 → F.toFun (d u) ∈ U) ∧
      (∀ y ∈ U, y ∈ unitThreeSphere → H.toFun y=y) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y ∈ unitThreeSphere,
        ContDiffAt ℝ ∞ (fun p : ℝ × Phase => (K p.1).toFun p.2) (t,y)) ∧
      (∀ y ∈ unitThreeSphere, (K 0).toFun y=G.toFun y) ∧
      (∀ y ∈ unitThreeSphere, (K 1).toFun y=H.toFun y) ∧
      ∀ t ∈ Icc (0:ℝ) 1, ∀ u : Plane, u 0^2+u 1^2 ≤ 1 →
        (K t).toFun (F.toFun (d u))=F.toFun (d u) := by


  dsimp only
  intro hGdisk
  obtain ⟨C,R,r,Nc,hC,hr,hrpos,hNc,hDNc,hSphere,hstart,hEmb,hRi,hchart,hlocal,hdivide,hleg⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let D := ContactTopology.SphereTransfer.diskSet
  have hDchart : D ⊆ Nc := by
    intro y hy
    have heq : (![y 0,y 1,0] : Fin 3 → ℝ)=y := by ext i; fin_cases i <;> simp [hy.2]
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,heq] using hDNc ![y 0,y 1] hy.1
  have hCDisk : ∀ y ∈ D, C y=ContactTopology.CoreDisk.imageDisk F ![y 0,y 1] := by
    intro y hy
    have heq : (![y 0,y 1,0] : Fin 3 → ℝ)=y := by ext i; fin_cases i <;> simp [hy.2]
    have hh := hstart ![y 0,y 1]
    simpa only [heq,ContactTopology.CoreDisk.imageDisk,ContactTopology.CoreDisk.disk,
      planeNormSq,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc,
      sub_add_eq_sub_sub] using hh
  have hGcoordinate : ∀ x ∈ D, G.toFun (C x)=C x := by
    intro x hx
    rw [hCDisk x hx]
    exact hGdisk ![x 0,x 1] hx.1
  have hboundaryC : ∀ x : Fin 3 → ℝ, x 0^2+x 1^2=1 → x 2=0 → C x ∈ Vb := by
    intro x hx hx0
    rw [hCDisk x ⟨hx.le,hx0⟩,ContactTopology.CoreDisk.imageDisk_boundary F ![x 0,x 1] hx]
    exact hboundary ![x 0,x 1] hx
  have hchart' : ∀ x ∈ Nc, ∀ v,
      phaseRadialContact (C x) (fderiv ℝ C x v)=r x*
        ContactTopology.SphereTransfer.covector (ContactTopology.SphereTransfer.modelCoeff x) v := hchart
  obtain ⟨e,L,Brel,he,hGe,hDe,hsource,hplane,hL,hLpos,hpb,hBrel,hboundarye,hBe,hBfix,hCemap⟩ :=
    ContactTopology.SphereTransfer.relative_coordinate_disk_model C R Nc hNc hC hSphere
      (fun x hx => (hRi x hx).1) (fun x hx => (hRi x hx).2.1) hlocal hDchart
      r (fun x _ => hrpos x) hchart' G hGcoordinate Vb hVb hboundaryC hGidentity
  have hoverlap : (C '' D) ∩ ((fun y : Phase => -y) '' (C '' D)) ⊆
      C '' {x : Fin 3 → ℝ | x 0^2+x 1^2=1 ∧ x 2=0} := by
    rintro y ⟨⟨x,hx,rfl⟩,hz⟩
    obtain ⟨_,⟨z,hz,rfl⟩,heq⟩ := hz
    have hh : ContactTopology.CoreDisk.imageDisk F ![x 0,x 1]=
        -ContactTopology.CoreDisk.imageDisk F ![z 0,z 1] := by
      rw [← hCDisk x hx,← hCDisk z hz]
      exact heq.symm
    have hb := (ContactTopology.CoreDisk.imageDisk_antipodal_fibers F ![x 0,x 1] ![z 0,z 1] hx.1 hz.1).mp hh
    exact ⟨x,⟨hb.1,hx.2⟩,rfl⟩
  obtain ⟨E,J,M,hM,hDM,hMN,hmatch,hJfix⟩ :=
    ContactTopology.SphereTransfer.given_chart_local_realization C R Nc hNc hC hSphere
      (fun x hx => (hRi x hx).1) (fun x hx => (hRi x hx).2.1) hlocal hDchart
      r (fun x _ => hrpos x) hchart' hoverlap e he hGe hDe hplane L hL hLpos hpb Brel hBrel hBe hboundarye hBfix
  obtain ⟨U,hU,hMU,hUdata⟩ := ContactTopology.SphereTransfer.chart_relative_open C R Nc M
    (fun x hx => (hRi x hx).2.1) (fun x hx => (hRi x hx).1) hM
    (fun x hx => (hMN hx).2) hlocal
  let H := ContactTopology.SphereContactAlgebra.compose (ContactTopology.SphereContactAlgebra.inverse E) G
  let Ji := ContactTopology.SphereContactAlgebra.isotopy_inverse E J
  let K : ℝ → EquivariantSphereContactomorphism := fun t =>
    ContactTopology.SphereContactAlgebra.compose (Ji.slice t) G
  have hHfix : ∀ y ∈ U, y ∈ unitThreeSphere → H.toFun y=y := by
    intro y hy hys
    have hxy := (hUdata y hy hys).2
    have hxM := (hUdata y hy hys).1
    have hEy : E.toFun y=G.toFun y := by
      calc
        E.toFun y=E.toFun (C (R y)) := by rw [hxy]
        _=C (e (R y)) := hmatch (R y) hxM
        _=G.toFun (C (R y)) := hCemap (R y) (hMN hxM).1
        _=G.toFun y := by rw [hxy]
    change E.invFun (G.toFun y)=y
    rw [← hEy,E.left_inv y hys]
  let W := U ∪ ((fun y : Phase => -y) '' U)
  have hW : IsOpen W := hU.union
    ((ContinuousLinearEquiv.neg ℝ : Phase ≃L[ℝ] Phase).isOpenMap U hU)
  have hWneg : ∀ y ∈ W, -y ∈ W := by
    intro y hy
    rcases hy with hy | ⟨z,hz,rfl⟩
    · exact Or.inr ⟨y,hy,rfl⟩
    · exact Or.inl (by simpa only [neg_neg] using hz)
  have hKfix : ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ D, (K t).toFun (C x)=C x := by
    intro t ht x hx
    have hsub : 1-t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    change E.invFun ((J.slice (1-t)).toFun (G.toFun (C x)))=C x
    rw [hGcoordinate x hx,hJfix (1-t) hsub x hx]
    have hEfix : E.toFun (C x)=C x :=
      (J.finish (C x) (hSphere x)).symm.trans (hJfix 1 (by constructor <;> norm_num) x hx)
    simpa only [hEfix] using E.left_inv (C x) (hSphere x)
  refine ⟨H,K,W,hW,hWneg,?_,?_,?_,?_,?_,?_⟩
  · intro u hu
    have hx : (![u 0,u 1,0] : Fin 3 → ℝ) ∈ M := hDM ⟨hu,rfl⟩
    have hh := hMU ⟨![u 0,u 1,0],hx,rfl⟩
    exact Or.inl (by simpa only [hstart,add_assoc,sub_add_eq_sub_sub] using hh)
  · intro y hy hys
    rcases hy with hy | ⟨z,hz,rfl⟩
    · exact hHfix y hy hys
    · have hzs := ContactTopology.SphereTransfer.sphere_neg hys
      simp only [neg_neg] at hzs
      rw [H.antipodal z hzs,hHfix z hz hzs]
  · intro t ht y hy
    have hG : ContDiffAt ℝ ∞ (fun p : ℝ × Phase => G.toFun p.2) (t,y) :=
      (G.smooth y hy).comp (t,y) contDiffAt_snd
    exact ContDiffAt.comp (g := fun p : ℝ × Phase => (Ji.slice p.1).toFun p.2)
      (f := fun p : ℝ × Phase => (p.1,G.toFun p.2)) (t,y)
      (Ji.smooth t ht (G.toFun y) (G.maps_sphere hy)) (contDiffAt_fst.prodMk hG)
  · intro y hy
    exact Ji.start (G.toFun y) (G.maps_sphere hy)
  · intro y hy
    exact Ji.finish (G.toFun y) (G.maps_sphere hy)
  · intro t ht u hu
    have hh := hKfix t ht ![u 0,u 1,0] ⟨hu,rfl⟩
    simpa only [hstart,add_assoc,sub_add_eq_sub_sub] using hh
