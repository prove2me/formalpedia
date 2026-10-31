-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_disk_equivariant_embedding_extension
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-31T00:18:31.779199+00:00
-- url     : https://prove2.me/submissions/03afdf95-a237-449c-85d0-a143db9000fc

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Theorems.Thm_BirkhoffGlobalSection_radial_normalization_contact_identity
import Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood
import Theorems.Thm_ContactTopology_relative_compact_contact_embedding_isotopy_extension


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


open BirkhoffGlobalSection Set
open scoped ContDiff

theorem solution
    (F : EquivariantSphereContactomorphism)
    (g : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hg : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g p.1 p.2))
    (lam : ℝ → (Fin 3 → ℝ) → ℝ)
    (hlam : ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => lam p.1 p.2))
    (N B : Set (Fin 3 → ℝ)) (hN : IsOpen N) (hB : IsOpen B)
    (hDN : {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ N)
    (hBN : B ⊆ N)
    (hboundary : {y : Fin 3 → ℝ | y 0^2+y 1^2=1 ∧ y 2=0} ⊆ B)
    (hinj : ∀ s, InjOn (g s) N)
    (hder : ∀ s x, x ∈ N → Function.Injective (fderiv ℝ (g s) x))
    (h0 : ∀ x ∈ N, g 0 x=x)
    (hstationary : ∀ s x, x ∈ B → g s x=x)
    (hDfix : ∀ s ∈ Icc (0:ℝ) 1, ∀ x : Fin 3 → ℝ, x 0^2+x 1^2 ≤ 1 → x 2=0 → g s x=x)
    (hpos : ∀ s x, x ∈ N → 0 < lam s x) :
    let I0 : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun y v =>
      (1+y 0^2-y 1^2)*v 0+(2*y 0*y 1)*v 1+(2*y 1)*v 2
    (∀ s x, x ∈ N → ∀ v, I0 (g s x) (fderiv ℝ (g s) x v)=lam s x*I0 x v) →
    ∃ C : (Fin 3 → ℝ) → Phase,
      ContDiff ℝ ∞ C ∧ (∀ x, C x ∈ unitThreeSphere) ∧
      (∀ x : Fin 2 → ℝ, C ![x 0,x 1,0]=F.toFun
        ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
          (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
      ∃ E : EquivariantSphereContactomorphism, ∃ J : EquivariantSphereContactIsotopy E,
      ∃ M : Set (Fin 3 → ℝ), ∃ P : Set Phase,
        IsOpen M ∧ {y : Fin 3 → ℝ | y 0^2+y 1^2 ≤ 1 ∧ y 2=0} ⊆ M ∧ M ⊆ N ∧
        Topology.IsEmbedding (fun x : M => C x) ∧
        IsCompact P ∧ P ⊆ unitThreeSphere ∧ (∀ y ∈ P, -y ∉ P) ∧
        (∀ x ∈ M, E.toFun (C x)=C (g 1 x)) ∧
        (∀ t ∈ Icc (0:ℝ) 1, ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 →
          (J.slice t).toFun (F.toFun
            ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0])=
          F.toFun ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
              (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]) ∧
        ∀ t y, y ∈ unitThreeSphere → y ∉ P ∪ ((fun z : Phase => -z) '' P) →
          (J.slice t).toFun y=y := by


  dsimp only
  intro hpb
  obtain ⟨C,R,r,Nc,hC,hr,hrpos,hNc,hDNc,hSphere,hstart,hEmb,hRi,hchart,hlocal,hdivide,hleg⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let D := ContactTopology.SphereTransfer.diskSet
  have hD := ContactTopology.SphereTransfer.diskSet_compact
  have hDchart : D ⊆ Nc := by
    intro y hy
    have heq : (![y 0,y 1,0] : Fin 3 → ℝ)=y := by ext i; fin_cases i <;> simp [hy.2]
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,heq] using hDNc ![y 0,y 1] hy.1
  let B0 := B ∩ Nc
  have hB0 : IsOpen B0 := hB.inter hNc
  have hCDisk : ∀ y ∈ D, C y=ContactTopology.CoreDisk.imageDisk F ![y 0,y 1] := by
    intro y hy
    have heq : (![y 0,y 1,0] : Fin 3 → ℝ)=y := by ext i; fin_cases i <;> simp [hy.2]
    have hh := hstart ![y 0,y 1]
    simpa only [heq,ContactTopology.CoreDisk.imageDisk,ContactTopology.CoreDisk.disk,
      planeNormSq,Function.comp_apply,Matrix.cons_val_zero,Matrix.cons_val_one,add_assoc,
      sub_add_eq_sub_sub] using hh
  have hoverlap : (C '' D) ∩ ((fun y : Phase => -y) '' (C '' D)) ⊆ C '' B0 := by
    rintro y ⟨⟨x,hx,rfl⟩,hz⟩
    obtain ⟨_,⟨z,hz,rfl⟩,heq⟩ := hz
    have he : ContactTopology.CoreDisk.imageDisk F ![x 0,x 1]=
        -ContactTopology.CoreDisk.imageDisk F ![z 0,z 1] := by
      rw [← hCDisk x hx,← hCDisk z hz]
      exact heq.symm
    have hb := (ContactTopology.CoreDisk.imageDisk_antipodal_fibers F ![x 0,x 1] ![z 0,z 1] hx.1 hz.1).mp he
    exact ⟨x,⟨hboundary ⟨hb.1,hx.2⟩,hDchart hx⟩,rfl⟩
  let a := ContactTopology.SphereTransfer.modelCoeff
  have hchart' : ∀ x ∈ Nc, ∀ v,
      phaseRadialContact (C x) (fderiv ℝ C x v)=r x*ContactTopology.SphereTransfer.covector (a x) v := by
    intro x hx v
    exact hchart x hx v
  obtain ⟨E,J,M,P,hM,hDM,hMN,hP,hPs,hPsep,hend,hfix,hout⟩ :=
    ContactTopology.SphereTransfer.relative_chart_equivariant_extension C R Nc hNc hC hSphere
      (fun x hx => (hRi x hx).1) (fun x hx => (hRi x hx).2.1) hlocal
      a ContactTopology.SphereTransfer.modelCoeff_smooth ContactTopology.SphereTransfer.modelCoeff_contact
      r (fun x _ => hrpos x) hchart' g hg lam hlam N hN hinj hder h0 hpos hpb
      D B0 hD hDN hDchart hB0 (fun x hx => hBN hx.1) inter_subset_right
      (fun s x hx => hstationary s x hx.1) (fun s hs x hx => hDfix s hs x hx.1 hx.2) hoverlap
  refine ⟨C,hC,hSphere,hstart,E,J,M,P,hM,hDM,(fun x hx => (hMN hx).1),?_,hP,hPs,hPsep,hend,?_,hout⟩
  · exact hEmb.comp ((Topology.IsEmbedding.subtypeVal :
      Topology.IsEmbedding (Subtype.val : M → (Fin 3 → ℝ))).codRestrict Nc
      (fun x => (hMN x.property).2))
  · intro t ht x hx
    have hh := hfix t ht ![x 0,x 1,0] ⟨hx,rfl⟩
    simpa only [hstart] using hh
