-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/902b3087-f5c5-5ba5-ad88-8805321c2ad4

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
import Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

noncomputable section

namespace PkgDesc18

universe u

variable {R : Type u} [CommRing R]

abbrev ι (A : Type u) [CommRing A] [Algebra R A] : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

theorem specMap_comp_ι {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ι (R := R) A = ι B := by
  rw [ι, ι, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

variable {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))

def q {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    pullback f (ι B) ⟶ pullback f (ι A) :=
  pullback.lift (pullback.fst f (ι B)) (pullback.snd f (ι B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (by rw [Category.assoc, specMap_comp_ι, pullback.condition])

@[scoped simp] theorem q_fst {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    q f φ ≫ pullback.fst f (ι A) = pullback.fst f (ι B) := pullback.lift_fst _ _ _

@[scoped simp] theorem q_snd {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    q f φ ≫ pullback.snd f (ι A) = pullback.snd f (ι B) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) :=
  pullback.lift_snd _ _ _

theorem q_comp {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
    (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C) : q f ψ ≫ q f φ = q f (ψ.comp φ) := by
  apply pullback.hom_ext
  · simp only [q, Category.assoc, pullback.lift_fst]
  · simp only [q, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp]; rfl

def restage {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    pullback f (ι B) ⟶ pullback g (ι B) :=
  pullback.lift (q f φ ≫ a ≫ pullback.fst g (ι A)) (pullback.snd f (ι B))
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc a, ha, ← Category.assoc, q_snd,
      Category.assoc, specMap_comp_ι])

@[scoped simp] theorem restage_fst {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ pullback.fst g (ι B) = q f φ ≫ a ≫ pullback.fst g (ι A) := pullback.lift_fst _ _ _

@[scoped simp] theorem restage_snd {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ pullback.snd g (ι B) = pullback.snd f (ι B) := pullback.lift_snd _ _ _

theorem restage_q {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha ≫ q g φ = q f φ ≫ a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, q_fst, restage_fst]
  · rw [Category.assoc, q_snd, ← Category.assoc, restage_snd, Category.assoc, ha, q_snd]

theorem eq_restage {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A))
    (α : pullback f (ι B) ⟶ pullback g (ι B)) (hα : α ≫ pullback.snd g (ι B) = pullback.snd f (ι B))
    (h : α ≫ q g φ = q f φ ≫ a) : α = restage f g φ a ha := by
  apply pullback.hom_ext
  · rw [restage_fst, ← Category.assoc, ← h, Category.assoc, q_fst]
  · rw [restage_snd, hα]

theorem restage_id {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) :
    restage f f φ (𝟙 _) (Category.id_comp _) = 𝟙 _ :=
  (eq_restage f f φ _ _ _ (Category.id_comp _) (by simp)).symm

theorem restage_comp (h : Z ⟶ Spec (CommRingCat.of R)) {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A))
    (b : pullback g (ι A) ⟶ pullback h (ι A)) (hb : b ≫ pullback.snd h (ι A) = pullback.snd g (ι A)) :
    restage f h φ (a ≫ b) (by rw [Category.assoc, hb, ha]) = restage f g φ a ha ≫ restage g h φ b hb :=
  (eq_restage f h φ _ _ _ (by rw [Category.assoc, restage_snd, restage_snd])
    (by rw [Category.assoc, restage_q, ← Category.assoc, restage_q, Category.assoc])).symm

theorem restage_restage {A B C : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [CommRing C]
    [Algebra R C] (φ : A →ₐ[R] B) (ψ : B →ₐ[R] C)
    (a : pullback f (ι A) ⟶ pullback g (ι A)) (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g ψ (restage f g φ a ha) (restage_snd f g φ a ha) = restage f g (ψ.comp φ) a ha :=
  eq_restage f g (ψ.comp φ) _ _ _ (restage_snd _ _ _ _ _)
    (by rw [← q_comp, ← q_comp, ← Category.assoc, restage_q, Category.assoc, restage_q, Category.assoc])

theorem restage_congr {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    {a a' : pullback f (ι A) ⟶ pullback g (ι A)} (h : a = a')
    (ha : a ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) (ha' : a' ≫ pullback.snd g (ι A) = pullback.snd f (ι A)) :
    restage f g φ a ha = restage f g φ a' ha' := by subst h; rfl

theorem exists_fg_restage_eq {L : Type u} [CommRing L] [Algebra R L] (T₁ : Subalgebra R L) (hT₁ : T₁.FG)
    [QuasiCompact f] [LocallyOfFiniteType g]
    (a b : pullback f (ι ↥T₁) ⟶ pullback g (ι ↥T₁))
    (ha : a ≫ pullback.snd g (ι ↥T₁) = pullback.snd f (ι ↥T₁)) (hb : b ≫ pullback.snd g (ι ↥T₁) = pullback.snd f (ι ↥T₁))
    (hab : q f T₁.val ≫ a = q f T₁.val ≫ b) (s : Finset L) :
    ∃ (T₂ : Subalgebra R L) (h₁₂ : T₁ ≤ T₂), T₂.FG ∧ (↑s : Set L) ⊆ T₂ ∧
      restage f g (Subalgebra.inclusion h₁₂) a ha = restage f g (Subalgebra.inclusion h₁₂) b hb := by
  classical

  have hsc : Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L)) ≫ ι (R := R) ↥T₁ = ι L := specMap_comp_ι T₁.val
  let D := pullback (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L)))
  let κ : D ⟶ pullback f (ι L) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst f (ι ↥T₁)) (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, hsc])
  have hκ : pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) = κ ≫ q f T₁.val := by
    apply pullback.hom_ext
    · simp only [Category.assoc, q_fst, κ, pullback.lift_fst]
    · simp only [Category.assoc, q_snd, κ, pullback.lift_snd_assoc]
      exact pullback.condition
  have hab' : pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) ≫ a =
      pullback.fst (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ L))) ≫ b := by
    rw [hκ, Category.assoc, hab, Category.assoc]
  obtain ⟨T₂', hT₂'fg, hsT₂', heq⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_pullback_fst_comp_eq_of_locallyOfFiniteType
      (pullback.snd f (ι ↥T₁)) (pullback.snd g (ι ↥T₁)) a b ha hb hab' s

  refine ⟨T₂'.restrictScalars R, fun x hx => ?_, ?_, hsT₂', ?_⟩
  · show x ∈ T₂'
    have : algebraMap ↥T₁ L ⟨x, hx⟩ ∈ T₂' := T₂'.algebraMap_mem _
    exact this
  · have h1 : (⊤ : Subalgebra R ↥T₁).FG := (Subalgebra.fg_top T₁).2 hT₁
    have h2 : (⊤ : Subalgebra ↥T₁ ↥T₂').FG := (Subalgebra.fg_top T₂').2 hT₂'fg
    have h3 : (⊤ : Subalgebra R ↥T₂').FG := Algebra.fg_trans' h1 h2
    have h4 : T₂'.restrictScalars R = (⊤ : Subalgebra R ↥T₂').map (T₂'.val.restrictScalars R) := by
      ext x
      rw [Subalgebra.mem_restrictScalars, Subalgebra.mem_map]
      constructor
      · intro hx'; exact ⟨⟨x, hx'⟩, Algebra.mem_top, rfl⟩
      · rintro ⟨y, -, rfl⟩; exact y.2
    rw [h4]; exact h3.map _
  ·
    set h₁₂ : T₁ ≤ T₂'.restrictScalars R := fun x hx =>
      show x ∈ T₂' from (T₂'.algebraMap_mem (⟨x, hx⟩ : ↥T₁) : algebraMap ↥T₁ L ⟨x, hx⟩ ∈ T₂') with hh
    let j : ↥(T₂'.restrictScalars R) →+* ↥T₂' :=
      { toFun := fun x => ⟨x.1, x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    have hj : (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂')) ≫ CommRingCat.ofHom j =
        CommRingCat.ofHom (Subalgebra.inclusion h₁₂).toRingHom := by
      rw [← CommRingCat.ofHom_comp]; rfl
    let r : pullback f (ι ↥(T₂'.restrictScalars R)) ⟶
        pullback (pullback.snd f (ι ↥T₁)) (Spec.map (CommRingCat.ofHom (algebraMap ↥T₁ ↥T₂'))) :=
      pullback.lift (q f (Subalgebra.inclusion h₁₂)) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom j))
        (by rw [q_snd, Category.assoc, ← Spec.map_comp]; erw [hj])
    have hr : r ≫ pullback.fst _ _ = q f (Subalgebra.inclusion h₁₂) := pullback.lift_fst _ _ _
    apply pullback.hom_ext
    · rw [restage_fst, restage_fst, ← hr, Category.assoc, Category.assoc, reassoc_of% heq]
    · rw [restage_snd, restage_snd]

end PkgDesc18
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18"

namespace PkgDesc17

section restage

variable {A₀ B B' : Type} [CommRing A₀] [CommRing B] [CommRing B']
  (β : A₀ →+* B) (β' : A₀ →+* B') (φ : B →+* B') (hφ : φ.comp β = β')
  {X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))

include hφ in
theorem spec_comp : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom β) := by
  rw [← hφ, CommRingCat.ofHom_comp, Spec.map_comp]

private noncomputable def _root_.PkgDesc17.trans {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    pullback f (Spec.map (CommRingCat.ofHom β')) ⟶ pullback f (Spec.map (CommRingCat.ofHom β)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ))
    (by rw [pullback.condition, Category.assoc, ← spec_comp β β' φ hφ])

p2m_export "PkgDesc17" "trans"
@[scoped simp] theorem trans_fst {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    trans β β' φ hφ f ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[scoped simp] theorem trans_snd {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A₀)) :
    trans β β' φ hφ f ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom φ) := pullback.lift_snd _ _ _

include hφ in

theorem restage_hom
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom β)) ⟶ pullback f₂ (Spec.map (CommRingCat.ofHom β)))
    (hg : g ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ g' : pullback f₁ (Spec.map (CommRingCat.ofHom β')) ⟶ pullback f₂ (Spec.map (CommRingCat.ofHom β')),
      g' ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      g' ≫ pullback.fst _ _ = trans β β' φ hφ f₁ ≫ g ≫ pullback.fst _ _ ∧
      trans β β' φ hφ f₁ ≫ g = g' ≫ trans β β' φ hφ f₂ := by
  have hc : (trans β β' φ hφ f₁ ≫ g ≫ pullback.fst _ _) ≫ f₂ =
      pullback.snd f₁ (Spec.map (CommRingCat.ofHom β')) ≫ Spec.map (CommRingCat.ofHom β') := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g, hg, ← Category.assoc, trans_snd,
      Category.assoc, ← spec_comp β β' φ hφ]
  refine ⟨pullback.lift _ _ hc, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, trans_fst, pullback.lift_fst]
  · simp only [Category.assoc, trans_snd, pullback.lift_snd_assoc]
    rw [hg, trans_snd]

include hφ in

theorem restage_iso
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom β)) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom β)))
    (he : e.hom ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ e' : pullback f₁ (Spec.map (CommRingCat.ofHom β')) ≅ pullback f₂ (Spec.map (CommRingCat.ofHom β')),
      e'.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      e'.hom ≫ pullback.fst _ _ = trans β β' φ hφ f₁ ≫ e.hom ≫ pullback.fst _ _ ∧
      trans β β' φ hφ f₁ ≫ e.hom = e'.hom ≫ trans β β' φ hφ f₂ := by
  have he' : e.inv ≫ pullback.snd _ _ = pullback.snd _ _ := by rw [Iso.inv_comp_eq, he]
  obtain ⟨F, hF₂, hF₁, hF⟩ := restage_hom β β' φ hφ f₁ f₂ e.hom he
  obtain ⟨G, hG₂, hG₁, hG⟩ := restage_hom β β' φ hφ f₂ f₁ e.inv he'
  have hFG : F ≫ G = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hG₁, ← Category.assoc F, ← hF, Category.assoc, Iso.hom_inv_id_assoc,
        trans_fst, Category.id_comp]
    · rw [Category.assoc, hG₂, hF₂, Category.id_comp]
  have hGF : G ≫ F = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hF₁, ← Category.assoc G, ← hG, Category.assoc, Iso.inv_hom_id_assoc,
        trans_fst, Category.id_comp]
    · rw [Category.assoc, hF₂, hG₂, Category.id_comp]
  exact ⟨⟨F, G, hFG, hGF⟩, hF₂, hF₁, hF⟩

end restage
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18"

section insts
variable {S : Type} [CommRing S] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (E : FakeEllipticCurve Λ N S)

theorem qc_f : QuasiCompact E.f := by haveI := E.bundle.proper; infer_instance
theorem qs_f : QuasiSeparated E.f := by haveI := E.bundle.proper; infer_instance
theorem lfp_f : LocallyOfFinitePresentation E.f := by haveI := E.bundle.smooth; infer_instance
theorem qc_lev : QuasiCompact (E.lev ≫ E.f) := by haveI := E.lev_finite; infer_instance
theorem qs_lev : QuasiSeparated (E.lev ≫ E.f) := by haveI := E.lev_finite; infer_instance
theorem lfp_lev : LocallyOfFinitePresentation (E.lev ≫ E.f) := E.lev_finitePresentation

variable {ℓ : ℕ} (C : E.ExtraLevel ℓ)

theorem qc_levK : QuasiCompact (C.levK ≫ E.f) := by haveI := C.levK_finite; infer_instance
theorem qs_levK : QuasiSeparated (C.levK ≫ E.f) := by haveI := C.levK_finite; infer_instance
theorem lfp_levK : LocallyOfFinitePresentation (C.levK ≫ E.f) := C.levK_finitePresentation

end insts
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18"

theorem val_comp_algebraMap {R L : Type} [CommRing R] [CommRing L] [Algebra R L] (T : Subalgebra R L) :
    T.val.toRingHom.comp (algebraMap R ↥T) = algebraMap R L := rfl

theorem inclusion_comp_algebraMap {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {T T' : Subalgebra R L}
    (h : T ≤ T') : (Subalgebra.inclusion h).toRingHom.comp (algebraMap R ↥T) = algebraMap R ↥T' := by
  ext r; rfl

theorem val_comp_inclusion {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {T T' : Subalgebra R L}
    (h : T ≤ T') : T'.val.toRingHom.comp (Subalgebra.inclusion h).toRingHom = T.val.toRingHom := by
  ext r; rfl

theorem le_of_fg_subset {R L : Type} [CommRing R] [CommRing L] [Algebra R L] {T T' : Subalgebra R L}
    {t : Finset L} (ht : Algebra.adjoin R (↑t : Set L) = T) (hsub : (↑t : Set L) ⊆ T') : T ≤ T' := by
  rw [← ht]; exact Algebra.adjoin_le hsub

theorem descend_data
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hc : c ≫ pullback.snd _ _ = pullback.snd _ _)
    (c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hc' : c' ≫ pullback.snd _ _ = pullback.snd _ _)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (eT : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (cT : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (cT' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))),
        eT.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ cT ≫ pullback.snd _ _ = pullback.snd _ _ ∧ cT' ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) u.1.f ≫ eT.hom =
          e.hom ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) w.1.f ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ≫ cT =
          c ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ≫ cT' =
          c' ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) := by
  classical
  haveI := qc_f u.1; haveI := qs_f u.1; haveI := lfp_f u.1; haveI := qc_f w.1; haveI := qs_f w.1; haveI := lfp_f w.1
  haveI := qc_lev u.1; haveI := qs_lev u.1; haveI := lfp_lev u.1; haveI := qc_lev w.1; haveI := qs_lev w.1; haveI := lfp_lev w.1

  obtain ⟨Ta, hTa, hsTa, ea, ea_snd, hea⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation u.1.f w.1.f e e_snd s
  obtain ⟨ta, hta⟩ := hTa

  obtain ⟨Tb, hTb, hsTb, cb, cb_snd, hcb⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (u.1.lev ≫ u.1.f) (w.1.lev ≫ w.1.f) c hc ta
  obtain ⟨tb, htb⟩ := hTb
  have hab : Ta ≤ Tb := le_of_fg_subset hta hsTb

  obtain ⟨T, hT, hsT, cT', cT'_snd, hcT'⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (w.1.lev ≫ w.1.f) (u.1.lev ≫ u.1.f) c' hc' tb
  have hbT : Tb ≤ T := le_of_fg_subset htb hsT
  have haT : Ta ≤ T := hab.trans hbT

  obtain ⟨eT, eT_snd, eT_fst, heT⟩ := restage_iso (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom
    (inclusion_comp_algebraMap haT) u.1.f w.1.f ea ea_snd
  obtain ⟨cT, cT_snd, cT_fst, hcT⟩ := restage_hom (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom
    (inclusion_comp_algebraMap hbT) (u.1.lev ≫ u.1.f) (w.1.lev ≫ w.1.f) cb cb_snd
  refine ⟨T, hT, (hsTa.trans (show (Ta : Set L) ⊆ T from haT)), eT, cT, cT', eT_snd, cT_snd, cT'_snd, ?_, ?_, ?_⟩
  ·
    have key := hea
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) u.1.f ≫
        trans (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom (inclusion_comp_algebraMap haT) u.1.f)
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) w.1.f ≫
        trans (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom (inclusion_comp_algebraMap haT) w.1.f)
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, eT_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, eT_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, e_snd]
  ·
    have key := hcb
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ≫
        trans (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom (inclusion_comp_algebraMap hbT) (u.1.lev ≫ u.1.f))
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ≫
        trans (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom (inclusion_comp_algebraMap hbT) (w.1.lev ≫ w.1.f))
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, cT_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, cT_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, hc]
  ·
    exact hcT' _ _ (trans_fst _ _ _ _ _) (trans_snd _ _ _ _ _) (trans_fst _ _ _ _ _) (trans_snd _ _ _ _ _)

theorem descend_dataK
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m ℓ : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hc : c ≫ pullback.snd _ _ = pullback.snd _ _)
    (c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hc' : c' ≫ pullback.snd _ _ = pullback.snd _ _)
    (k : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hk : k ≫ pullback.snd _ _ = pullback.snd _ _)
    (k' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (hk' : k' ≫ pullback.snd _ _ = pullback.snd _ _)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (eT : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (cT : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (cT' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (kT : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (kT' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))),
        eT.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧ cT ≫ pullback.snd _ _ = pullback.snd _ _ ∧ cT' ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        kT ≫ pullback.snd _ _ = pullback.snd _ _ ∧ kT' ≫ pullback.snd _ _ = pullback.snd _ _ ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) u.1.f ≫ eT.hom =
          e.hom ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) w.1.f ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ≫ cT =
          c ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ≫ cT' =
          c' ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cu.levK ≫ u.1.f) ≫ kT =
          k ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cw.levK ≫ w.1.f) ∧
        trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cw.levK ≫ w.1.f) ≫ kT' =
          k' ≫ trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cu.levK ≫ u.1.f) := by
  classical
  haveI := qc_f u.1; haveI := qs_f u.1; haveI := lfp_f u.1; haveI := qc_f w.1; haveI := qs_f w.1; haveI := lfp_f w.1
  haveI := qc_lev u.1; haveI := qs_lev u.1; haveI := lfp_lev u.1; haveI := qc_lev w.1; haveI := qs_lev w.1; haveI := lfp_lev w.1
  haveI := qc_levK u.1 Cu; haveI := qs_levK u.1 Cu; haveI := lfp_levK u.1 Cu
  haveI := qc_levK w.1 Cw; haveI := qs_levK w.1 Cw; haveI := lfp_levK w.1 Cw

  obtain ⟨Ta, hTa, hsTa, ea, ea_snd, hea⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation u.1.f w.1.f e e_snd s
  obtain ⟨ta, hta⟩ := hTa

  obtain ⟨Tb, hTb, hsTb, cb, cb_snd, hcb⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (u.1.lev ≫ u.1.f) (w.1.lev ≫ w.1.f) c hc ta
  obtain ⟨tb, htb⟩ := hTb
  have hab : Ta ≤ Tb := le_of_fg_subset hta hsTb

  obtain ⟨Tc, hTc, hsTc, cc, cc_snd, hcc⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (w.1.lev ≫ w.1.f) (u.1.lev ≫ u.1.f) c' hc' tb
  obtain ⟨tc, htc⟩ := hTc
  have hbc : Tb ≤ Tc := le_of_fg_subset htb hsTc

  obtain ⟨Td, hTd, hsTd, kd, kd_snd, hkd⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (Cu.levK ≫ u.1.f) (Cw.levK ≫ w.1.f) k hk tc
  obtain ⟨td, htd⟩ := hTd
  have hcd : Tc ≤ Td := le_of_fg_subset htc hsTd

  obtain ⟨T, hT, hsT, kT', kT'_snd, hkT'⟩ :=
    AlgebraicGeometry.exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation
      (Cw.levK ≫ w.1.f) (Cu.levK ≫ u.1.f) k' hk' td
  have hdT : Td ≤ T := le_of_fg_subset htd hsT
  have hcT : Tc ≤ T := hcd.trans hdT
  have hbT : Tb ≤ T := hbc.trans hcT
  have haT : Ta ≤ T := hab.trans hbT

  obtain ⟨eT, eT_snd, eT_fst, heT⟩ := restage_iso (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom
    (inclusion_comp_algebraMap haT) u.1.f w.1.f ea ea_snd
  obtain ⟨cT, cT_snd, cT_fst, hcT2⟩ := restage_hom (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom
    (inclusion_comp_algebraMap hbT) (u.1.lev ≫ u.1.f) (w.1.lev ≫ w.1.f) cb cb_snd
  obtain ⟨cT', cT'_snd, cT'_fst, hcT'2⟩ := restage_hom (algebraMap R ↥Tc) (algebraMap R ↥T) (Subalgebra.inclusion hcT).toRingHom
    (inclusion_comp_algebraMap hcT) (w.1.lev ≫ w.1.f) (u.1.lev ≫ u.1.f) cc cc_snd
  obtain ⟨kT, kT_snd, kT_fst, hkT2⟩ := restage_hom (algebraMap R ↥Td) (algebraMap R ↥T) (Subalgebra.inclusion hdT).toRingHom
    (inclusion_comp_algebraMap hdT) (Cu.levK ≫ u.1.f) (Cw.levK ≫ w.1.f) kd kd_snd
  refine ⟨T, hT, (hsTa.trans (show (Ta : Set L) ⊆ T from haT)), eT, cT, cT', kT, kT', eT_snd, cT_snd, cT'_snd, kT_snd, kT'_snd,
    ?_, ?_, ?_, ?_, ?_⟩
  ·
    have key := hea
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) u.1.f ≫
        trans (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom (inclusion_comp_algebraMap haT) u.1.f)
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) w.1.f ≫
        trans (algebraMap R ↥Ta) (algebraMap R ↥T) (Subalgebra.inclusion haT).toRingHom (inclusion_comp_algebraMap haT) w.1.f)
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, eT_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, eT_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, e_snd]
  ·
    have key := hcb
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ≫
        trans (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom (inclusion_comp_algebraMap hbT) (u.1.lev ≫ u.1.f))
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ≫
        trans (algebraMap R ↥Tb) (algebraMap R ↥T) (Subalgebra.inclusion hbT).toRingHom (inclusion_comp_algebraMap hbT) (w.1.lev ≫ w.1.f))
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, cT_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, cT_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, hc]
  ·
    have key := hcc
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (w.1.lev ≫ w.1.f) ≫
        trans (algebraMap R ↥Tc) (algebraMap R ↥T) (Subalgebra.inclusion hcT).toRingHom (inclusion_comp_algebraMap hcT) (w.1.lev ≫ w.1.f))
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (u.1.lev ≫ u.1.f) ≫
        trans (algebraMap R ↥Tc) (algebraMap R ↥T) (Subalgebra.inclusion hcT).toRingHom (inclusion_comp_algebraMap hcT) (u.1.lev ≫ u.1.f))
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, cT'_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, cT'_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, hc']
  ·
    have key := hkd
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cu.levK ≫ u.1.f) ≫
        trans (algebraMap R ↥Td) (algebraMap R ↥T) (Subalgebra.inclusion hdT).toRingHom (inclusion_comp_algebraMap hdT) (Cu.levK ≫ u.1.f))
      (trans (algebraMap R ↥T) (algebraMap R L) T.val.toRingHom (val_comp_algebraMap T) (Cw.levK ≫ w.1.f) ≫
        trans (algebraMap R ↥Td) (algebraMap R ↥T) (Subalgebra.inclusion hdT).toRingHom (inclusion_comp_algebraMap hdT) (Cw.levK ≫ w.1.f))
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
      (by rw [Category.assoc, trans_fst, trans_fst])
      (by rw [Category.assoc, trans_snd, ← Category.assoc, trans_snd, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            val_comp_inclusion])
    apply pullback.hom_ext
    · rw [Category.assoc, kT_fst, ← Category.assoc, ← Category.assoc, key, Category.assoc, Category.assoc, trans_fst, trans_fst,
        Category.assoc, trans_fst]
    · rw [Category.assoc, kT_snd, trans_snd, Category.assoc, trans_snd, ← Category.assoc, hk]
  ·
    exact hkT' _ _ (trans_fst _ _ _ _ _) (trans_snd _ _ _ _ _) (trans_fst _ _ _ _ _) (trans_snd _ _ _ _ _)

end PkgDesc17
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

noncomputable section

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace PkgDesc17

open PkgDesc18

variable {R : Type} [CommRing R] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem mul_coe_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of S)} (h : t₁ = t₂)
    (x y : SchemeHomOver t₁ f) :
    (L.mul t₁ x y).1 = (L.mul t₂ ⟨x.1, by rw [← h]; exact x.2⟩ ⟨y.1, by rw [← h]; exact y.2⟩).1 := by
  subst h; rfl

theorem mul_coe_congr_pts {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)}
    (x y x' y' : SchemeHomOver t f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t x' y').1 := by
  rw [Subtype.ext hx, Subtype.ext hy]

abbrev f2 (E : FakeEllipticCurve Λ N R) : pullback E.f E.f ⟶ Spec (CommRingCat.of R) := pullback.fst E.f E.f ≫ E.f

section univ
variable (E : FakeEllipticCurve Λ N R) (A : Type) [CommRing A] [Algebra R A]

def ptX : SchemeHomOver (pullback.snd (f2 E) (ι A)) (pullback.snd E.f (ι A)) :=
  ⟨pullback.lift (pullback.fst (f2 E) (ι A) ≫ pullback.fst E.f E.f) (pullback.snd (f2 E) (ι A))
      (by rw [Category.assoc]; exact pullback.condition),
    pullback.lift_snd _ _ _⟩

def ptY : SchemeHomOver (pullback.snd (f2 E) (ι A)) (pullback.snd E.f (ι A)) :=
  ⟨pullback.lift (pullback.fst (f2 E) (ι A) ≫ pullback.snd E.f E.f) (pullback.snd (f2 E) (ι A))
      (by rw [Category.assoc, ← pullback.condition (f := E.f) (g := E.f)]; exact pullback.condition),
    pullback.lift_snd _ _ _⟩

@[scoped simp] theorem ptX_coe_fst : (ptX E A).1 ≫ pullback.fst E.f (ι A) = pullback.fst (f2 E) (ι A) ≫ pullback.fst E.f E.f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem ptY_coe_fst : (ptY E A).1 ≫ pullback.fst E.f (ι A) = pullback.fst (f2 E) (ι A) ≫ pullback.snd E.f E.f :=
  pullback.lift_fst _ _ _
@[scoped simp] theorem ptX_coe_snd : (ptX E A).1 ≫ pullback.snd E.f (ι A) = pullback.snd (f2 E) (ι A) := pullback.lift_snd _ _ _
@[scoped simp] theorem ptY_coe_snd : (ptY E A).1 ≫ pullback.snd E.f (ι A) = pullback.snd (f2 E) (ι A) := pullback.lift_snd _ _ _

end univ
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

section defs
variable (u w : FakeEllipticCurve Λ N R) (A : Type) [CommRing A] [Algebra R A]
  (e : pullback u.f (ι A) ⟶ pullback w.f (ι A)) (e_snd : e ≫ pullback.snd w.f (ι A) = pullback.snd u.f (ι A))

def mulA : pullback (f2 u) (ι A) ⟶ pullback w.f (ι A) :=
  ((u.L.baseChange (ι A)).mul (pullback.snd (f2 u) (ι A)) (ptX u A) (ptY u A)).1 ≫ e

include e_snd in

def mulB : pullback (f2 u) (ι A) ⟶ pullback w.f (ι A) :=
  ((w.L.baseChange (ι A)).mul (pullback.snd (f2 u) (ι A))
    ⟨(ptX u A).1 ≫ e, by rw [Category.assoc, e_snd, (ptX u A).2]⟩
    ⟨(ptY u A).1 ≫ e, by rw [Category.assoc, e_snd, (ptY u A).2]⟩).1

def MulClause : Prop :=
  ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of A)) (x y : SchemeHomOver t (pullback.snd u.f (ι A))),
    ((u.L.baseChange (ι A)).mul t x y).1 ≫ e =
      ((w.L.baseChange (ι A)).mul t ⟨x.1 ≫ e, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e, by rw [Category.assoc, e_snd, y.2]⟩).1

theorem mulA_eq_mulB_of_mulClause (h : MulClause u w A e e_snd) : mulA u w A e = mulB u w A e e_snd := h _ _ _

theorem mulClause_of_mulA_eq_mulB (h : mulA u w A e = mulB u w A e e_snd) : MulClause u w A e e_snd := by
  intro T' t x y

  have hxy : (x.1 ≫ pullback.fst u.f (ι A)) ≫ u.f = (y.1 ≫ pullback.fst u.f (ι A)) ≫ u.f := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc, x.2, y.2]
  have hr : pullback.lift (x.1 ≫ pullback.fst u.f (ι A)) (y.1 ≫ pullback.fst u.f (ι A)) hxy ≫ f2 u = t ≫ ι A := by
    rw [f2, ← Category.assoc, pullback.lift_fst, Category.assoc, pullback.condition, ← Category.assoc, x.2]
  let r : T' ⟶ pullback (f2 u) (ι A) := pullback.lift _ _ hr
  have hrt : r ≫ pullback.snd (f2 u) (ι A) = t := pullback.lift_snd _ _ _
  have hrX : r ≫ (ptX u A).1 = x.1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, ptX_coe_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, ptX_coe_snd, hrt, x.2]
  have hrY : r ≫ (ptY u A).1 = y.1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, ptY_coe_fst, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    · rw [Category.assoc, ptY_coe_snd, hrt, y.2]

  have nu := congrArg Subtype.val ((u.L.baseChange (ι A)).mul_natural _ t r hrt (ptX u A) (ptY u A))
  have nw := congrArg Subtype.val ((w.L.baseChange (ι A)).mul_natural _ t r hrt
    ⟨(ptX u A).1 ≫ e, by rw [Category.assoc, e_snd, (ptX u A).2]⟩ ⟨(ptY u A).1 ≫ e, by rw [Category.assoc, e_snd, (ptY u A).2]⟩)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at nu nw
  have hL : ((u.L.baseChange (ι A)).mul t x y).1 = r ≫ ((u.L.baseChange (ι A)).mul _ (ptX u A) (ptY u A)).1 := by
    rw [nu]; exact mul_coe_congr_pts _ _ _ _ _ hrX.symm hrY.symm
  have hRt : ((w.L.baseChange (ι A)).mul t ⟨x.1 ≫ e, by rw [Category.assoc, e_snd, x.2]⟩
      ⟨y.1 ≫ e, by rw [Category.assoc, e_snd, y.2]⟩).1 = r ≫ mulB u w A e e_snd := by
    rw [mulB, nw]
    exact mul_coe_congr_pts _ _ _ _ _
      (by show x.1 ≫ e = r ≫ ((ptX u A).1 ≫ e); rw [← Category.assoc, hrX])
      (by show y.1 ≫ e = r ≫ ((ptY u A).1 ≫ e); rw [← Category.assoc, hrY])
  rw [hL, hRt, Category.assoc, ← h, mulA]

end defs
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

section transition
variable (u w : FakeEllipticCurve Λ N R) {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  (φ : A →ₐ[R] B)
  (eA : pullback u.f (ι A) ⟶ pullback w.f (ι A)) (eA_snd : eA ≫ pullback.snd w.f (ι A) = pullback.snd u.f (ι A))
  (eB : pullback u.f (ι B) ⟶ pullback w.f (ι B)) (eB_snd : eB ≫ pullback.snd w.f (ι B) = pullback.snd u.f (ι B))
  (hq : q u.f φ ≫ eA = eB ≫ q w.f φ)

theorem q_ptX : q (f2 u) φ ≫ (ptX u A).1 = (ptX u B).1 ≫ q u.f φ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptX_coe_fst, ← Category.assoc, q_fst, Category.assoc, q_fst, ptX_coe_fst]
  · rw [Category.assoc, ptX_coe_snd, q_snd, Category.assoc, q_snd, ← Category.assoc, ptX_coe_snd]

theorem q_ptY : q (f2 u) φ ≫ (ptY u A).1 = (ptY u B).1 ≫ q u.f φ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptY_coe_fst, ← Category.assoc, q_fst, Category.assoc, q_fst, ptY_coe_fst]
  · rw [Category.assoc, ptY_coe_snd, q_snd, Category.assoc, q_snd, ← Category.assoc, ptY_coe_snd]

theorem q_baseChange_mul (E : FakeEllipticCurve Λ N R)
    (XA YA : SchemeHomOver (pullback.snd (f2 u) (ι A)) (pullback.snd E.f (ι A)))
    (XB YB : SchemeHomOver (pullback.snd (f2 u) (ι B)) (pullback.snd E.f (ι B)))
    (hX : q (f2 u) φ ≫ XA.1 = XB.1 ≫ q E.f φ) (hY : q (f2 u) φ ≫ YA.1 = YB.1 ≫ q E.f φ) :
    q (f2 u) φ ≫ ((E.L.baseChange (ι A)).mul _ XA YA).1 = ((E.L.baseChange (ι B)).mul _ XB YB).1 ≫ q E.f φ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, q_fst, RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChange_mul,
      RelativeGroupLaw.baseChangePointOfBase_coe, RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst,
      pullback.lift_fst]
    have nat := congrArg Subtype.val (E.L.mul_natural (pullback.snd (f2 u) (ι A) ≫ ι A)
      (q (f2 u) φ ≫ pullback.snd (f2 u) (ι A) ≫ ι A) (q (f2 u) φ) rfl
      (RelativeGroupLaw.baseChangePointToBase (ι A) XA) (RelativeGroupLaw.baseChangePointToBase (ι A) YA))
    rw [GoodReductionJacobian.schemeHomOverComp_coe] at nat
    rw [nat, mul_coe_congr E.L (show q (f2 u) φ ≫ pullback.snd (f2 u) (ι A) ≫ ι A = pullback.snd (f2 u) (ι B) ≫ ι B by
      rw [← Category.assoc, q_snd, Category.assoc, specMap_comp_ι])]
    apply mul_coe_congr_pts
    · show q (f2 u) φ ≫ XA.1 ≫ pullback.fst E.f (ι A) = XB.1 ≫ pullback.fst E.f (ι B)
      rw [← Category.assoc, hX, Category.assoc, q_fst]
    · show q (f2 u) φ ≫ YA.1 ≫ pullback.fst E.f (ι A) = YB.1 ≫ pullback.fst E.f (ι B)
      rw [← Category.assoc, hY, Category.assoc, q_fst]
  · rw [Category.assoc, Category.assoc, q_snd, ((E.L.baseChange (ι A)).mul _ XA YA).2, q_snd, ← Category.assoc,
      ((E.L.baseChange (ι B)).mul _ XB YB).2]

include hq in

theorem q_mulA : q (f2 u) φ ≫ mulA u w A eA = mulA u w B eB ≫ q w.f φ := by
  rw [mulA, mulA, ← Category.assoc, q_baseChange_mul u φ u (ptX u A) (ptY u A) (ptX u B) (ptY u B) (q_ptX u φ) (q_ptY u φ),
    Category.assoc, hq, Category.assoc]

include hq eA_snd eB_snd in

theorem q_mulB : q (f2 u) φ ≫ mulB u w A eA eA_snd = mulB u w B eB eB_snd ≫ q w.f φ := by
  rw [mulB, mulB]
  exact q_baseChange_mul u φ w _ _ _ _
    (by rw [← Category.assoc, q_ptX, Category.assoc, Category.assoc, hq])
    (by rw [← Category.assoc, q_ptY, Category.assoc, Category.assoc, hq])

end transition
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

end PkgDesc17
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

namespace PkgDesc17

open PkgDesc18

section ActClosure

variable {R : Type} [CommRing R] {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem eq_one_of_mul_self {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem eq_inv_of_mul_eq_one {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x y : SchemeHomOver t f)
    (h : L.mul t x y = L.one t) : y = L.inv t x := by
  calc y = L.mul t (L.one t) y := (L.one_mul t y).symm
    _ = L.mul t (L.mul t (L.inv t x) x) y := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x y) := L.mul_assoc t _ _ _
    _ = L.mul t (L.inv t x) (L.one t) := by rw [h]
    _ = L.inv t x := L.mul_one t _

theorem pushPt_act_zero (E : FakeEllipticCurve Λ N R) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R))
    (Q : SchemeHomOver s E.f) : pushPt (E.act 0) (E.act_over 0) Q = E.L.one s := by
  apply eq_one_of_mul_self
  have h := E.act_add 0 0 s Q
  rw [add_zero] at h
  exact h.symm

theorem pushPt_act_neg (E : FakeEllipticCurve Λ N R) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R))
    (y : ↥Λ) (Q : SchemeHomOver s E.f) :
    pushPt (E.act (-y)) (E.act_over (-y)) Q = E.L.inv s (pushPt (E.act y) (E.act_over y) Q) := by
  apply eq_inv_of_mul_eq_one
  rw [← E.act_add y (-y) s Q]
  have : y + -y = 0 := add_neg_cancel y
  rw [this]
  exact pushPt_act_zero E s Q

variable {A : Type} [CommRing A] [Algebra R A] (u w : FakeEllipticCurve Λ N R)
  (e : pullback u.f (ι A) ⟶ pullback w.f (ι A)) (e_snd : e ≫ pullback.snd w.f (ι A) = pullback.snd u.f (ι A))

def mapE {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of A)} (P : SchemeHomOver t (pullback.snd u.f (ι A))) :
    SchemeHomOver t (pullback.snd w.f (ι A)) :=
  ⟨P.1 ≫ e, by rw [Category.assoc, e_snd, P.2]⟩

@[scoped simp] theorem mapE_coe {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of A)} (P : SchemeHomOver t (pullback.snd u.f (ι A))) :
    (mapE u w e e_snd P).1 = P.1 ≫ e := rfl

def Φ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (Q : SchemeHomOver (t ≫ ι A) u.f) : SchemeHomOver (t ≫ ι A) w.f :=
  RelativeGroupLaw.baseChangePointToBase (ι A) (mapE u w e e_snd (RelativeGroupLaw.baseChangePointOfBase (ι A) Q))

theorem Φ_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (Q : SchemeHomOver (t ≫ ι A) u.f) :
    (Φ u w e e_snd t Q).1 = (pullback.lift Q.1 t Q.2 ≫ e) ≫ pullback.fst w.f (ι A) := rfl

include e_snd in
theorem Φ_mul (e_mul : MulClause u w A e e_snd) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A))
    (Q Q' : SchemeHomOver (t ≫ ι A) u.f) :
    Φ u w e e_snd t (u.L.mul _ Q Q') = w.L.mul _ (Φ u w e e_snd t Q) (Φ u w e e_snd t Q') := by
  have h := e_mul t (RelativeGroupLaw.baseChangePointOfBase (ι A) Q) (RelativeGroupLaw.baseChangePointOfBase (ι A) Q')
  rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase]
    at h

  have h2 : mapE u w e e_snd (RelativeGroupLaw.baseChangePointOfBase (ι A) (u.L.mul _ Q Q')) =
      (w.L.baseChange (ι A)).mul t (mapE u w e e_snd (RelativeGroupLaw.baseChangePointOfBase (ι A) Q))
        (mapE u w e e_snd (RelativeGroupLaw.baseChangePointOfBase (ι A) Q')) := Subtype.ext h
  unfold Φ
  rw [h2, RelativeGroupLaw.baseChangePointToBase_mul]

include e_snd in
theorem Φ_one (e_mul : MulClause u w A e e_snd) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) :
    Φ u w e e_snd t (u.L.one _) = w.L.one _ := by
  apply eq_one_of_mul_self
  rw [← Φ_mul u w e e_snd e_mul, u.L.one_mul]

include e_snd in
theorem Φ_inv (e_mul : MulClause u w A e e_snd) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A))
    (Q : SchemeHomOver (t ≫ ι A) u.f) :
    Φ u w e e_snd t (u.L.inv _ Q) = w.L.inv _ (Φ u w e e_snd t Q) := by
  apply eq_inv_of_mul_eq_one
  rw [← Φ_mul u w e e_snd e_mul, RelativeGroupLaw.mul_inv_cancel, Φ_one u w e e_snd e_mul]

def ActCompat (y : ↥Λ) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of A)) (Q : SchemeHomOver (t ≫ ι A) u.f),
    Φ u w e e_snd t (pushPt (u.act y) (u.act_over y) Q) = pushPt (w.act y) (w.act_over y) (Φ u w e e_snd t Q)

include e_snd in
theorem actCompat_zero (e_mul : MulClause u w A e e_snd) : ActCompat u w e e_snd 0 := by
  intro T t Q
  rw [pushPt_act_zero, pushPt_act_zero, Φ_one u w e e_snd e_mul]

include e_snd in
theorem actCompat_add (e_mul : MulClause u w A e e_snd) (y z : ↥Λ) (hy : ActCompat u w e e_snd y) (hz : ActCompat u w e e_snd z) :
    ActCompat u w e e_snd (y + z) := by
  intro T t Q
  rw [u.act_add, w.act_add, Φ_mul u w e e_snd e_mul, hy, hz]

include e_snd in
theorem actCompat_neg (e_mul : MulClause u w A e e_snd) (y : ↥Λ) (hy : ActCompat u w e e_snd y) :
    ActCompat u w e e_snd (-y) := by
  intro T t Q
  rw [pushPt_act_neg, pushPt_act_neg, Φ_inv u w e e_snd e_mul, hy]

abbrev sAct' (E : FakeEllipticCurve Λ N R) (x : ↥Λ) : pullback E.f (ι A) ⟶ pullback E.f (ι A) :=
  pullback.lift (pullback.fst E.f (ι A) ≫ E.act x) (pullback.snd E.f (ι A)) (by rw [Category.assoc, E.act_over x, pullback.condition])

@[scoped simp] theorem sAct'_fst (E : FakeEllipticCurve Λ N R) (x : ↥Λ) :
    sAct' (A := A) E x ≫ pullback.fst E.f (ι A) = pullback.fst E.f (ι A) ≫ E.act x := pullback.lift_fst _ _ _
@[scoped simp] theorem sAct'_snd (E : FakeEllipticCurve Λ N R) (x : ↥Λ) :
    sAct' (A := A) E x ≫ pullback.snd E.f (ι A) = pullback.snd E.f (ι A) := pullback.lift_snd _ _ _

theorem actCompat_of_eq (y : ↥Λ) (h : sAct' (A := A) u y ≫ e = e ≫ sAct' (A := A) w y) : ActCompat u w e e_snd y := by
  intro T t Q
  apply Subtype.ext
  rw [Φ_coe]
  show (pullback.lift (Q.1 ≫ u.act y) t _ ≫ e) ≫ pullback.fst w.f (ι A) =
    ((pullback.lift Q.1 t Q.2 ≫ e) ≫ pullback.fst w.f (ι A)) ≫ w.act y
  have h1 : pullback.lift (Q.1 ≫ u.act y) t (by rw [Category.assoc, u.act_over y]; exact Q.2) =
      pullback.lift Q.1 t Q.2 ≫ sAct' (A := A) u y := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  rw [h1]
  simp only [Category.assoc]
  rw [reassoc_of% h, sAct'_fst]

include e_snd in

theorem eq_of_actCompat (y : ↥Λ) (h : ActCompat u w e e_snd y) : sAct' (A := A) u y ≫ e = e ≫ sAct' (A := A) w y := by
  let Q₀ : SchemeHomOver (pullback.snd u.f (ι A) ≫ ι A) u.f := ⟨pullback.fst u.f (ι A), pullback.condition⟩
  have hQ₀ : pullback.lift Q₀.1 (pullback.snd u.f (ι A)) Q₀.2 = 𝟙 _ :=
    pullback.hom_ext (by rw [pullback.lift_fst, Category.id_comp]) (by rw [pullback.lift_snd, Category.id_comp])
  have hQ₁ : pullback.lift ((pushPt (u.act y) (u.act_over y) Q₀).1) (pullback.snd u.f (ι A))
      (pushPt (u.act y) (u.act_over y) Q₀).2 = sAct' (A := A) u y :=
    pullback.hom_ext (by rw [pullback.lift_fst, pullback.lift_fst]; rfl) (by rw [pullback.lift_snd, pullback.lift_snd])
  have hc := congrArg Subtype.val (h _ (pullback.snd u.f (ι A)) Q₀)
  have hR : (pushPt (w.act y) (w.act_over y) (Φ u w e e_snd _ Q₀)).1 = (Φ u w e e_snd _ Q₀).1 ≫ w.act y := rfl
  rw [hR, Φ_coe, Φ_coe, hQ₀, hQ₁, Category.id_comp] at hc
  apply pullback.hom_ext
  · rw [hc]; simp only [Category.assoc, sAct'_fst]
  · rw [Category.assoc, e_snd, sAct'_snd, Category.assoc, sAct'_snd, e_snd]

include e_snd in

theorem act_closure (e_mul : MulClause u w A e e_snd) (G : Set ℍ[ℚ, a, b]) (hG : Submodule.span ℤ G = Λ)
    (hgen : ∀ (g : ℍ[ℚ, a, b]) (hgG : g ∈ G) (hg : g ∈ Λ), sAct' (A := A) u ⟨g, hg⟩ ≫ e = e ≫ sAct' (A := A) w ⟨g, hg⟩)
    (x : ↥Λ) : sAct' (A := A) u x ≫ e = e ≫ sAct' (A := A) w x := by
  apply eq_of_actCompat u w e e_snd
  have hx : (x : ℍ[ℚ, a, b]) ∈ Submodule.span ℤ G := by rw [hG]; exact x.2
  have key : ∀ (y : ℍ[ℚ, a, b]) (hy : y ∈ Submodule.span ℤ G), ∀ hy' : y ∈ Λ, ActCompat u w e e_snd ⟨y, hy'⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hyG => intro hy'; exact actCompat_of_eq u w e e_snd _ (hgen y hyG hy')
    | zero => intro hy'; exact actCompat_zero u w e e_snd e_mul
    | add y z hy hz ihy ihz =>
      intro hyz
      have hy' : y ∈ Λ := hG ▸ hy
      have hz' : z ∈ Λ := hG ▸ hz
      exact actCompat_add u w e e_snd e_mul ⟨y, hy'⟩ ⟨z, hz'⟩ (ihy hy') (ihz hz')
    | smul n y hy ihy =>
      intro hny
      have hy' : y ∈ Λ := hG ▸ hy
      have : (⟨n • y, hny⟩ : ↥Λ) = n • ⟨y, hy'⟩ := rfl
      rw [this]
      clear hny this
      induction n using Int.induction_on with
      | zero => rw [zero_smul]; exact actCompat_zero u w e e_snd e_mul
      | succ k ih => rw [add_smul, one_smul]; exact actCompat_add u w e e_snd e_mul _ _ ih (ihy hy')
      | pred k ih =>
        rw [sub_smul, one_smul, sub_eq_add_neg]
        exact actCompat_add u w e e_snd e_mul _ _ ih (actCompat_neg u w e e_snd e_mul _ (ihy hy'))
  exact key x.1 hx x.2

end ActClosure
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

end PkgDesc17
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

namespace PkgDesc18

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ} {R : Type} [CommRing R]

def sAct (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) (x : ↥Λ) :
    pullback u.1.f (ι A) ⟶ pullback u.1.f (ι A) :=
  pullback.lift (pullback.fst u.1.f (ι A) ≫ u.1.act x) (pullback.snd u.1.f (ι A))
    (by rw [Category.assoc, u.1.act_over x, pullback.condition])

def sLev (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    pullback (u.1.lev ≫ u.1.f) (ι A) ⟶ pullback u.1.f (ι A) :=
  pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (ι A) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (ι A))
    (by rw [Category.assoc]; exact pullback.condition)

def sP (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    Spec (CommRingCat.of A) ⟶ pullback u.1.f (ι A) :=
  pullback.lift (ι A ≫ (u.2.P).1) (𝟙 _) (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp])

theorem sAct_snd (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) (x : ↥Λ) :
    sAct A u x ≫ pullback.snd u.1.f (ι A) = pullback.snd u.1.f (ι A) := pullback.lift_snd _ _ _

theorem sLev_snd (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    sLev A u ≫ pullback.snd u.1.f (ι A) = pullback.snd (u.1.lev ≫ u.1.f) (ι A) := pullback.lift_snd _ _ _

theorem q_sAct {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (x : ↥Λ) :
    sAct B u x ≫ q u.1.f φ = q u.1.f φ ≫ sAct A u x := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, Category.assoc]
    simp only [sAct, pullback.lift_fst]
    rw [← Category.assoc, q_fst]
  · simp only [Category.assoc, q_snd, sAct, pullback.lift_snd, pullback.lift_snd_assoc]

theorem q_sLev {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    sLev B u ≫ q u.1.f φ = q (u.1.lev ≫ u.1.f) φ ≫ sLev A u := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, Category.assoc]
    simp only [sLev, pullback.lift_fst]
    rw [← Category.assoc, q_fst]
  · simp only [Category.assoc, q_snd, sLev, pullback.lift_snd, pullback.lift_snd_assoc]

theorem restage_sAct {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) (x : ↥Λ) :
    restage u.1.f u.1.f φ (sAct A u x) (sAct_snd A u x) = sAct B u x :=
  (eq_restage _ _ φ _ _ _ (sAct_snd B u x) (q_sAct φ u x)).symm

theorem restage_sLev {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    restage (u.1.lev ≫ u.1.f) u.1.f φ (sLev A u) (sLev_snd A u) = sLev B u :=
  (eq_restage _ _ φ _ _ _ (sLev_snd B u) (q_sLev φ u)).symm

def sLevK (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) {ℓ : ℕ} (C : u.1.ExtraLevel ℓ) :
    pullback (C.levK ≫ u.1.f) (ι A) ⟶ pullback u.1.f (ι A) :=
  pullback.lift (pullback.fst (C.levK ≫ u.1.f) (ι A) ≫ C.levK) (pullback.snd (C.levK ≫ u.1.f) (ι A))
    (by rw [Category.assoc]; exact pullback.condition)

theorem sLevK_snd (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) {ℓ : ℕ} (C : u.1.ExtraLevel ℓ) :
    sLevK A u C ≫ pullback.snd u.1.f (ι A) = pullback.snd (C.levK ≫ u.1.f) (ι A) := pullback.lift_snd _ _ _

theorem q_sLevK {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) {ℓ : ℕ} (C : u.1.ExtraLevel ℓ) :
    sLevK B u C ≫ q u.1.f φ = q (C.levK ≫ u.1.f) φ ≫ sLevK A u C := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst, Category.assoc]
    simp only [sLevK, pullback.lift_fst]
    rw [← Category.assoc, q_fst]
  · simp only [Category.assoc, q_snd, sLevK, pullback.lift_snd, pullback.lift_snd_assoc]

theorem restage_sLevK {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) {ℓ : ℕ} (C : u.1.ExtraLevel ℓ) :
    restage (C.levK ≫ u.1.f) u.1.f φ (sLevK A u C) (sLevK_snd A u C) = sLevK B u C :=
  (eq_restage _ _ φ _ _ _ (sLevK_snd B u C) (q_sLevK φ u C)).symm

theorem fg_finset_sup {L : Type} [CommRing L] [Algebra R L] {ι' : Type} (G : Finset ι') (T : ι' → Subalgebra R L)
    (h : ∀ i ∈ G, (T i).FG) : (G.sup T).FG := by
  classical
  induction G using Finset.induction_on with
  | empty => simpa using Subalgebra.fg_bot
  | insert i G hi ih =>
    rw [Finset.sup_insert]
    exact (h i (Finset.mem_insert_self i G)).sup (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def sPP (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    pullback (𝟙 (Spec (CommRingCat.of R))) (ι A) ⟶ pullback u.1.f (ι A) :=
  pullback.snd _ _ ≫ sP A u

theorem sP_snd (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    sP A u ≫ pullback.snd u.1.f (ι A) = 𝟙 _ := pullback.lift_snd _ _ _

theorem sPP_snd (A : Type) [CommRing A] [Algebra R A] (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    sPP A u ≫ pullback.snd u.1.f (ι A) = pullback.snd _ _ := by
  rw [sPP, Category.assoc, sP_snd, Category.comp_id]

theorem q_sPP {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    sPP B u ≫ q u.1.f φ = q (𝟙 _) φ ≫ sPP A u := by
  apply pullback.hom_ext
  · rw [Category.assoc, q_fst]
    simp only [sPP, sP, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc (q _ φ), q_snd, Category.assoc, ← Category.assoc (Spec.map _), specMap_comp_ι]
  · rw [Category.assoc, q_snd, ← Category.assoc, sPP_snd, Category.assoc, sPP_snd, q_snd]

theorem restage_sPP {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)
    (u : FakeEllipticCurve.WithFullLevel Λ N m R) :
    restage (𝟙 _) u.1.f φ (sPP A u) (sPP_snd A u) = sPP B u :=
  (eq_restage _ _ φ _ _ _ (sPP_snd B u) (q_sPP φ u)).symm

end PkgDesc18
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc18 P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage.PkgDesc17"

open PkgDesc18 PkgDesc17 in

theorem PkgDesc18.mul_descends
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R)
    (e : pullback u.1.f (ι L) ≅ pullback w.1.f (ι L))
    (e_snd : e.hom ≫ pullback.snd w.1.f (ι L) = pullback.snd u.1.f (ι L))
    (e_mul : PkgDesc17.MulClause u.1 w.1 L e.hom e_snd)
    (T₁ : Subalgebra R L) (hT₁fg : T₁.FG)
    (e₁ : pullback u.1.f (ι ↥T₁) ≅ pullback w.1.f (ι ↥T₁))
    (e₁_snd : e₁.hom ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd u.1.f (ι ↥T₁))
    (hqe : q u.1.f T₁.val ≫ e₁.hom = e.hom ≫ q w.1.f T₁.val)
    (mulA_snd : PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁))
    (mulB_snd : PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁)) :
    ∃ (Tm : Subalgebra R L) (h1m : T₁ ≤ Tm), Tm.FG ∧
      restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1m) (PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom) mulA_snd =
      restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1m) (PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd) mulB_snd := by
  haveI := PkgDesc17.qc_f w.1; haveI := PkgDesc17.lfp_f w.1
  haveI : QuasiCompact (PkgDesc17.f2 u.1) := by
    haveI := u.1.bundle.proper
    show QuasiCompact (pullback.fst u.1.f u.1.f ≫ u.1.f)
    infer_instance
  obtain ⟨Tm, h1m, hTmfg, -, hmul⟩ := exists_fg_restage_eq (PkgDesc17.f2 u.1) w.1.f T₁ hT₁fg
    (PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom) (PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd) mulA_snd mulB_snd
    (by
      rw [PkgDesc17.q_mulA u.1 w.1 T₁.val e₁.hom e.hom hqe, PkgDesc17.q_mulB u.1 w.1 T₁.val e₁.hom e₁_snd e.hom e_snd hqe,
        PkgDesc17.mulA_eq_mulB_of_mulClause u.1 w.1 L e.hom e_snd e_mul]) ∅
  exact ⟨Tm, h1m, hTmfg, hmul⟩

open PkgDesc18 PkgDesc17 in

theorem PkgDesc18.mulClause_at
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N m : ℕ}
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R)
    (T₁ T : Subalgebra R L) (h1T : T₁ ≤ T)
    (e₁ : pullback u.1.f (ι ↥T₁) ≅ pullback w.1.f (ι ↥T₁))
    (e₁_snd : e₁.hom ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd u.1.f (ι ↥T₁))
    (mulA_snd : PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁))
    (mulB_snd : PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁))
    (h : restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1T) (PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom) mulA_snd =
      restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1T) (PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd) mulB_snd)
    (eT : pullback u.1.f (ι ↥T) ⟶ pullback w.1.f (ι ↥T)) (heT : eT = restage u.1.f w.1.f (Subalgebra.inclusion h1T) e₁.hom e₁_snd)
    (eT_snd : eT ≫ pullback.snd w.1.f (ι ↥T) = pullback.snd u.1.f (ι ↥T)) :
    PkgDesc17.MulClause u.1 w.1 ↥T eT eT_snd := by
  apply PkgDesc17.mulClause_of_mulA_eq_mulB
  have hq : q u.1.f (Subalgebra.inclusion h1T) ≫ e₁.hom = eT ≫ q w.1.f (Subalgebra.inclusion h1T) := by
    rw [heT]; exact (restage_q u.1.f w.1.f (Subalgebra.inclusion h1T) e₁.hom e₁_snd).symm
  have hA : restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1T) (PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom) mulA_snd =
      PkgDesc17.mulA u.1 w.1 ↥T eT :=
    (eq_restage _ _ _ _ _ _ (by rw [PkgDesc17.mulA, Category.assoc, eT_snd]; exact ((u.1.L.baseChange _).mul _ _ _).2)
      (PkgDesc17.q_mulA u.1 w.1 (Subalgebra.inclusion h1T) e₁.hom eT hq).symm).symm
  have hB : restage (PkgDesc17.f2 u.1) w.1.f (Subalgebra.inclusion h1T) (PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd) mulB_snd =
      PkgDesc17.mulB u.1 w.1 ↥T eT eT_snd :=
    (eq_restage _ _ _ _ _ _ ((w.1.L.baseChange _).mul _ _ _).2
      (PkgDesc17.q_mulB u.1 w.1 (Subalgebra.inclusion h1T) e₁.hom e₁_snd eT eT_snd hq).symm).symm
  rw [hA, hB] at h
  exact h

set_option maxHeartbeats 1600000 in
open PkgDesc18 PkgDesc17 in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsMaximalOrder Λ) {N m ℓ : ℕ}
    {R : Type} [CommRing R] [IsNoetherianRing R] {L : Type} [CommRing L] [Algebra R L]
    (u w : FakeEllipticCurve.WithFullLevel Λ N m R) (Cu : u.1.ExtraLevel ℓ) (Cw : w.1.ExtraLevel ℓ)
    (e : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_snd : e.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
    (e_mul : ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of L)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))),
      ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t x y).1 ≫ e.hom =
        ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R L)))).mul t
          ⟨x.1 ≫ e.hom, by rw [Category.assoc, e_snd, x.2]⟩ ⟨y.1 ≫ e.hom, by rw [Category.assoc, e_snd, y.2]⟩).1)
    (e_act : ∀ x : ↥Λ,
      pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ e.hom =
        e.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R L))))
          (by rw [Category.assoc, w.1.act_over x, pullback.condition]))
    (e_P : pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (u.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ e.hom =
        pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ (w.2.P).1) (𝟙 _)
          (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp]))
    (e_lev : ∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_lev' : ∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
        c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) =
          pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
            (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)
    (e_levK : ∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.hom)
    (e_levK' : ∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))),
          cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) =
            pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R L))))
              (by rw [Category.assoc]; exact pullback.condition) ≫ e.inv)
    (s : Finset L) :
    ∃ (T : Subalgebra R L), T.FG ∧ (↑s : Set L) ⊆ T ∧
      ∃ (eT : pullback u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≅ pullback w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
        (eT_snd : eT.hom ≫ pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) = pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))),
        (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of ↥T)) (x y : SchemeHomOver t (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))),
          ((u.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t x y).1 ≫ eT.hom =
            ((w.1.L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap R ↥T)))).mul t
              ⟨x.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, x.2]⟩ ⟨y.1 ≫ eT.hom, by rw [Category.assoc, eT_snd, y.2]⟩).1) ∧
        (∀ x : ↥Λ,
          pullback.lift (pullback.fst u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.act x) (pullback.snd u.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, u.1.act_over x, pullback.condition]) ≫ eT.hom =
            eT.hom ≫ pullback.lift (pullback.fst w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.act x) (pullback.snd w.1.f (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
              (by rw [Category.assoc, w.1.act_over x, pullback.condition])) ∧
        (pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (u.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (u.2.P).2, Category.comp_id, Category.id_comp]) ≫ eT.hom =
            pullback.lift ((Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ (w.2.P).1) (𝟙 _)
              (by rw [Category.assoc, (w.2.P).2, Category.comp_id, Category.id_comp])) ∧
        (∃ c : pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c ≫ pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.hom) ∧
        (∃ c' : pullback (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            c' ≫ pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ u.1.lev) (pullback.snd (u.1.lev ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ w.1.lev) (pullback.snd (w.1.lev ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.inv) ∧
        (∃ cK : pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            cK ≫ pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.hom) ∧
        (∃ cK' : pullback (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ⟶ pullback (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))),
            cK' ≫ pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cu.levK) (pullback.snd (Cu.levK ≫ u.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) =
              pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))) ≫ Cw.levK) (pullback.snd (Cw.levK ≫ w.1.f) (Spec.map (CommRingCat.ofHom (algebraMap R ↥T))))
                (by rw [Category.assoc]; exact pullback.condition) ≫ eT.inv) := by
  classical
  haveI := PkgDesc17.qc_f u.1; haveI := PkgDesc17.qs_f u.1; haveI := PkgDesc17.lfp_f u.1
  haveI := PkgDesc17.qc_f w.1; haveI := PkgDesc17.qs_f w.1; haveI := PkgDesc17.lfp_f w.1
  haveI := PkgDesc17.qc_lev u.1; haveI := PkgDesc17.lfp_lev u.1; haveI := PkgDesc17.qc_lev w.1; haveI := PkgDesc17.lfp_lev w.1
  haveI := PkgDesc17.qc_levK u.1 Cu; haveI := PkgDesc17.lfp_levK u.1 Cu; haveI := PkgDesc17.qc_levK w.1 Cw; haveI := PkgDesc17.lfp_levK w.1 Cw

  obtain ⟨c, hc⟩ := e_lev
  obtain ⟨c', hc'⟩ := e_lev'
  obtain ⟨k, hk⟩ := e_levK
  obtain ⟨k', hk'⟩ := e_levK'
  have e_inv_snd : e.inv ≫ pullback.snd u.1.f (ι L) = pullback.snd w.1.f (ι L) := by
    rw [← e_snd, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hc_snd : c ≫ pullback.snd (w.1.lev ≫ w.1.f) (ι L) = pullback.snd (u.1.lev ≫ u.1.f) (ι L) := by
    have := congrArg (· ≫ pullback.snd w.1.f (ι L)) hc
    simpa only [Category.assoc, sLev_snd, e_snd, show pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (ι L) ≫ w.1.lev)
      (pullback.snd (w.1.lev ≫ w.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLev L w from rfl,
      show pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (ι L) ≫ u.1.lev)
      (pullback.snd (u.1.lev ≫ u.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLev L u from rfl] using this
  have hc'_snd : c' ≫ pullback.snd (u.1.lev ≫ u.1.f) (ι L) = pullback.snd (w.1.lev ≫ w.1.f) (ι L) := by
    have := congrArg (· ≫ pullback.snd u.1.f (ι L)) hc'
    simpa only [Category.assoc, sLev_snd, e_inv_snd, show pullback.lift (pullback.fst (w.1.lev ≫ w.1.f) (ι L) ≫ w.1.lev)
      (pullback.snd (w.1.lev ≫ w.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLev L w from rfl,
      show pullback.lift (pullback.fst (u.1.lev ≫ u.1.f) (ι L) ≫ u.1.lev)
      (pullback.snd (u.1.lev ≫ u.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLev L u from rfl] using this
  have hk_snd : k ≫ pullback.snd (Cw.levK ≫ w.1.f) (ι L) = pullback.snd (Cu.levK ≫ u.1.f) (ι L) := by
    have := congrArg (· ≫ pullback.snd w.1.f (ι L)) hk
    simpa only [Category.assoc, sLevK_snd, e_snd, show pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (ι L) ≫ Cw.levK)
      (pullback.snd (Cw.levK ≫ w.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLevK L w Cw from rfl,
      show pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (ι L) ≫ Cu.levK)
      (pullback.snd (Cu.levK ≫ u.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLevK L u Cu from rfl] using this
  have hk'_snd : k' ≫ pullback.snd (Cu.levK ≫ u.1.f) (ι L) = pullback.snd (Cw.levK ≫ w.1.f) (ι L) := by
    have := congrArg (· ≫ pullback.snd u.1.f (ι L)) hk'
    simpa only [Category.assoc, sLevK_snd, e_inv_snd, show pullback.lift (pullback.fst (Cw.levK ≫ w.1.f) (ι L) ≫ Cw.levK)
      (pullback.snd (Cw.levK ≫ w.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLevK L w Cw from rfl,
      show pullback.lift (pullback.fst (Cu.levK ≫ u.1.f) (ι L) ≫ Cu.levK)
      (pullback.snd (Cu.levK ≫ u.1.f) (ι L)) (by rw [Category.assoc]; exact pullback.condition) = sLevK L u Cu from rfl] using this

  obtain ⟨T₁, hT₁fg, hsT₁, e₁, c₁, c₁', k₁, k₁', e₁_snd, c₁_snd, c₁'_snd, k₁_snd, k₁'_snd, he₁, hc₁, hc₁', hk₁, hk₁'⟩ :=
    PkgDesc17.descend_dataK u w Cu Cw e e_snd c hc_snd c' hc'_snd k hk_snd k' hk'_snd s

  have hqe : q u.1.f T₁.val ≫ e₁.hom = e.hom ≫ q w.1.f T₁.val := he₁
  have hqc : q (u.1.lev ≫ u.1.f) T₁.val ≫ c₁ = c ≫ q (w.1.lev ≫ w.1.f) T₁.val := hc₁
  have hqc' : q (w.1.lev ≫ w.1.f) T₁.val ≫ c₁' = c' ≫ q (u.1.lev ≫ u.1.f) T₁.val := hc₁'
  have hqk : q (Cu.levK ≫ u.1.f) T₁.val ≫ k₁ = k ≫ q (Cw.levK ≫ w.1.f) T₁.val := hk₁
  have hqk' : q (Cw.levK ≫ w.1.f) T₁.val ≫ k₁' = k' ≫ q (Cu.levK ≫ u.1.f) T₁.val := hk₁'
  have e₁_inv_snd : e₁.inv ≫ pullback.snd u.1.f (ι ↥T₁) = pullback.snd w.1.f (ι ↥T₁) := by
    rw [← e₁_snd, ← Category.assoc, e₁.inv_hom_id, Category.id_comp]
  have hqe' : q w.1.f T₁.val ≫ e₁.inv = e.inv ≫ q u.1.f T₁.val := by
    rw [← cancel_mono e₁.hom, Category.assoc, e₁.inv_hom_id, Category.comp_id, Category.assoc, hqe,
      ← Category.assoc, e.inv_hom_id, Category.id_comp]

  obtain ⟨Tl, h1l, hTlfg, -, hl⟩ := exists_fg_restage_eq (u.1.lev ≫ u.1.f) w.1.f T₁ hT₁fg
    (c₁ ≫ sLev ↥T₁ w) (sLev ↥T₁ u ≫ e₁.hom)
    (by rw [Category.assoc, sLev_snd, c₁_snd]) (by rw [Category.assoc, e₁_snd, sLev_snd])
    (by
      rw [← Category.assoc, hqc, Category.assoc, ← q_sLev, ← Category.assoc, ← Category.assoc, ← q_sLev,
        Category.assoc, Category.assoc, hqe]
      exact congrArg (· ≫ q w.1.f T₁.val) hc) ∅
  obtain ⟨Tl', h1l', hTl'fg, -, hl'⟩ := exists_fg_restage_eq (w.1.lev ≫ w.1.f) u.1.f T₁ hT₁fg
    (c₁' ≫ sLev ↥T₁ u) (sLev ↥T₁ w ≫ e₁.inv)
    (by rw [Category.assoc, sLev_snd, c₁'_snd]) (by rw [Category.assoc, e₁_inv_snd, sLev_snd])
    (by
      rw [← Category.assoc, hqc', Category.assoc, ← q_sLev, ← Category.assoc, ← Category.assoc, ← q_sLev,
        Category.assoc, Category.assoc, hqe']
      exact congrArg (· ≫ q u.1.f T₁.val) hc') ∅

  obtain ⟨Tk, h1k, hTkfg, -, hkk⟩ := exists_fg_restage_eq (Cu.levK ≫ u.1.f) w.1.f T₁ hT₁fg
    (k₁ ≫ sLevK ↥T₁ w Cw) (sLevK ↥T₁ u Cu ≫ e₁.hom)
    (by rw [Category.assoc, sLevK_snd, k₁_snd]) (by rw [Category.assoc, e₁_snd, sLevK_snd])
    (by
      rw [← Category.assoc, hqk, Category.assoc, ← q_sLevK, ← Category.assoc, ← Category.assoc, ← q_sLevK,
        Category.assoc, Category.assoc, hqe]
      exact congrArg (· ≫ q w.1.f T₁.val) hk) ∅
  obtain ⟨Tk', h1k', hTk'fg, -, hkk'⟩ := exists_fg_restage_eq (Cw.levK ≫ w.1.f) u.1.f T₁ hT₁fg
    (k₁' ≫ sLevK ↥T₁ u Cu) (sLevK ↥T₁ w Cw ≫ e₁.inv)
    (by rw [Category.assoc, sLevK_snd, k₁'_snd]) (by rw [Category.assoc, e₁_inv_snd, sLevK_snd])
    (by
      rw [← Category.assoc, hqk', Category.assoc, ← q_sLevK, ← Category.assoc, ← Category.assoc, ← q_sLevK,
        Category.assoc, Category.assoc, hqe']
      exact congrArg (· ≫ q u.1.f T₁.val) hk') ∅

  haveI : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (ι L)) := inferInstance
  obtain ⟨Tp, h1p, hTpfg, -, hp⟩ := exists_fg_restage_eq (𝟙 _) w.1.f T₁ hT₁fg
    (sPP ↥T₁ u ≫ e₁.hom) (sPP ↥T₁ w)
    (by rw [Category.assoc, e₁_snd, sPP_snd]) (sPP_snd _ _)
    (by
      rw [← Category.assoc, ← q_sPP, Category.assoc, hqe, ← q_sPP, ← Category.assoc]
      congr 1
      rw [sPP, sPP, Category.assoc]
      exact congrArg (pullback.snd _ _ ≫ ·) e_P) ∅

  have hsAct : ∀ (A : Type) [CommRing A] [Algebra R A] (v : FakeEllipticCurve.WithFullLevel Λ N m R) (x : ↥Λ),
      pullback.lift (pullback.fst v.1.f (Spec.map (CommRingCat.ofHom (algebraMap R A))) ≫ v.1.act x)
        (pullback.snd v.1.f (Spec.map (CommRingCat.ofHom (algebraMap R A))))
        (by rw [Category.assoc, v.1.act_over x, pullback.condition]) = sAct A v x := fun _ _ _ _ _ => rfl
  have Hact : ∀ x : ↥Λ, ∃ (T₂ : Subalgebra R L) (h₁₂ : T₁ ≤ T₂), T₂.FG ∧
      restage u.1.f w.1.f (Subalgebra.inclusion h₁₂) (sAct ↥T₁ u x ≫ e₁.hom) (by rw [Category.assoc, e₁_snd, sAct_snd]) =
      restage u.1.f w.1.f (Subalgebra.inclusion h₁₂) (e₁.hom ≫ sAct ↥T₁ w x) (by rw [Category.assoc, sAct_snd, e₁_snd]) := by
    intro x
    obtain ⟨T₂, h₁₂, hfg, -, h⟩ := exists_fg_restage_eq u.1.f w.1.f T₁ hT₁fg
      (sAct ↥T₁ u x ≫ e₁.hom) (e₁.hom ≫ sAct ↥T₁ w x)
      (by rw [Category.assoc, e₁_snd, sAct_snd]) (by rw [Category.assoc, sAct_snd, e₁_snd])
      (by
        rw [← Category.assoc, ← q_sAct, Category.assoc, hqe, ← Category.assoc, ← hsAct L u x, e_act x, hsAct L w x,
          Category.assoc, q_sAct, ← Category.assoc, ← hqe, Category.assoc]) ∅
    exact ⟨T₂, h₁₂, hfg, h⟩
  choose Tx h1x hTxfg hx using Hact

  obtain ⟨G, hG⟩ := hΛ.isOrder.fg
  have hGΛ : ∀ g ∈ G, g ∈ Λ := fun g hg => hG ▸ Submodule.subset_span hg
  let GΛ : Finset ↥Λ := G.attach.image (fun g => ⟨g.1, hGΛ g.1 g.2⟩)

  have mulA_snd : PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁) := by
    rw [PkgDesc17.mulA, Category.assoc, e₁_snd]; exact ((u.1.L.baseChange _).mul _ _ _).2
  have mulB_snd : PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd ≫ pullback.snd w.1.f (ι ↥T₁) = pullback.snd (PkgDesc17.f2 u.1) (ι ↥T₁) :=
    ((w.1.L.baseChange _).mul _ _ _).2
  obtain ⟨Tm, h1m, hTmfg, hmul⟩ := PkgDesc18.mul_descends u w e e_snd e_mul T₁ hT₁fg e₁ e₁_snd hqe mulA_snd mulB_snd

  obtain ⟨T, h1T, hlT, hl'T, hpT, hxT, hmT, hkT, hk'T, hTfg, hsT⟩ : ∃ T : Subalgebra R L, T₁ ≤ T ∧ Tl ≤ T ∧ Tl' ≤ T ∧ Tp ≤ T ∧
      (∀ x ∈ GΛ, Tx x ≤ T) ∧ Tm ≤ T ∧ Tk ≤ T ∧ Tk' ≤ T ∧ T.FG ∧ (↑s : Set L) ⊆ T := by
    have h0 : Tl ⊔ Tl' ⊔ Tp ⊔ GΛ.sup Tx ⊔ Tm ≤ Tl ⊔ Tl' ⊔ Tp ⊔ GΛ.sup Tx ⊔ Tm ⊔ Tk ⊔ Tk' := le_sup_left.trans le_sup_left
    refine ⟨Tl ⊔ Tl' ⊔ Tp ⊔ GΛ.sup Tx ⊔ Tm ⊔ Tk ⊔ Tk', ?_, ?_, ?_, ?_, ?_, le_sup_right.trans h0, le_sup_right.trans le_sup_left,
      le_sup_right, ?_, ?_⟩
    · exact (h1l.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))).trans h0
    · exact (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans h0
    · exact (le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left))).trans h0
    · exact (le_sup_right.trans (le_sup_left.trans le_sup_left)).trans h0
    · exact fun x hx' => ((Finset.le_sup hx').trans (le_sup_right.trans le_sup_left)).trans h0
    · exact (((((hTlfg.sup hTl'fg).sup hTpfg).sup (fg_finset_sup GΛ Tx (fun x _ => hTxfg x))).sup hTmfg).sup hTkfg).sup hTk'fg
    · exact hsT₁.trans ((h1l.trans (le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)))).trans h0)

  have hincl : ∀ (T₂ : Subalgebra R L) (h₁₂ : T₁ ≤ T₂) (h₂ : T₂ ≤ T),
      (Subalgebra.inclusion h₂).comp (Subalgebra.inclusion h₁₂) = Subalgebra.inclusion h1T := fun _ _ _ => by ext; rfl
  have two_step : ∀ {X Y : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
      (T₂ : Subalgebra R L) (h₁₂ : T₁ ≤ T₂) (h₂ : T₂ ≤ T)
      (a₁ b₁ : pullback f (ι ↥T₁) ⟶ pullback g (ι ↥T₁)) (ha₁ : a₁ ≫ pullback.snd g _ = pullback.snd f _)
      (hb₁ : b₁ ≫ pullback.snd g _ = pullback.snd f _),
      restage f g (Subalgebra.inclusion h₁₂) a₁ ha₁ = restage f g (Subalgebra.inclusion h₁₂) b₁ hb₁ →
      restage f g (Subalgebra.inclusion h1T) a₁ ha₁ = restage f g (Subalgebra.inclusion h1T) b₁ hb₁ := by
    intro X Y f g T₂ h₁₂ h₂ a₁ b₁ ha₁ hb₁ h
    have e1 := restage_restage f g (Subalgebra.inclusion h₁₂) (Subalgebra.inclusion h₂) a₁ ha₁
    have e2 := restage_restage f g (Subalgebra.inclusion h₁₂) (Subalgebra.inclusion h₂) b₁ hb₁
    rw [hincl T₂ h₁₂ h₂] at e1 e2
    rw [← e1, ← e2]
    congr 1

  let eT : pullback u.1.f (ι ↥T) ≅ pullback w.1.f (ι ↥T) :=
    { hom := restage u.1.f w.1.f (Subalgebra.inclusion h1T) e₁.hom e₁_snd
      inv := restage w.1.f u.1.f (Subalgebra.inclusion h1T) e₁.inv e₁_inv_snd
      hom_inv_id := (restage_comp u.1.f w.1.f u.1.f (Subalgebra.inclusion h1T) e₁.hom e₁_snd e₁.inv e₁_inv_snd).symm.trans
        ((restage_congr u.1.f u.1.f (Subalgebra.inclusion h1T) e₁.hom_inv_id _ (Category.id_comp _)).trans
          (restage_id u.1.f (Subalgebra.inclusion h1T)))
      inv_hom_id := (restage_comp w.1.f u.1.f w.1.f (Subalgebra.inclusion h1T) e₁.inv e₁_inv_snd e₁.hom e₁_snd).symm.trans
        ((restage_congr w.1.f w.1.f (Subalgebra.inclusion h1T) e₁.inv_hom_id _ (Category.id_comp _)).trans
          (restage_id w.1.f (Subalgebra.inclusion h1T))) }
  have eT_snd : eT.hom ≫ pullback.snd w.1.f (ι ↥T) = pullback.snd u.1.f (ι ↥T) :=
    restage_snd u.1.f w.1.f (Subalgebra.inclusion h1T) e₁.hom e₁_snd
  let cT := restage (u.1.lev ≫ u.1.f) (w.1.lev ≫ w.1.f) (Subalgebra.inclusion h1T) c₁ c₁_snd
  let cT' := restage (w.1.lev ≫ w.1.f) (u.1.lev ≫ u.1.f) (Subalgebra.inclusion h1T) c₁' c₁'_snd
  let kT := restage (Cu.levK ≫ u.1.f) (Cw.levK ≫ w.1.f) (Subalgebra.inclusion h1T) k₁ k₁_snd
  let kT' := restage (Cw.levK ≫ w.1.f) (Cu.levK ≫ u.1.f) (Subalgebra.inclusion h1T) k₁' k₁'_snd

  have HlevT : cT ≫ sLev ↥T w = sLev ↥T u ≫ eT.hom := by
    have h := two_step _ _ Tl h1l hlT (c₁ ≫ sLev ↥T₁ w) (sLev ↥T₁ u ≫ e₁.hom)
      (by rw [Category.assoc, sLev_snd, c₁_snd]) (by rw [Category.assoc, e₁_snd, sLev_snd]) hl
    rw [restage_comp _ (ha := c₁_snd) (hb := sLev_snd _ _), restage_comp _ (ha := sLev_snd _ _) (hb := e₁_snd),
      restage_sLev, restage_sLev] at h
    exact h
  have Hlev'T : cT' ≫ sLev ↥T u = sLev ↥T w ≫ eT.inv := by
    have h := two_step _ _ Tl' h1l' hl'T (c₁' ≫ sLev ↥T₁ u) (sLev ↥T₁ w ≫ e₁.inv)
      (by rw [Category.assoc, sLev_snd, c₁'_snd]) (by rw [Category.assoc, e₁_inv_snd, sLev_snd]) hl'
    rw [restage_comp _ (ha := c₁'_snd) (hb := sLev_snd _ _), restage_comp _ (ha := sLev_snd _ _) (hb := e₁_inv_snd),
      restage_sLev, restage_sLev] at h
    exact h

  have HlevKT : kT ≫ sLevK ↥T w Cw = sLevK ↥T u Cu ≫ eT.hom := by
    have h := two_step _ _ Tk h1k hkT (k₁ ≫ sLevK ↥T₁ w Cw) (sLevK ↥T₁ u Cu ≫ e₁.hom)
      (by rw [Category.assoc, sLevK_snd, k₁_snd]) (by rw [Category.assoc, e₁_snd, sLevK_snd]) hkk
    rw [restage_comp _ (ha := k₁_snd) (hb := sLevK_snd _ _ _), restage_comp _ (ha := sLevK_snd _ _ _) (hb := e₁_snd),
      restage_sLevK, restage_sLevK] at h
    exact h
  have HlevK'T : kT' ≫ sLevK ↥T u Cu = sLevK ↥T w Cw ≫ eT.inv := by
    have h := two_step _ _ Tk' h1k' hk'T (k₁' ≫ sLevK ↥T₁ u Cu) (sLevK ↥T₁ w Cw ≫ e₁.inv)
      (by rw [Category.assoc, sLevK_snd, k₁'_snd]) (by rw [Category.assoc, e₁_inv_snd, sLevK_snd]) hkk'
    rw [restage_comp _ (ha := k₁'_snd) (hb := sLevK_snd _ _ _), restage_comp _ (ha := sLevK_snd _ _ _) (hb := e₁_inv_snd),
      restage_sLevK, restage_sLevK] at h
    exact h

  have HPT : sP ↥T u ≫ eT.hom = sP ↥T w := by
    have h := two_step _ _ Tp h1p hpT (sPP ↥T₁ u ≫ e₁.hom) (sPP ↥T₁ w)
      (by rw [Category.assoc, e₁_snd, sPP_snd]) (sPP_snd _ _) hp
    rw [restage_comp _ (ha := sPP_snd _ _) (hb := e₁_snd), restage_sPP, restage_sPP] at h
    haveI : IsIso (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (ι ↥T)) := inferInstance
    rw [← cancel_epi (pullback.snd (𝟙 (Spec (CommRingCat.of R))) (ι ↥T))]
    simpa only [sPP, Category.assoc] using h

  have HactG : ∀ x ∈ GΛ, sAct ↥T u x ≫ eT.hom = eT.hom ≫ sAct ↥T w x := by
    intro x hx'
    have h := two_step _ _ (Tx x) (h1x x) (hxT x hx') (sAct ↥T₁ u x ≫ e₁.hom) (e₁.hom ≫ sAct ↥T₁ w x)
      (by rw [Category.assoc, e₁_snd, sAct_snd]) (by rw [Category.assoc, sAct_snd, e₁_snd]) (hx x)
    rw [restage_comp _ (ha := sAct_snd _ _ _) (hb := e₁_snd), restage_comp _ (ha := e₁_snd) (hb := sAct_snd _ _ _),
      restage_sAct, restage_sAct] at h
    exact h

  have HmulT : PkgDesc17.MulClause u.1 w.1 ↥T eT.hom eT_snd :=
    PkgDesc18.mulClause_at u w T₁ T h1T e₁ e₁_snd mulA_snd mulB_snd
      (two_step _ _ Tm h1m hmT (PkgDesc17.mulA u.1 w.1 ↥T₁ e₁.hom) (PkgDesc17.mulB u.1 w.1 ↥T₁ e₁.hom e₁_snd)
        mulA_snd mulB_snd hmul) eT.hom rfl eT_snd

  have HactT : ∀ x : ↥Λ, sAct ↥T u x ≫ eT.hom = eT.hom ≫ sAct ↥T w x := by
    intro x
    refine PkgDesc17.act_closure u.1 w.1 eT.hom eT_snd HmulT (↑G : Set ℍ[ℚ, a, b]) hG ?_ x
    intro g hgG hg
    have hmem : (⟨g, hg⟩ : ↥Λ) ∈ GΛ := Finset.mem_image.2 ⟨⟨g, hgG⟩, Finset.mem_attach _ _, rfl⟩
    exact HactG ⟨g, hg⟩ hmem
  refine ⟨T, hTfg, hsT, eT, eT_snd, ?_, ?_, ?_, ⟨cT, ?_⟩, ⟨cT', ?_⟩, ⟨kT, ?_⟩, ⟨kT', ?_⟩⟩
  · intro T' t x y; exact HmulT t x y
  · intro x; exact HactT x
  · exact HPT
  · exact HlevT
  · exact Hlev'T
  · exact HlevKT
  · exact HlevK'T

end
end S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_fg_subalgebra_stdIsoPackage_extraLevel_of_stdIsoPackage (solution)
