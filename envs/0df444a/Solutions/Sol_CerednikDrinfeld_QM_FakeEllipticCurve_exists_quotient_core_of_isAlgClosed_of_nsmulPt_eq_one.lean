-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_quotient_core_of_isAlgClosed_of_nsmulPt_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7649c5ac-9a9b-535d-80ac-fdf898cf6dfc

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_quotient_desc_hom_of_isColimit
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_pushPt_act_natCast_eq_nsmulPt
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_forall_finset_exists_isAffineOpen_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isFinite_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed_of_nsmulPt_eq_one
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian

namespace C1asm

universe u

variable {R : Type u} [CommRing R]

theorem mapPt_comp {A A' A'' : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R)}
    {f'' : A'' ⟶ Spec (CommRingCat.of R)} (φ : A ⟶ A') (hφ : φ ≫ f' = f) (ψ : A' ⟶ A'') (hψ : ψ ≫ f'' = f')
    {h : (φ ≫ ψ) ≫ f'' = f} {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (P : SchemeHomOver t f) :
    mapPt (φ ≫ ψ) h P = mapPt ψ hψ (mapPt φ hφ P) := by
  apply Subtype.ext; simp [mapPt, Category.assoc]

theorem nsmulPt_eq_nsmul {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f) :
    nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GoodReductionJacobian.RelativeGroupLaw.nsmul_succ, ← ih]; rfl

def IsHom {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    (LX : RelativeGroupLaw R gX) (LY : RelativeGroupLaw R gY) (α : SchemeHomOver gX gY) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (u v : SchemeHomOver t gX),
    mapPt α.1 α.2 (LX.mul t u v) = LY.mul t (mapPt α.1 α.2 u) (mapPt α.1 α.2 v)

theorem IsHom.comp {X Y Z : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {gZ : Z ⟶ Spec (CommRingCat.of R)} {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {LZ : RelativeGroupLaw R gZ}
    {α : SchemeHomOver gX gY} {β : SchemeHomOver gY gZ} (hα : IsHom LX LY α) (hβ : IsHom LY LZ β) :
    IsHom LX LZ ⟨α.1 ≫ β.1, by rw [Category.assoc, β.2, α.2]⟩ := by
  intro T t u v
  show mapPt (α.1 ≫ β.1) _ (LX.mul t u v) = LZ.mul t (mapPt (α.1 ≫ β.1) _ u) (mapPt (α.1 ≫ β.1) _ v)
  rw [mapPt_comp α.1 α.2 β.1 β.2, hα, hβ, ← mapPt_comp α.1 α.2 β.1 β.2, ← mapPt_comp α.1 α.2 β.1 β.2]

theorem IsHom.map_one {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : mapPt α.1 α.2 (LX.one t) = LY.one t := by
  have h := hα t (LX.one t) (LX.one t)
  rw [LX.one_mul] at h
  have := congrArg (LY.mul t (LY.inv t (mapPt α.1 α.2 (LX.one t)))) h
  rw [← LY.mul_assoc, LY.inv_mul_cancel, LY.one_mul] at this
  exact this.symm

theorem IsHom.map_nsmulPt {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t gX) :
    mapPt α.1 α.2 (nsmulPt LX t n P) = nsmulPt LY t n (mapPt α.1 α.2 P) := by
  induction n with
  | zero => exact hα.map_one t
  | succ n ih => simp only [nsmulPt]; rw [hα, ih]

theorem IsHom.map_inv {X Y : Scheme.{u}} {gX : X ⟶ Spec (CommRingCat.of R)} {gY : Y ⟶ Spec (CommRingCat.of R)}
    {LX : RelativeGroupLaw R gX} {LY : RelativeGroupLaw R gY} {α : SchemeHomOver gX gY} (hα : IsHom LX LY α)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t gX) :
    mapPt α.1 α.2 (LX.inv t P) = LY.inv t (mapPt α.1 α.2 P) := by
  letI := LY.pointGroup t
  have h := hα t (LX.inv t P) P
  rw [LX.inv_mul_cancel, hα.map_one] at h
  exact (inv_eq_of_mul_eq_one_left h.symm).symm

end C1asm

theorem C1asm.quotCore
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E₀ : FakeEllipticCurve Λ N k) (hO : IsOrder Λ)
    (n : ℕ)
    (K₀ : Scheme.{0}) (ι : K₀ ⟶ E₀.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ E₀.f)) (hι_flat : Flat (ι ≫ E₀.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ E₀.f))
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (E₀.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (E₀.L.mul t P Q) ∧ FactorsThrough ι (E₀.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (E₀.act x) (E₀.act_over x) P))
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → nsmulPt E₀.L t n P = E₀.L.one t) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (act : ↥Λ → (A ⟶ A))
      (hact : ∀ x : ↥Λ, act x ≫ f = f)
      (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f) (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f),

      L.IsCommutative ∧
      AbelianSchemePropertyBundle k f ∧
      (∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
        pushPt (act (x + y)) (hact (x + y)) P = L.mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E₀.act x ≫ p = p ≫ act x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ y : ↥A, p.finrank y = (ι ≫ E₀.f).finrank (f.base y)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt p hp P = L.one t ↔ FactorsThrough ι P) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, act x ≫ ψ = ψ ≫ E₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t n P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
        mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t n Q) ∧

      (∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : E₀.A ⟶ X) (hφ : φ ≫ gX = E₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
          mapPt φ hφ (E₀.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
          FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
        ∃! χ : SchemeHomOver f gX, p ≫ χ.1 = φ ∧
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f),
            mapPt χ.1 χ.2 (L.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) := by
  classical
  haveI := hι_closed
  haveI := hι_finite
  haveI := hι_flat
  haveI := hι_fp

  obtain ⟨P, g, LP, p, hg, w, hbundle, hcommP, hfin, hflat, hlfp, hsurj, hhom, hker, hpb, ⟨hcolim⟩⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_quotient_abelianSchemePropertyBundle_of_finiteFlat_subgroup
      E₀.L E₀.bundle E₀.comm
      (GoodReductionJacobian.RelativeGroupLaw.forall_finset_exists_isAffineOpen_of_isAlgClosed E₀.L E₀.bundle)
      ι hK_one (fun t x y hx hy => (hK_sub t x y hx hy).1) (fun t x hx => (hK_sub t x x hx hx).2)
  haveI := hfin
  haveI := hflat
  haveI := hlfp
  haveI := hsurj
  have hhom' : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t E₀.f),
      mapPt p hg (E₀.L.mul t x y) = LP.mul t (mapPt p hg x) (mapPt p hg y) := fun t x y => hhom t x y

  have hdesc_act : ∀ x : ↥Λ, ∃! ψ : SchemeHomOver g g, p ≫ ψ.1 = E₀.act x ≫ p ∧
      ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩ := by
    intro x
    refine GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E₀.L ι p w hcolim hg LP
      hhom LP ⟨E₀.act x ≫ p, by rw [Category.assoc, hg, E₀.act_over]⟩ ?_ ?_
    · intro T t x' y'
      have h1 := congrArg (mapPt p hg) (E₀.act_hom x t x' y')
      rw [hhom'] at h1
      have e1 : ∀ (z : SchemeHomOver t E₀.f),
          (⟨z.1 ≫ (E₀.act x ≫ p), by rw [Category.assoc, Category.assoc, hg, E₀.act_over, z.2]⟩ : SchemeHomOver t g) =
            mapPt p hg (pushPt (E₀.act x) (E₀.act_over x) z) := by
        intro z; apply Subtype.ext; simp [mapPt, pushPt, Category.assoc]
      rw [e1, e1, e1]; exact h1
    · intro T t e he
      have hfac : FactorsThrough ι (pushPt (E₀.act x) (E₀.act_over x)
          (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f)) :=
        hK_stable x t _ ⟨e, rfl⟩
      obtain ⟨e', he'⟩ := hfac
      have := (hker t (pushPt (E₀.act x) (E₀.act_over x)
        (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f))).2 ⟨e', he'⟩
      refine Eq.trans ?_ this
      apply Subtype.ext; simp [mapPt, pushPt, Category.assoc]
  choose actP hactP using hdesc_act
  have hpact : ∀ x : ↥Λ, p ≫ (actP x).1 = E₀.act x ≫ p := fun x => (hactP x).1.1
  have hactP_hom : ∀ (x : ↥Λ) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t g),
      (⟨(LP.mul t u v).1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
        LP.mul t ⟨u.1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, u.2]⟩
          ⟨v.1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, v.2]⟩ :=
    fun x => (hactP x).1.2
  have hactP_uniq : ∀ (x : ↥Λ) (ψ : SchemeHomOver g g), p ≫ ψ.1 = E₀.act x ≫ p →
      (∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t g),
        (⟨(LP.mul t u v).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (LP.mul t u v).2]⟩ : SchemeHomOver t g) =
          LP.mul t ⟨u.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, u.2]⟩ ⟨v.1 ≫ ψ.1, by rw [Category.assoc, ψ.2, v.2]⟩) →
      ψ = actP x := fun x ψ h1 h2 => (hactP x).2 ψ ⟨h1, h2⟩

  have hnΛ : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    have : ((n : ℚ) : ℍ[ℚ, a, b]) = (n : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
    rw [this]; exact Λ.smul_mem _ hO.one_mem
  obtain ⟨ψ, ⟨hpψ, hψhom⟩, hψuniq⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E₀.L ι p w hcolim hg LP hhom
      E₀.L ⟨E₀.act ⟨_, hnΛ⟩, E₀.act_over _⟩ (fun t x y => E₀.act_hom ⟨_, hnΛ⟩ t x y) (by
        intro T t e he
        have h1 := CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₀ hO.one_mem n hnΛ t
          (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f)
        have h2 := hK_torsion t (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f) ⟨e, rfl⟩
        exact (h1.trans h2))

  have hp_hom : C1asm.IsHom E₀.L LP ⟨p, hg⟩ := fun _ t x y => hhom' t x y
  have hψ_hom : C1asm.IsHom LP E₀.L ψ := fun _ t u v => hψhom t u v
  have hact_hom : ∀ x : ↥Λ, C1asm.IsHom LP LP (actP x) := fun x _ t u v => hactP_hom x t u v
  have hEact_hom : ∀ x : ↥Λ, C1asm.IsHom E₀.L E₀.L ⟨E₀.act x, E₀.act_over x⟩ := fun x _ t u v => E₀.act_hom x t u v
  have hact_one : ∀ h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ, (actP ⟨1, h1⟩).1 = 𝟙 P := by
    intro h1
    have := hactP_uniq ⟨1, h1⟩ ⟨𝟙 P, Category.id_comp g⟩ (by rw [E₀.act_one h1]; simp) (by
      intro T t u v; apply Subtype.ext; simp)
    exact (congrArg Subtype.val this).symm
  have hact_mul : ∀ (x y : ↥Λ) (hxy : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
      (actP ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), hxy⟩).1 = (actP y).1 ≫ (actP x).1 := by
    intro x y hxy
    have hc := C1asm.IsHom.comp (hact_hom y) (hact_hom x)
    have hcand := hactP_uniq ⟨(x : ℍ[ℚ, a, b]) * y, hxy⟩ ⟨(actP y).1 ≫ (actP x).1, by rw [Category.assoc, (actP x).2, (actP y).2]⟩
      (by rw [← Category.assoc, hpact y, Category.assoc, hpact x, ← Category.assoc, ← E₀.act_mul x y hxy])
      (fun t u v => hc t u v)
    exact (congrArg Subtype.val hcand).symm
  have hact_add : ∀ (x y : ↥Λ) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (P' : SchemeHomOver t g),
      pushPt (actP (x + y)).1 (actP (x + y)).2 P' = LP.mul t (pushPt (actP x).1 (actP x).2 P') (pushPt (actP y).1 (actP y).2 P') := by
    intro x y T t P'
    have hh : ∀ (z : ↥Λ) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t g),
        pushPt (actP z).1 (actP z).2 (LP.mul t u v) = LP.mul t (pushPt (actP z).1 (actP z).2 u) (pushPt (actP z).1 (actP z).2 v) :=
      fun z _ t u v => hactP_hom z t u v
    have hsum : ∀ {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t g),
        pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 Q =
          LP.mul t (pushPt (actP x).1 (actP x).2 Q) (pushPt (actP y).1 (actP y).2 Q) :=
      fun t Q => LP.mul_natural g t Q.1 Q.2 (actP x) (actP y)
    have hσ : LP.mul g (actP x) (actP y) = actP (x + y) := by
      refine hactP_uniq (x + y) _ ?_ ?_
      · have h1 := LP.mul_natural g E₀.f p hg (actP x) (actP y)
        have h2 : ∀ z : ↥Λ, schemeHomOverComp p hg (actP z) = mapPt p hg ⟨E₀.act z, E₀.act_over z⟩ := by
          intro z; apply Subtype.ext; exact hpact z
        have h3 := E₀.act_add x y E₀.f ⟨𝟙 E₀.A, Category.id_comp _⟩
        have h4 : ∀ z : ↥Λ, pushPt (E₀.act z) (E₀.act_over z) (⟨𝟙 E₀.A, Category.id_comp _⟩ : SchemeHomOver E₀.f E₀.f) =
            ⟨E₀.act z, E₀.act_over z⟩ := by
          intro z; apply Subtype.ext; exact Category.id_comp _
        simp only [h4] at h3
        rw [h2, h2, ← hhom', ← h3] at h1
        exact congrArg Subtype.val h1
      · intro T t u v
        show pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 (LP.mul t u v) =
          LP.mul t (pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 u)
            (pushPt (LP.mul g (actP x) (actP y)).1 (LP.mul g (actP x) (actP y)).2 v)
        rw [hsum, hsum, hsum, hh x, hh y]
        letI : CommGroup (SchemeHomOver t g) := { (LP.pointGroup t) with mul_comm := hcommP t }
        exact mul_mul_mul_comm _ _ _ _
    show pushPt (actP (x + y)).1 (actP (x + y)).2 P' = LP.mul t (pushPt (actP x).1 (actP x).2 P') (pushPt (actP y).1 (actP y).2 P')
    rw [← hσ]
    exact hsum t P'
  have hψlin : ∀ x : ↥Λ, (actP x).1 ≫ ψ.1 = ψ.1 ≫ E₀.act x := by
    intro x
    have hcomm_xl : E₀.act x ≫ E₀.act ⟨_, hnΛ⟩ = E₀.act ⟨_, hnΛ⟩ ≫ E₀.act x := by
      have h1 := E₀.act_mul ⟨_, hnΛ⟩ x (hO.mul_mem hnΛ x.2)
      have h2 := E₀.act_mul x ⟨_, hnΛ⟩ (hO.mul_mem x.2 hnΛ)
      have h3 : (⟨((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hO.mul_mem hnΛ x.2⟩ : ↥Λ) =
          ⟨(x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b]), hO.mul_mem x.2 hnΛ⟩ := by
        apply Subtype.ext
        show ((n : ℚ) : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = (x : ℍ[ℚ, a, b]) * ((n : ℚ) : ℍ[ℚ, a, b])
        rw [QuaternionAlgebra.coe_mul_eq_smul, QuaternionAlgebra.mul_coe_eq_smul]
      rw [h3] at h1; rw [h1] at h2; exact h2
    obtain ⟨χ, -, hχuniq⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E₀.L ι p w hcolim hg LP hhom
        E₀.L ⟨E₀.act x ≫ E₀.act ⟨_, hnΛ⟩, by rw [Category.assoc, E₀.act_over, E₀.act_over]⟩
        (fun t u v => (C1asm.IsHom.comp (hEact_hom x) (hEact_hom ⟨_, hnΛ⟩)) t u v) (by
          intro T t e he
          have h1 := CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₀ hO.one_mem n hnΛ t
            (pushPt (E₀.act x) (E₀.act_over x) (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f))
          have h2 := hK_torsion t
            (pushPt (E₀.act x) (E₀.act_over x) (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f))
            (hK_stable x t _ ⟨e, rfl⟩)
          refine Eq.trans ?_ (h1.trans h2)
          apply Subtype.ext; simp [pushPt, mapPt, Category.assoc])
    have hA : (⟨(actP x).1 ≫ ψ.1, by rw [Category.assoc, ψ.2, (actP x).2]⟩ : SchemeHomOver g E₀.f) = χ :=
      hχuniq _ ⟨by rw [← Category.assoc, hpact x, Category.assoc, hpψ], fun t u v => (C1asm.IsHom.comp (hact_hom x) hψ_hom) t u v⟩
    have hB : (⟨ψ.1 ≫ E₀.act x, by rw [Category.assoc, E₀.act_over, ψ.2]⟩ : SchemeHomOver g E₀.f) = χ :=
      hχuniq _ ⟨by rw [← Category.assoc, hpψ]; exact hcomm_xl.symm, fun t u v => (C1asm.IsHom.comp hψ_hom (hEact_hom x)) t u v⟩
    exact congrArg Subtype.val (hA.trans hB.symm)
  have hψp : ψ.1 ≫ p = (actP ⟨((n : ℚ) : ℍ[ℚ, a, b]), hnΛ⟩).1 := by
    have hcand := hactP_uniq ⟨_, hnΛ⟩ ⟨ψ.1 ≫ p, by rw [Category.assoc, hg, ψ.2]⟩
      (by rw [← Category.assoc, hpψ]) (fun t u v => (C1asm.IsHom.comp hψ_hom hp_hom) t u v)
    exact congrArg Subtype.val hcand

  have hnat : ∀ (m : ℕ) (hm : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {T : Scheme} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t g),
      pushPt (actP ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩).1 (actP ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm⟩).2 Q = nsmulPt LP t m Q := by
    intro m
    induction m with
    | zero =>
      intro hm T t Q
      have h0 : (⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) + ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ = ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ := by
        apply Subtype.ext; simp
      have h := hact_add ⟨_, hm⟩ ⟨_, hm⟩ t Q
      rw [h0] at h

      have := congrArg (LP.mul t (LP.inv t (pushPt (actP ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩).1 (actP ⟨(((0 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩).2 Q))) h
      rw [← LP.mul_assoc, LP.inv_mul_cancel, LP.one_mul] at this
      exact this.symm
    | succ m ih =>
      intro hm T t Q
      have hm' : ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
        have : ((m : ℚ) : ℍ[ℚ, a, b]) = (m : ℤ) • (1 : ℍ[ℚ, a, b]) := by rw [zsmul_eq_mul, mul_one]; norm_cast
        rw [this]; exact Λ.smul_mem _ hO.one_mem
      have e : (⟨(((m + 1 : ℕ) : ℚ) : ℍ[ℚ, a, b]), hm⟩ : ↥Λ) = ⟨((m : ℚ) : ℍ[ℚ, a, b]), hm'⟩ + ⟨1, hO.one_mem⟩ := by
        apply Subtype.ext; push_cast; rfl
      rw [e, hact_add, ih hm']
      have h1' : pushPt (actP ⟨1, hO.one_mem⟩).1 (actP ⟨1, hO.one_mem⟩).2 Q = Q := by
        apply Subtype.ext
        show Q.1 ≫ (actP ⟨1, hO.one_mem⟩).1 = Q.1
        rw [hact_one, Category.comp_id]
      rw [h1']
      rfl

  have hrank : ∀ y : ↥P, p.finrank y = (ι ≫ E₀.f).finrank (g.base y) := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj.1 y
    have h1 := Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb.flip x

    rw [← h1, Scheme.Hom.finrank_pullback_snd]
    congr 1
    show E₀.f.base x = g.base (p.base x)
    rw [← hg]; rfl
  refine ⟨P, g, LP, fun x => (actP x).1, fun x => (actP x).2, p, hg, ψ.1, ψ.2, hcommP, hbundle,
    fun s => (AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isFinite_of_surjective E₀.f g p hg s).trans (E₀.dim_fibre s),
    fun x _ t P' Q' => hactP_hom x t P' Q', hact_one, hact_mul, fun x y _ t P' => hact_add x y t P',
    hhom', fun x => (hpact x).symm, hfin, hflat, hlfp, hsurj, hrank, fun t P' => hker t P',
    fun t u v => hψhom t u v, hψlin, ?_, ?_, ?_⟩
  ·
    intro T t P'
    have e : mapPt ψ.1 ψ.2 (mapPt p hg P') = pushPt (E₀.act ⟨_, hnΛ⟩) (E₀.act_over _) P' := by
      apply Subtype.ext
      show (P'.1 ≫ p) ≫ ψ.1 = P'.1 ≫ E₀.act ⟨_, hnΛ⟩
      rw [Category.assoc, hpψ]
    exact e.trans (CerednikDrinfeld.QM.FakeEllipticCurve.pushPt_act_natCast_eq_nsmulPt E₀ hO.one_mem n hnΛ t P')
  ·
    intro T t Q
    have e : mapPt p hg (mapPt ψ.1 ψ.2 Q) = pushPt (actP ⟨_, hnΛ⟩).1 (actP ⟨_, hnΛ⟩).2 Q := by
      apply Subtype.ext
      show (Q.1 ≫ ψ.1) ≫ p = Q.1 ≫ (actP ⟨_, hnΛ⟩).1
      rw [Category.assoc, hψp]
    exact e.trans (hnat n hnΛ t Q)
  ·
    intro X gX LX φ hφ hφhom hφK
    exact GoodReductionJacobian.RelativeGroupLaw.existsUnique_quotient_desc_hom_of_isColimit E₀.L ι p w hcolim hg LP hhom
      LX ⟨φ, hφ⟩ (fun t x y => hφhom t x y)
      (fun t e he => hφK t (⟨e ≫ ι, by rw [Category.assoc]; exact he⟩ : SchemeHomOver t E₀.f) ⟨e, rfl⟩)

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type) [Field k] [IsAlgClosed k] (E₀ : FakeEllipticCurve Λ N k) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (n : ℕ)
    (K₀ : Scheme.{0}) (ι : K₀ ⟶ E₀.A) (hι_closed : IsClosedImmersion ι)
    (hι_finite : IsFinite (ι ≫ E₀.f)) (hι_flat : Flat (ι ≫ E₀.f)) (hι_fp : LocallyOfFinitePresentation (ι ≫ E₀.f))
    (hK_one : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)), FactorsThrough ι (E₀.L.one t))
    (hK_sub : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι Q → FactorsThrough ι (E₀.L.mul t P Q) ∧ FactorsThrough ι (E₀.L.inv t P))
    (hK_stable : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → FactorsThrough ι (pushPt (E₀.act x) (E₀.act_over x) P))
    (hK_torsion : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
      FactorsThrough ι P → nsmulPt E₀.L t n P = E₀.L.one t) :
    ∃ (A : Scheme.{0}) (f : A ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (act : ↥Λ → (A ⟶ A))
      (hact : ∀ x : ↥Λ, act x ≫ f = f)
      (p : E₀.A ⟶ A) (hp : p ≫ f = E₀.f) (ψ : A ⟶ E₀.A) (hψ : ψ ≫ E₀.f = f),

      L.IsCommutative ∧
      AbelianSchemePropertyBundle k f ∧
      (∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = 2) ∧
      (∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        pushPt (act x) (hact x) (L.mul t P Q) = L.mul t (pushPt (act x) (hact x) P) (pushPt (act x) (hact x) Q)) ∧
      (∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 A) ∧
      (∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
        act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x) ∧
      (∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
        pushPt (act (x + y)) (hact (x + y)) P = L.mul t (pushPt (act x) (hact x) P) (pushPt (act y) (hact y) P)) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
        mapPt p hp (E₀.L.mul t P Q) = L.mul t (mapPt p hp P) (mapPt p hp Q)) ∧
      (∀ x : ↥Λ, E₀.act x ≫ p = p ≫ act x) ∧
      IsFinite p ∧ Flat p ∧ LocallyOfFinitePresentation p ∧ Surjective p ∧
      (∀ y : ↥A, p.finrank y = (ι ≫ E₀.f).finrank (f.base y)) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt p hp P = L.one t ↔ FactorsThrough ι P) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
        mapPt ψ hψ (L.mul t P Q) = E₀.L.mul t (mapPt ψ hψ P) (mapPt ψ hψ Q)) ∧
      (∀ x : ↥Λ, act x ≫ ψ = ψ ≫ E₀.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
        mapPt ψ hψ (mapPt p hp P) = nsmulPt E₀.L t n P) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (Q : SchemeHomOver t f),
        mapPt p hp (mapPt ψ hψ Q) = nsmulPt L t n Q) ∧

      (∀ (X : Scheme.{0}) (gX : X ⟶ Spec (CommRingCat.of k)) (LX : RelativeGroupLaw k gX) (φ : E₀.A ⟶ X) (hφ : φ ≫ gX = E₀.f),
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t E₀.f),
          mapPt φ hφ (E₀.L.mul t P Q) = LX.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t E₀.f),
          FactorsThrough ι P → mapPt φ hφ P = LX.one t) →
        ∃! χ : SchemeHomOver f gX, p ≫ χ.1 = φ ∧
          ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (u v : SchemeHomOver t f),
            mapPt χ.1 χ.2 (L.mul t u v) = LX.mul t (mapPt χ.1 χ.2 u) (mapPt χ.1 χ.2 v)) := by
  exact C1asm.quotCore k E₀ hΛ n K₀ ι hι_closed hι_finite hι_flat hι_fp hK_one hK_sub hK_stable hK_torsion

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed_of_nsmulPt_eq_one
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_quotient_core_of_isAlgClosed_of_nsmulPt_eq_one (solution)
