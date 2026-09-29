-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/f6dd332d-8d32-572d-920d-b6bee64f4676

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_comp_eq_of_isNilpotent_ker_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian"

namespace W1Asm

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rw [RelativeGroupLaw.nsmul_zero]; rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem val_comp_schemeNsmul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (Q : SchemeHomOver t f) : Q.1 ≫ L.schemeNsmul n = (nsmulPt L t n Q).1 := by
  have h := L.nsmul_natural f t Q.1 Q.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp Q.1 Q.2 (RelativeGroupLaw.idPoint (f := f)) = Q :=
    Subtype.ext (by rw [schemeHomOverComp_coe]; exact Category.comp_id _)
  rw [hid, ← nsmulPt_eq_nsmul L t n Q] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  have h2 : L.mul t (L.inv t x) (L.mul t x x) = L.mul t (L.inv t x) x := by rw [h]
  rw [← L.mul_assoc, L.inv_mul_cancel, L.one_mul] at h2
  exact h2

theorem pushPt_nsmulPt (L : RelativeGroupLaw R f) (u : A ⟶ A) (hu : u ≫ f = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt u hu (L.mul t P Q) = L.mul t (pushPt u hu P) (pushPt u hu Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (m : ℕ) (P : SchemeHomOver t f) :
    pushPt u hu (nsmulPt L t m P) = nsmulPt L t m (pushPt u hu P) := by
  induction m with
  | zero =>
      change pushPt u hu (L.one t) = L.one t
      apply eq_one_of_mul_self
      have := hhom t (L.one t) (L.one t)
      rw [L.one_mul] at this
      exact this.symm
  | succ m ih =>
      change pushPt u hu (L.mul t (nsmulPt L t m P) P) = L.mul t (nsmulPt L t m (pushPt u hu P)) (pushPt u hu P)
      rw [hhom, ih]

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R)}
    (x₁ y₁ x₂ y₂ : SchemeHomOver t f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t x₁ y₁).1 = (L.mul t x₂ y₂).1 := by
  have h1 : x₁ = x₂ := Subtype.ext hx
  have h2 : y₁ = y₂ := Subtype.ext hy
  subst h1 h2
  rfl

end W1Asm

open W1Asm in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {r : ℕ} [Fact r.Prime]
    (coord : ↥Λ → Zp2 r × Zp2 r) (hcoord : IsOrderCoord Λ r coord)

    {S S₀ : Type} [CommRing S] [IsNoetherianRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hp2 : ∀ s t : S, p s = 0 → p t = 0 → s * t = 0) (hr : IsNilpotent ((r : ℕ) : S))

    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f)
    (φ₀_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      mapPt φ₀ hφ₀ (E₀.L.mul t P Q) = A₀.L.mul t (mapPt φ₀ hφ₀ P) (mapPt φ₀ hφ₀ Q))
    (φ₀_act : ∀ x : ↥Λ, E₀.act x ≫ φ₀ = φ₀ ≫ A₀.act x) :
    ∃ (m : ℕ) (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
        mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x) ∧

      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
        P.1 ≫ g ≫ φ = (nsmulPt A₀.L t (r ^ m) (mapPt φ₀ hφ₀ P)).1 ≫ gA) := by
  classical
  letI : Algebra S S₀ := p.toAlgebra
  have hπ : Function.Surjective (algebraMap S S₀) := hp
  have hμ : RingHom.ker (algebraMap S S₀) ^ (1 + 1) = ⊥ := by
    rw [eq_bot_iff, pow_succ, pow_one, Ideal.mul_le]
    intro s hs t ht
    rw [Ideal.mem_bot]
    exact hp2 s t hs ht
  obtain ⟨n, hn⟩ := hr
  have hN : ((r ^ n : ℕ) : S) = 0 := by rw [Nat.cast_pow]; exact hn
  obtain ⟨hgpb, hg_mul, hg_act, -⟩ := hg
  obtain ⟨hgApb, hgA_mul, hgA_act, -⟩ := hgA

  have hu₀hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t E₀.f),
      (E₀.L.mul t P Q).1 ≫ φ₀ =
        (A₀.L.mul t ⟨P.1 ≫ φ₀, by rw [Category.assoc, hφ₀]; exact P.2⟩
          ⟨Q.1 ≫ φ₀, by rw [Category.assoc, hφ₀]; exact Q.2⟩).1 :=
    fun t P Q => congrArg Subtype.val (φ₀_mul t P Q)

  obtain ⟨F, hF, hFhom, hFred⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_comp_schemeNsmul_comp_of_natCast_eq_zero
      S S₀ hπ (r ^ n) hN 1 hμ E.f E.L E.comm E.bundle A.f A.L A.comm A.bundle
      E₀.f E₀.L g hgpb (fun t P Q => hg_mul t P Q) A₀.f A₀.L gA hgApb (fun t P Q => hgA_mul t P Q)
      φ₀ hφ₀ (fun t P Q => hu₀hom t P Q)

  have hFmap : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt F hF (E.L.mul t P Q) = A.L.mul t (mapPt F hF P) (mapPt F hF Q) :=
    fun t P Q => Subtype.ext (hFhom t P Q)

  have hred : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
      P.1 ≫ g ≫ F = (nsmulPt A₀.L t (r ^ (n * 1)) (mapPt φ₀ hφ₀ P)).1 ≫ gA := by
    intro T t P
    rw [hFred, ← Category.assoc P.1 φ₀, ← mapPt_coe φ₀ hφ₀ P, ← Category.assoc, val_comp_schemeNsmul, pow_one,
      mul_one]
  refine ⟨n * 1, F, hF, hFmap, ?_, hred⟩

  intro x
  have hI : IsNilpotent (RingHom.ker (algebraMap S S₀)) := ⟨1 + 1, hμ⟩
  have h1f : (E.act x ≫ F) ≫ A.f = E.f := by rw [Category.assoc, hF, E.act_over]
  have h2f : (F ≫ A.act x) ≫ A.f = E.f := by rw [Category.assoc, A.act_over, hF]
  refine GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_comp_eq_of_isNilpotent_ker_of_isNoetherianRing
    (algebraMap S S₀) hπ hI E.L A.L E.bundle A.bundle (E.act x ≫ F) (F ≫ A.act x) h1f h2f ?_ ?_ ?_
  ·
    intro T t P Q
    apply Subtype.ext
    have h1 := congrArg Subtype.val (E.act_hom x t P Q)
    simp only [mapPt_coe] at h1
    have h2 := congrArg Subtype.val (hFmap t (pushPt (E.act x) (E.act_over x) P) (pushPt (E.act x) (E.act_over x) Q))
    simp only [mapPt_coe] at h2
    change (E.L.mul t P Q).1 ≫ E.act x ≫ F = _
    rw [← Category.assoc, h1, h2]
    exact mul_val_congr A.L _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)
  ·
    intro T t P Q
    apply Subtype.ext
    have h1 := congrArg Subtype.val (hFmap t P Q)
    simp only [mapPt_coe] at h1
    have h2 := congrArg Subtype.val (A.act_hom x t (mapPt F hF P) (mapPt F hF Q))
    simp only [mapPt_coe] at h2
    change (E.L.mul t P Q).1 ≫ F ≫ A.act x = _
    rw [← Category.assoc, h1, h2]
    exact mul_val_congr A.L _ _ _ _ (Category.assoc _ _ _) (Category.assoc _ _ _)
  ·
    intro T t P

    have hP : P.1 ≫ E.f = t ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)) := P.2
    set P₀ : T ⟶ E₀.A := hgpb.lift P.1 t hP with hP₀def
    have hP₀g : P₀ ≫ g = P.1 := hgpb.lift_fst _ _ hP
    have hP₀f : P₀ ≫ E₀.f = t := hgpb.lift_snd _ _ hP

    let Px : SchemeHomOver t E₀.f := ⟨P₀ ≫ E₀.act x, by rw [Category.assoc, E₀.act_over]; exact hP₀f⟩
    have hx1 := hred t Px
    have hx2 := hred t ⟨P₀, hP₀f⟩

    have hmap : mapPt φ₀ hφ₀ Px = pushPt (A₀.act x) (A₀.act_over x) (mapPt φ₀ hφ₀ ⟨P₀, hP₀f⟩) := by
      apply Subtype.ext
      change (P₀ ≫ E₀.act x) ≫ φ₀ = (P₀ ≫ φ₀) ≫ A₀.act x
      rw [Category.assoc, φ₀_act x, Category.assoc]
    rw [hmap, ← pushPt_nsmulPt A₀.L (A₀.act x) (A₀.act_over x) (fun t P Q => A₀.act_hom x t P Q)] at hx1
    change (P₀ ≫ E₀.act x) ≫ g ≫ F = ((nsmulPt A₀.L t (r ^ (n * 1)) (mapPt φ₀ hφ₀ ⟨P₀, hP₀f⟩)).1 ≫ A₀.act x) ≫ gA at hx1
    calc P.1 ≫ E.act x ≫ F = P₀ ≫ (g ≫ E.act x) ≫ F := by rw [← hP₀g]; simp only [Category.assoc]
      _ = P₀ ≫ (E₀.act x ≫ g) ≫ F := by rw [hg_act x]
      _ = (P₀ ≫ E₀.act x) ≫ g ≫ F := by simp only [Category.assoc]
      _ = (nsmulPt A₀.L t (r ^ (n * 1)) (mapPt φ₀ hφ₀ ⟨P₀, hP₀f⟩)).1 ≫ A₀.act x ≫ gA := by
            rw [hx1]; simp only [Category.assoc]
      _ = (nsmulPt A₀.L t (r ^ (n * 1)) (mapPt φ₀ hφ₀ ⟨P₀, hP₀f⟩)).1 ≫ gA ≫ A.act x := by rw [hgA_act x]
      _ = (P₀ ≫ g ≫ F) ≫ A.act x := by rw [hx2]; simp only [Category.assoc]
      _ = P.1 ≫ F ≫ A.act x := by rw [← hP₀g]; simp only [Category.assoc]

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_comp_eq_nsmulPt_pow_comp_of_squareZero_of_isNoetherianRing (solution)
