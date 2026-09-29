-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/01c214ee-3dc4-5b5a-af20-aa7849a92ac9

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RegularLocalRingQuotientAscent.dualNumberFst_apply GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal NeronModelInfra GoodReductionJacobian

namespace W3

section Zn

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

def zn (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) : ↥Λ := ⟨(((n : ℕ) : ℤ) : ℚ), hΛℤ _⟩

theorem zn_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) :
    ((zn hΛℤ n : ↥Λ) : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
  simp [zn]

theorem zn_eq_of_coe (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (n : ℕ) (x : ↥Λ)
    (hx : (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b])) : x = zn hΛℤ n :=
  Subtype.ext (by rw [hx, zn_coe])

theorem zn_add (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (m n : ℕ) : zn hΛℤ m + zn hΛℤ n = zn hΛℤ (m + n) :=
  Subtype.ext (by
    rw [Submodule.coe_add, zn_coe, zn_coe, zn_coe]
    push_cast
    first | rfl | simp)

variable {S : Type} [CommRing S]

theorem act_zn_one (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S) :
    E.act (zn hΛℤ 1) = 𝟙 E.A := by
  have h1 : (1 : ℍ[ℚ, a, b]) ∈ Λ := by
    have := (zn hΛℤ 1).2
    rw [zn_coe] at this
    simpa using this
  have e : zn hΛℤ 1 = ⟨1, h1⟩ := Subtype.ext (by rw [zn_coe]; simp)
  rw [e, E.act_one h1]

theorem pushPt_act_zn (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) (E : FakeEllipticCurve Λ N S)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) (k : ℕ) :
    pushPt (E.act (zn hΛℤ k)) (E.act_over _) P = nsmulPt E.L t k P := by
  induction k with
  | zero =>
    have key := E.act_add (zn hΛℤ 0) (zn hΛℤ 0) t P
    rw [zn_add] at key
    letI := E.L.pointGroup t
    exact mul_eq_left.mp key.symm
  | succ k ih =>
    rw [← zn_add, E.act_add, ih]
    have h1 : pushPt (E.act (zn hΛℤ 1)) (E.act_over _) P = P :=
      Subtype.ext (by simp only [mapPt_coe, act_zn_one, Category.comp_id])
    rw [h1]
    rfl

end Zn

section Points

variable {S : Type} [CommRing S] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S)}

theorem mapPt_one (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    mapPt φ hφ (L.one t) = L'.one t := by
  have key := hmul t (L.one t) (L.one t)
  rw [L.one_mul t (L.one t)] at key
  letI := L'.pointGroup t
  exact mul_eq_left.mp key.symm

theorem mapPt_nsmulPt (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S f') (φ : A ⟶ A') (hφ : φ ≫ f' = f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      mapPt φ hφ (L.mul t P Q) = L'.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    mapPt φ hφ (nsmulPt L t n P) = nsmulPt L' t n (mapPt φ hφ P) := by
  induction n with
  | zero => exact mapPt_one L L' φ hφ hmul t
  | succ n ih =>
    show mapPt φ hφ (L.mul t (nsmulPt L t n P) P) = L'.mul t (nsmulPt L' t n (mapPt φ hφ P)) (mapPt φ hφ P)
    rw [hmul, ih]

theorem nsmulPt_mul (L : RelativeGroupLaw S f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (P : SchemeHomOver t f) (m n : ℕ) : nsmulPt L t (m * n) P = nsmulPt L t n (nsmulPt L t m P) := by
  letI := L.pointGroup t
  have h : ∀ (k : ℕ) (Q : SchemeHomOver t f), nsmulPt L t k Q = Q ^ k := by
    intro k Q
    induction k with
    | zero => exact (pow_zero Q).symm
    | succ k ih => rw [pow_succ, ← ih]; rfl
  rw [h, h, h, pow_mul]

end Points

end W3

open W3 in

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ) {r : ℕ} [Fact r.Prime]

    {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (E A : FakeEllipticCurve Λ N S) (E₀ A₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia p E E₀ g)
    (gA : A₀.A ⟶ A.A) (hgA : FakeEllipticCurve.IsPullbackVia p A A₀ gA)

    (φ : E.A ⟶ A.A) (hφ : φ ≫ A.f = E.f) (φ' : A.A ⟶ E.A) (hφ' : φ' ≫ E.f = A.f)
    (φ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = A.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (φ'_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt φ' hφ' (A.L.mul t P Q) = E.L.mul t (mapPt φ' hφ' P) (mapPt φ' hφ' Q))
    (φ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ A.act x) (φ'_act : ∀ x : ↥Λ, A.act x ≫ φ' = φ' ≫ E.act x)

    (φ₀ : E₀.A ⟶ A₀.A) (hφ₀ : φ₀ ≫ A₀.f = E₀.f) (φ₀' : A₀.A ⟶ E₀.A) (hφ₀' : φ₀' ≫ E₀.f = A₀.f) (d m m' : ℕ)
    (h₀ : FakeEllipticCurve.IsIsogenyPair (r ^ d) E₀ A₀ φ₀ φ₀')
    (hred : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (P : SchemeHomOver t E₀.f),
      P.1 ≫ g ≫ φ = (nsmulPt A₀.L t (r ^ m) (mapPt φ₀ hφ₀ P)).1 ≫ gA)
    (hred' : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀)) (Q : SchemeHomOver t A₀.f),
      Q.1 ≫ gA ≫ φ' = (nsmulPt E₀.L t (r ^ m') (mapPt φ₀' hφ₀' Q)).1 ≫ g) :
    FakeEllipticCurve.IsIsogenyPair (r ^ (d + m + m')) E A φ φ' := by
  obtain ⟨hφ₀o, hφ₀'o, h0mul, h0mul', h0act, h0act', h0deg⟩ := h₀
  obtain ⟨hgP, hgmul, hgact, -⟩ := hg
  obtain ⟨hgAP, hgAmul, hgAact, -⟩ := hgA
  have hnil : ∃ n : ℕ, RingHom.ker p ^ n = ⊥ := by
    obtain ⟨n, hn⟩ := hI
    exact ⟨n, by rw [← Ideal.zero_eq_bot]; exact hn⟩

  have hdd : (((r ^ d : ℕ) : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← zn_coe hΛℤ]; exact (zn hΛℤ _).2
  obtain ⟨hE₀deg, hA₀deg⟩ := h0deg hdd
  rw [zn_eq_of_coe hΛℤ (r ^ d) ⟨_, hdd⟩ rfl] at hE₀deg hA₀deg

  have keyE : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀))
      (P : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom p)) E.f),
      P.1 ≫ φ ≫ φ' = P.1 ≫ E.act (zn hΛℤ (r ^ (d + m + m'))) := by
    intro T t P
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : SchemeHomOver t E₀.f, P₀.1 ≫ g = P.1 :=
      ⟨⟨hgP.lift P.1 t P.2, hgP.lift_snd _ _ _⟩, hgP.lift_fst _ _ _⟩
    rw [← hP₀, Category.assoc, Category.assoc, reassoc_of% (hred t P₀), hred',
      mapPt_nsmulPt A₀.L E₀.L φ₀' hφ₀'o h0mul', ← hgact]
    have e2 : mapPt φ₀' hφ₀'o (mapPt φ₀ hφ₀o P₀) = nsmulPt E₀.L t (r ^ d) P₀ := by
      rw [← pushPt_act_zn hΛℤ E₀]
      exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hE₀deg])
    rw [e2, ← nsmulPt_mul, ← nsmulPt_mul, ← pow_add, ← pow_add]
    show _ = (pushPt (E₀.act (zn hΛℤ (r ^ (d + m + m')))) (E₀.act_over _) P₀).1 ≫ g
    rw [pushPt_act_zn hΛℤ E₀, show d + (m + m') = d + m + m' by omega]
  have keyA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀))
      (P : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom p)) A.f),
      P.1 ≫ φ' ≫ φ = P.1 ≫ A.act (zn hΛℤ (r ^ (d + m + m'))) := by
    intro T t P
    obtain ⟨P₀, hP₀⟩ : ∃ P₀ : SchemeHomOver t A₀.f, P₀.1 ≫ gA = P.1 :=
      ⟨⟨hgAP.lift P.1 t P.2, hgAP.lift_snd _ _ _⟩, hgAP.lift_fst _ _ _⟩
    rw [← hP₀, Category.assoc, Category.assoc, reassoc_of% (hred' t P₀), hred,
      mapPt_nsmulPt E₀.L A₀.L φ₀ hφ₀o h0mul, ← hgAact]
    have e2 : mapPt φ₀ hφ₀o (mapPt φ₀' hφ₀'o P₀) = nsmulPt A₀.L t (r ^ d) P₀ := by
      rw [← pushPt_act_zn hΛℤ A₀]
      exact Subtype.ext (by simp only [mapPt_coe, Category.assoc, hA₀deg])
    rw [e2, ← nsmulPt_mul, ← nsmulPt_mul, ← pow_add, ← pow_add]
    show _ = (pushPt (A₀.act (zn hΛℤ (r ^ (d + m + m')))) (A₀.act_over _) P₀).1 ≫ gA
    rw [pushPt_act_zn hΛℤ A₀, show d + (m' + m) = d + m + m' by omega]

  have rigid : ∀ (X Y : FakeEllipticCurve Λ N S) (χ₁ χ₂ : X.A ⟶ Y.A) (hχ₁ : χ₁ ≫ Y.f = X.f) (hχ₂ : χ₂ ≫ Y.f = X.f)
      (hom₁ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
        mapPt χ₁ hχ₁ (X.L.mul t P Q) = Y.L.mul t (mapPt χ₁ hχ₁ P) (mapPt χ₁ hχ₁ Q))
      (hom₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
        mapPt χ₂ hχ₂ (X.L.mul t P Q) = Y.L.mul t (mapPt χ₂ hχ₂ P) (mapPt χ₂ hχ₂ Q))
      (agree : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S₀))
        (P : SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom p)) X.f), P.1 ≫ χ₁ = P.1 ≫ χ₂),
      χ₁ = χ₂ := by
    intro X Y χ₁ χ₂ hχ₁ hχ₂ hom₁ hom₂ agree
    have H := GoodReductionJacobian.RelativeGroupLaw.eq_of_forall_mul_comp_eq_of_comp_eq_of_isNilpotent_ker S X.f Y.f X.L Y.L
      X.comm Y.comm X.bundle Y.bundle S S₀ p hp hnil (𝟙 _)
      (pullback.fst X.f (𝟙 _) ≫ χ₁) (pullback.fst X.f (𝟙 _) ≫ χ₂)
      (by rw [Category.assoc, hχ₁, pullback.condition]) (by rw [Category.assoc, hχ₂, pullback.condition])
      (by
        intro T t' P Q
        have l1 : ∀ (R : SchemeHomOver (t' ≫ 𝟙 _) X.f) (h1 : (pullback.lift R.1 t' R.2 ≫ (pullback.fst X.f (𝟙 _) ≫ χ₁)) ≫ Y.f = t' ≫ 𝟙 _),
            (⟨pullback.lift R.1 t' R.2 ≫ (pullback.fst X.f (𝟙 _) ≫ χ₁), h1⟩ : SchemeHomOver (t' ≫ 𝟙 _) Y.f) = mapPt χ₁ hχ₁ R :=
          fun R h1 => Subtype.ext (by simp only [mapPt_coe, pullback.lift_fst_assoc])
        rw [l1, l1, ← hom₁, mapPt_coe, pullback.lift_fst_assoc])
      (by
        intro T t' P Q
        have l1 : ∀ (R : SchemeHomOver (t' ≫ 𝟙 _) X.f) (h1 : (pullback.lift R.1 t' R.2 ≫ (pullback.fst X.f (𝟙 _) ≫ χ₂)) ≫ Y.f = t' ≫ 𝟙 _),
            (⟨pullback.lift R.1 t' R.2 ≫ (pullback.fst X.f (𝟙 _) ≫ χ₂), h1⟩ : SchemeHomOver (t' ≫ 𝟙 _) Y.f) = mapPt χ₂ hχ₂ R :=
          fun R h1 => Subtype.ext (by simp only [mapPt_coe, pullback.lift_fst_assoc])
        rw [l1, l1, ← hom₂, mapPt_coe, pullback.lift_fst_assoc])
      (by
        simp only [pullback.map, pullback.lift_fst_assoc, Category.id_comp]
        have hc : pullback.fst X.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _) ≫ X.f =
            (pullback.snd X.f (Spec.map (CommRingCat.ofHom p) ≫ 𝟙 _)) ≫ Spec.map (CommRingCat.ofHom p) := by
          rw [pullback.condition, Category.comp_id]
        exact agree _ ⟨_, hc⟩)
    have := congrArg (fun k => pullback.lift (𝟙 X.A) X.f (by simp) ≫ k) H
    simpa only [pullback.lift_fst_assoc, Category.id_comp] using this
  refine ⟨hφ, hφ', φ_mul, φ'_mul, φ_act, φ'_act, fun hd => ?_⟩
  rw [zn_eq_of_coe hΛℤ (r ^ (d + m + m')) ⟨_, hd⟩ rfl]
  have homE : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
      mapPt (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) (E.L.mul t P Q) =
        E.L.mul t (mapPt (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) P) (mapPt (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) Q) := by
    intro T t P Q
    have l1 : ∀ (R : SchemeHomOver t E.f), mapPt (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) R = mapPt φ' hφ' (mapPt φ hφ R) :=
      fun R => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
    rw [l1, l1, l1, φ_mul, φ'_mul]
  have homA : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t A.f),
      mapPt (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) (A.L.mul t P Q) =
        A.L.mul t (mapPt (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) P) (mapPt (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) Q) := by
    intro T t P Q
    have l1 : ∀ (R : SchemeHomOver t A.f), mapPt (φ' ≫ φ) (by rw [Category.assoc, hφ, hφ']) R = mapPt φ hφ (mapPt φ' hφ' R) :=
      fun R => Subtype.ext (by simp only [mapPt_coe, Category.assoc])
    rw [l1, l1, l1, φ'_mul, φ_mul]
  constructor
  · exact rigid E E (φ ≫ φ') (E.act _) (by rw [Category.assoc, hφ', hφ]) (E.act_over _) homE (E.act_hom _) keyE
  · exact rigid A A (φ' ≫ φ) (A.act _) (by rw [Category.assoc, hφ, hφ']) (A.act_over _) homA (A.act_hom _) keyA

end S_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_isIsogenyPair_pow_add_of_comp_eq_nsmulPt_pow_comp_of_isNilpotent_ker (solution)
