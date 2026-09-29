-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.ExtraLevel.etale_and_forall_factorsThrough_iff_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9fd11547-3786-5e31-9f0a-f0b13ca281f1

import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM"
open scoped Quaternion

noncomputable section

namespace ExtraLevelUniqBody

section Geometric

variable {S : Type} [CommRing S]

def ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) : S →+* k :=
  (Spec.preimage b).hom

theorem geomPoint_ringHomOf {k : Type} [Field k] (b : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) :
    geomPoint k (ringHomOf b) = b := by
  unfold geomPoint ringHomOf
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

def geomPtAt (X : Scheme.{0}) (x : X) : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x))) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) (AlgebraicClosure (X.residueField x)))) ≫
    X.fromSpecResidueField x

theorem geomPtAt_apply (X : Scheme.{0}) (x : X) (p : Spec (CommRingCat.of (AlgebraicClosure (X.residueField x)))) :
    (geomPtAt X x).base p = x := by
  simp only [geomPtAt, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
  exact Scheme.fromSpecResidueField_apply x _

end Geometric

section Kernel

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem nsmul_eq_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    L.nsmul t n P = nsmulPt L t n P := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show L.mul t (L.nsmul t n P) P = L.mul t (nsmulPt L t n P) P
    rw [ih]

theorem coe_nsmulPt {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (P : SchemeHomOver t f) :
    (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have hnat := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P :=
    Subtype.ext (Category.comp_id _)
  rw [hid, nsmul_eq_nsmulPt, nsmul_eq_nsmulPt] at hnat
  rw [← hnat]
  show P.1 ≫ (nsmulPt L f n RelativeGroupLaw.idPoint).1 = P.1 ≫ (L.nsmul f n RelativeGroupLaw.idPoint).1
  rw [nsmul_eq_nsmulPt]

theorem coe_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id t)
  exact (congrArg Subtype.val h).symm

abbrev kerι (n : ℕ) : L.schemeKer n ⟶ A :=
  pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1

theorem kerι_f (n : ℕ) : kerι L n ≫ f = L.schemeKerStr n := by
  have h1 : kerι L n ≫ f = kerι L n ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over n]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc,
    (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id]

def kerLift {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : T ⟶ L.schemeKer n :=
  pullback.lift P.1 t (by rw [← coe_nsmulPt, hP, coe_one])

@[scoped simp, reassoc] theorem kerLift_kerι {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ kerι L n = P.1 :=
  pullback.lift_fst _ _ _

@[scoped simp, reassoc] theorem kerLift_str {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (n : ℕ) (P : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) : kerLift L n P hP ≫ L.schemeKerStr n = t :=
  pullback.lift_snd _ _ _

end Kernel

section Level

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
variable (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) (K : E.ExtraLevel ℓ)

def tautPt : SchemeHomOver (K.levK ≫ E.f) E.f := ⟨K.levK, rfl⟩

theorem tautPt_torsion : nsmulPt E.L (K.levK ≫ E.f) ℓ (tautPt E ℓ K) = E.L.one _ :=
  K.levK_torsion _ _ ⟨𝟙 _, Category.id_comp _⟩

def jK : K.K ⟶ E.L.schemeKer ℓ := kerLift E.L ℓ (tautPt E ℓ K) (tautPt_torsion E ℓ K)

@[scoped simp, reassoc] theorem jK_kerι : jK E ℓ K ≫ kerι E.L ℓ = K.levK := kerLift_kerι _ _ _ _

@[scoped simp, reassoc] theorem jK_str : jK E ℓ K ≫ E.L.schemeKerStr ℓ = K.levK ≫ E.f := kerLift_str _ _ _ _

scoped instance isClosedImmersion_jK : IsClosedImmersion (jK E ℓ K) := by
  haveI : IsClosedImmersion (jK E ℓ K ≫ kerι E.L ℓ) := by rw [jK_kerι]; exact K.levK_closed
  exact IsClosedImmersion.of_comp (jK E ℓ K) (kerι E.L ℓ)

variable (hℓ : IsUnit ((ℓ : ℕ) : S))

include hℓ in

theorem etale_levK_f : Etale (K.levK ≫ E.f) := by
  obtain ⟨-, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓ
  haveI := het
  haveI : FormallyUnramified (K.levK ≫ E.f) := by
    rw [← jK_str]
    exact MorphismProperty.comp_mem _ _ _ (inferInstance : FormallyUnramified (jK E ℓ K))
      (inferInstance : FormallyUnramified (E.L.schemeKerStr ℓ))
  haveI := K.levK_flat
  haveI := K.levK_finitePresentation
  exact Etale.of_formallyUnramified_of_flat _

include hℓ in

theorem isOpenImmersion_jK : IsOpenImmersion (jK E ℓ K) := by
  obtain ⟨-, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E ℓ hℓ
  haveI := het
  haveI : Etale (jK E ℓ K ≫ E.L.schemeKerStr ℓ) := by rw [jK_str]; exact etale_levK_f E ℓ K hℓ
  haveI : Etale (jK E ℓ K) := Etale.of_comp (jK E ℓ K) (E.L.schemeKerStr ℓ)
  haveI : Mono (jK E ℓ K) := by
    haveI := K.levK_closed
    exact mono_of_mono_fac (jK_kerι E ℓ K)
  exact IsOpenImmersion.of_flat_of_mono _

include hℓ in

theorem factorsThrough_iff {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f) :
    FactorsThrough K.levK P ↔
      nsmulPt E.L t ℓ P = E.L.one t ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (τ : Spec (CommRingCat.of k) ⟶ T)
        (hτ : τ ≫ t = geomPoint k sk), FactorsThrough K.levK (schemeHomOverComp τ hτ P) := by
  constructor
  · intro hP
    refine ⟨K.levK_torsion t P hP, fun k _ _ sk τ hτ => ?_⟩
    obtain ⟨P₀, hP₀⟩ := hP
    exact ⟨τ ≫ P₀, by rw [Category.assoc, hP₀]; rfl⟩
  · rintro ⟨htor, hgeom⟩
    haveI := isOpenImmersion_jK E ℓ K hℓ
    let P' : T ⟶ E.L.schemeKer ℓ := kerLift E.L ℓ P htor

    have hrange : Set.range P'.base ⊆ Set.range (jK E ℓ K).base := by
      rintro _ ⟨τ₀, rfl⟩
      let τ := geomPtAt T τ₀
      let sk := ringHomOf (τ ≫ t)
      have hτ : τ ≫ t = geomPoint _ sk := (geomPoint_ringHomOf (τ ≫ t)).symm
      obtain ⟨Q₀, hQ₀⟩ := hgeom _ sk τ hτ

      have heq : τ ≫ P' = Q₀ ≫ jK E ℓ K := by
        apply pullback.hom_ext
        · show (τ ≫ P') ≫ kerι E.L ℓ = (Q₀ ≫ jK E ℓ K) ≫ kerι E.L ℓ
          rw [Category.assoc, Category.assoc, jK_kerι, hQ₀, kerLift_kerι]
          rfl
        · show (τ ≫ P') ≫ E.L.schemeKerStr ℓ = (Q₀ ≫ jK E ℓ K) ≫ E.L.schemeKerStr ℓ
          rw [Category.assoc, Category.assoc, jK_str, kerLift_str, ← Category.assoc, hQ₀]
          show τ ≫ t = (schemeHomOverComp τ hτ P).1 ≫ E.f
          rw [(schemeHomOverComp τ hτ P).2, hτ]
      have hpt : P'.base τ₀ = (τ ≫ P').base (IsLocalRing.closedPoint _) := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, geomPtAt_apply]
      rw [hpt, heq]
      exact ⟨Q₀.base _, by rw [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]⟩
    refine ⟨IsOpenImmersion.lift (jK E ℓ K) P' hrange, ?_⟩
    rw [← jK_kerι E ℓ K, ← Category.assoc, IsOpenImmersion.lift_fac, kerLift_kerι]

end Level

end ExtraLevelUniqBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit.ExtraLevelUniqBody"

open ExtraLevelUniqBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (ℓ : ℕ) (hℓ : IsUnit ((ℓ : ℕ) : S)) (K : E.ExtraLevel ℓ) :
    Etale (K.levK ≫ E.f) ∧
    ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
      FactorsThrough K.levK P ↔
        nsmulPt E.L t ℓ P = E.L.one t ∧
        ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k) (τ : Spec (CommRingCat.of k) ⟶ T)
          (hτ : τ ≫ t = geomPoint k sk), FactorsThrough K.levK (schemeHomOverComp τ hτ P) :=
  ⟨etale_levK_f E ℓ K hℓ, fun t P => factorsThrough_iff E ℓ K hℓ t P⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit.ExtraLevelUniqBody"

end S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_ExtraLevel_etale_and_forall_factorsThrough_iff_of_isUnit (solution)
