-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_lift_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a66fd670-2904-5a50-9f65-6070ac7bc7db

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isFinite_and_etale_schemeKerStr_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker.CerednikDrinfeld.QM NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.FullLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.FullLevel nsmulPt FakeEllipticCurve FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit"
namespace LevelEtaleUniqueGen
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

universe u

section Yoneda

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S))
    (n : ℕ) (x : SchemeHomOver t f) : nsmulPt L t n x = L.nsmul t n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show L.mul t (nsmulPt L t n x) x = L.mul t (L.nsmul t n x) x
      rw [ih]

theorem coe_nsmul_eq_comp_schemeNsmul (L : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (L.nsmul t n x).1 = x.1 ≫ L.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem coe_nsmulPt (L : RelativeGroupLaw S f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    (nsmulPt L t n x).1 = x.1 ≫ L.schemeNsmul n := by
  rw [nsmulPt_eq_nsmul, coe_nsmul_eq_comp_schemeNsmul]

end Yoneda

theorem isNilpotent_ker_specMap {S S₀ : Type u} [CommRing S] [CommRing S₀] (p : S →+* S₀)
    (hI : IsNilpotent (RingHom.ker p)) :
    IsNilpotent (Spec.map (CommRingCat.ofHom p)).ker := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change (Spec.map (CommRingCat.ofHom p)).ker ^ n = ⊥
  refine le_bot_iff.mp (Scheme.IdealSheafData.le_of_isAffine ?_)
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot,
    Pi.bot_apply]
  set e : Γ(Spec (CommRingCat.of S), ⊤) →+* S := (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom with he
  have hnat := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom p)
  have hle : RingHom.ker ((Spec.map (CommRingCat.ofHom p)).app ⊤).hom ≤ Ideal.comap e (RingHom.ker p) := by
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    have ha' : (Spec.map (CommRingCat.ofHom p)).appTop a = 0 := ha
    have h1 : p (e a) = (Scheme.ΓSpecIso (CommRingCat.of S₀)).hom ((Spec.map (CommRingCat.ofHom p)).appTop a) := by
      have h2 := congrArg (fun φ => φ.hom a) hnat
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h2
      rw [he]
      exact h2.symm
    rw [h1, ha', map_zero]
  have hinj : Function.Injective e := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1
  have hker : RingHom.ker e = ⊥ := (RingHom.injective_iff_ker_eq_bot e).mp hinj
  calc RingHom.ker ((Spec.map (CommRingCat.ofHom p)).app ⊤).hom ^ n
      ≤ (Ideal.comap e (RingHom.ker p)) ^ n := Ideal.pow_right_mono hle n
    _ ≤ Ideal.comap e (RingHom.ker p ^ n) := Ideal.le_comap_pow e n
    _ = Ideal.comap e ⊥ := by rw [hn]; rfl
    _ = ⊥ := by rw [← RingHom.ker_eq_comap_bot, hker]

theorem fullLevel_ext {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E : FakeEllipticCurve Λ N S} {m : ℕ} {P P' : E.FullLevel m} (h : P.P = P'.P) : P = P' := by
  cases P
  cases P'
  cases h
  rfl

theorem eq_of_nsmulPt_eq_one_of_comp_eq {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : FakeEllipticCurve Λ N S) (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    {Z : Scheme.{0}} (i : Z ⟶ Spec (CommRingCat.of S)) [IsClosedImmersion i] (hi : IsNilpotent i.ker)
    (P P' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) E.f)
    (hP : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P = E.L.one (𝟙 (Spec (CommRingCat.of S))))
    (hP' : nsmulPt E.L (𝟙 (Spec (CommRingCat.of S))) m P' = E.L.one (𝟙 (Spec (CommRingCat.of S))))
    (h : i ≫ P.1 = i ≫ P'.1) : P = P' := by
  obtain ⟨-, het⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.isFinite_and_etale_schemeKerStr_of_isUnit E m hm
  haveI := het

  have hPm : P.1 ≫ E.L.schemeNsmul m =
      𝟙 (Spec (CommRingCat.of S)) ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [← coe_nsmulPt, hP, Category.id_comp]
  have hP'm : P'.1 ≫ E.L.schemeNsmul m =
      𝟙 (Spec (CommRingCat.of S)) ≫ (E.L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    rw [← coe_nsmulPt, hP', Category.id_comp]
  have hu : pullback.lift P.1 (𝟙 (Spec (CommRingCat.of S))) hPm =
      pullback.lift P'.1 (𝟙 (Spec (CommRingCat.of S))) hP'm := by
    refine FormallyUnramified.hom_ext i hi (E.L.schemeKerStr m) ?_ ?_
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst, h]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
    · change pullback.lift P.1 (𝟙 (Spec (CommRingCat.of S))) hPm ≫ pullback.snd _ _ =
        pullback.lift P'.1 (𝟙 (Spec (CommRingCat.of S))) hP'm ≫ pullback.snd _ _
      rw [pullback.lift_snd, pullback.lift_snd]
  apply Subtype.ext
  calc P.1 = pullback.lift P.1 (𝟙 (Spec (CommRingCat.of S))) hPm ≫ pullback.fst _ _ := (pullback.lift_fst _ _ _).symm
    _ = pullback.lift P'.1 (𝟙 (Spec (CommRingCat.of S))) hP'm ≫ pullback.fst _ _ := by rw [hu]
    _ = P'.1 := pullback.lift_fst _ _ _

end CerednikDrinfeld.QM.LevelEtaleUniqueGen

open CerednikDrinfeld.QM.LevelEtaleUniqueGen in

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (m : ℕ)
    (S S₀ : Type) [CommRing S] [CommRing S₀] [Algebra S S₀]
    (hπ : Function.Surjective (algebraMap S S₀)) (hker : IsNilpotent (RingHom.ker (algebraMap S S₀)))
    (hm : IsUnit ((m : ℕ) : S))
    (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom (algebraMap S S₀))))
    (hg_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hg_act : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (P₀ : E₀.FullLevel m) :
    ∃! P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom (algebraMap S S₀)) ≫ (P.P).1 := by

  obtain ⟨P, hP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker
      E E₀ m hm (algebraMap S S₀) hπ hker g hg hg_mul hg_act P₀
  refine ⟨P, hP, fun P' hP' => ?_⟩

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap S S₀))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hk := isNilpotent_ker_specMap (algebraMap S S₀) hker
  have hPP' : P'.P = P.P :=
    eq_of_nsmulPt_eq_one_of_comp_eq E m hm (Spec.map (CommRingCat.ofHom (algebraMap S S₀))) hk
      P'.P P.P P'.torsion P.torsion (by rw [← hP', ← hP])
  exact fullLevel_ext hPP'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_lift_of_isNilpotent_ker (solution)
