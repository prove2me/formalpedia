-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/171469af-79bc-5dd7-ba04-f1773ef8b814

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_comp_eq_specMap_comp_of_isNilpotent_ker
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
p2m_open "CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker.CerednikDrinfeld CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker.CerednikDrinfeld.QM NeronModelInfra"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.FakeEllipticCurve.FullLevel QM.FakeEllipticCurve QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker QM.FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker"
namespace QM
p2m_export "CerednikDrinfeld.QM" "FakeEllipticCurve.FullLevel FakeEllipticCurve FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker"
namespace R4LevelEt
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

theorem fullLevel_ext {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    {E : FakeEllipticCurve Λ N S} {m : ℕ} {P P' : E.FullLevel m} (h : P.P = P'.P) : P = P' := by
  cases P
  cases P'
  cases h
  rfl

theorem isNilpotent_ker_specMap {S S₀ : Type} [CommRing S] [CommRing S₀] (p : S →+* S₀)
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

end CerednikDrinfeld.QM.R4LevelEt

open CerednikDrinfeld.QM.R4LevelEt in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S S₀ : Type} [CommRing S] [IsLocalRing S] [CommRing S₀]
    (E : FakeEllipticCurve Λ N S) (E₀ : FakeEllipticCurve Λ N S₀)
    (m : ℕ) (hm : IsUnit ((m : ℕ) : S))
    (p : S →+* S₀) (hp : Function.Surjective p) (hI : IsNilpotent (RingHom.ker p))
    (g : E₀.A ⟶ E.A) (hg : CategoryTheory.IsPullback g E₀.f E.f (Spec.map (CommRingCat.ofHom p)))
    (hmul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of S₀)) (P Q : SchemeHomOver t' E₀.f),
      (E₀.L.mul t' P Q).1 ≫ g =
        (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom p))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hact : ∀ x : ↥Λ, E₀.act x ≫ g = g ≫ E.act x)
    (P₀ : E₀.FullLevel m) :
    ∃! P : E.FullLevel m, (P₀.P).1 ≫ g = Spec.map (CommRingCat.ofHom p) ≫ (P.P).1 := by

  obtain ⟨P, hP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_comp_eq_specMap_comp_of_isNilpotent_ker
      E E₀ m hm p hp hI g hg hmul hact P₀
  refine ⟨P, hP, fun P' hP' => ?_⟩

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom p)) := IsClosedImmersion.spec_of_surjective _ hp
  have hker := isNilpotent_ker_specMap p hI
  have hPP' : P'.P = P.P :=
    CerednikDrinfeld.QM.FakeEllipticCurve.eq_of_nsmulPt_eq_one_of_comp_eq_of_isNilpotent_ker E m hm
      (Spec.map (CommRingCat.ofHom p)) hker (𝟙 (Spec (CommRingCat.of S))) P'.P P.P P'.torsion P.torsion
      (by rw [← hP', ← hP])
  exact fullLevel_ext hPP'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker (solution)
