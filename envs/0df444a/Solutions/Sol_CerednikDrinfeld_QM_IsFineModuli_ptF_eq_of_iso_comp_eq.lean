-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.ptF_eq_of_iso_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1a511f7c-b55f-5cca-9033-80e0619cd10a

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_exists_P_eq_mapPt
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_ptF_eq_of_iso_comp_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing

namespace TA4Aux
open IsLocalRing

theorem isUnit_natCast {q : ℕ} [Fact q.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
    (m : ℕ) (hqm : ¬ q ∣ m) : IsUnit ((m : ℕ) : A) := by

  have hq0 : ((q : ℕ) : ResidueField O) = 0 := by
    have : residue O (algebraMap ℤ_[q] O (q : ℤ_[q])) = 0 := (residue_eq_zero_iff _).mpr hqO
    rwa [map_natCast, map_natCast] at this

  obtain ⟨p, hp⟩ := CharP.exists (ResidueField O)
  have hpq : p = q := by
    have hdvd : p ∣ q := (CharP.cast_eq_zero_iff (ResidueField O) p q).mp hq0
    rcases (Nat.dvd_prime (Fact.out : q.Prime)).mp hdvd with h1 | h2
    · exact absurd h1 (CharP.char_ne_one (ResidueField O) p)
    · exact h2
  subst hpq
  have hm0 : ((m : ℕ) : ResidueField O) ≠ 0 := fun h => hqm ((CharP.cast_eq_zero_iff (ResidueField O) p m).mp h)

  by_contra hu
  apply hm0
  have hmem : ((m : ℕ) : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hu
  have hker : RingHom.ker resA = maximalIdeal A :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resA hs)
  have : resA (m : A) = 0 := by rw [← RingHom.mem_ker, hker]; exact hmem
  rwa [map_natCast] at this

end TA4Aux

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (m : ℕ) (hm : 3 ≤ m) (hqm : ¬ q ∣ m)
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℤ_[q]))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of ℤ_[q])),
      FakeEllipticCurve.WithFullLevel Λ 1 m S → SchemeHomOver s πM)
    (hM : IsFineModuli Λ 1 m M πM ptF)
    (y : M)

    (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[q] O]
    (hqO : algebraMap ℤ_[q] O (q : ℤ_[q]) ∈ maximalIdeal O) [IsAlgClosed (ResidueField O)]

    (xbar : M.presheaf.stalk y →+* ResidueField O)
    (hxbar : RingHom.ker xbar = maximalIdeal (M.presheaf.stalk y))

    (u₀ : FakeEllipticCurve.WithFullLevel Λ 1 m (ResidueField O))
    (hu₀ : (ptF (ResidueField O) (Spec.map (CommRingCat.ofHom ((residue O).comp (algebraMap ℤ_[q] O)))) u₀).1 =
      Spec.map (CommRingCat.ofHom xbar) ≫ M.fromSpecStalk y)

    (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
    (resA : A →+* ResidueField O) (hs : Function.Surjective resA) (hc : resA.comp (algebraMap O A) = residue O)
    (u u' : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A) (g' : u₀.1.A ⟶ u'.1.A)
    (hg : FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g) (hP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1)
    (hg' : FakeEllipticCurve.IsPullbackVia resA u'.1 u₀.1 g') (hP' : (u₀.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom resA) ≫ (u'.2.P).1)
    (e : u.1.A ≅ u'.1.A) (hge : g ≫ e.hom = g') (he : e.hom ≫ u'.1.f = u.1.f)
    (hmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P Q : SchemeHomOver t u.1.f),
      mapPt e.hom he (u.1.L.mul t P Q) = u'.1.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q))
    (hact : ∀ x : ↥Λ, u.1.act x ≫ e.hom = e.hom ≫ u'.1.act x)
    (hlev : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of A)) (P : SchemeHomOver t u.1.f),
      FactorsThrough u.1.lev P ↔ FactorsThrough u'.1.lev (mapPt e.hom he P)) :
    (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u').1 := by
  classical
  obtain ⟨hpb', hmul', hact', -⟩ := hg'

  obtain ⟨P', hP'e⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.exists_P_eq_mapPt u.1 u'.1 e he hmul hact u.2

  have h1 : (u₀.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom resA) ≫ (P'.P).1 := by
    rw [hP'e, show (mapPt e.hom he u.2.P).1 = (u.2.P).1 ≫ e.hom from rfl, ← Category.assoc, ← hP, Category.assoc, hge]

  have hmA : IsUnit ((m : ℕ) : A) := TA4Aux.isUnit_natCast O hqO A resA hs m hqm
  have hnil : IsNilpotent (RingHom.ker resA) := by
    rw [IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resA hs), ← IsLocalRing.jacobson_eq_maximalIdeal ⊥]
    · exact IsArtinianRing.isNilpotent_jacobson_bot
    · exact bot_ne_top
  have huniq := CerednikDrinfeld.QM.FakeEllipticCurve.FullLevel.existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker u'.1 u₀.1 m hmA
    resA hs hnil g' hpb' hmul' hact' u₀.2
  have hPeq : P' = u'.2 := huniq.unique h1 hP'

  have hiso : FakeEllipticCurve.WithFullLevel.Iso u u' :=
    ⟨e, he, hmul, hact, hlev, by rw [← hP'e, hPeq]⟩
  exact congrArg Subtype.val (hM.ptF_iso A _ u u' hiso)

end S_CerednikDrinfeld_QM_IsFineModuli_ptF_eq_of_iso_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_ptF_eq_of_iso_comp_eq (solution)
