-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/ed1cffd0-0627-55ce-867f-1990099a3565

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_isPullback_iff_ptF_eq_specMap_comp_ptF
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_FullLevel_existsUnique_comp_eq_specMap_comp_of_isNilpotent_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing

namespace P2mWs2Ta

theorem ringHom_padicInt_ext_of_isNilpotent {q : ℕ} [Fact q.Prime] {A : Type} [CommRing A]
    (hq : IsNilpotent ((q : ℕ) : A)) (φ ψ : ℤ_[q] →+* A) : φ = ψ := by
  have key : ∀ (n : ℕ) (x : ℤ_[q]), φ x - ψ x ∈ (Ideal.span {((q : ℕ) : A)}) ^ n := by
    intro n
    induction n with
    | zero => intro x; rw [pow_zero, Ideal.one_eq_top]; trivial
    | succ n ih =>
      intro x
      have hx : x - (PadicInt.zmodRepr x : ℤ_[q]) ∈ Ideal.span {(q : ℤ_[q])} := by
        rw [← PadicInt.maximalIdeal_eq_span_p]; exact PadicInt.sub_zmodRepr_mem x
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hx
      have hx' : x = (PadicInt.zmodRepr x : ℤ_[q]) + r * (q : ℤ_[q]) := by rw [hr]; ring
      have h1 : φ x - ψ x = ((q : ℕ) : A) * (φ r - ψ r) := by
        rw [hx', map_add, map_add, map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast]; ring
      rw [h1, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span rfl) (ih r)
  obtain ⟨N, hN⟩ := hq
  ext x
  have := key N x
  rw [Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.mem_bot] at this
  exact sub_eq_zero.mp this

end P2mWs2Ta

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
    (ψ : M.presheaf.stalk y →+* A) (hψ : resA.comp ψ = xbar) :
    ∃ (u : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A),
      FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g ∧
      (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1 ∧
      (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y) := by
  classical

  have hkerA : RingHom.ker resA = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resA hs)
  have hqA : ((q : ℕ) : A) ∈ maximalIdeal A := by
    rw [← hkerA, RingHom.mem_ker]
    have : ((q : ℕ) : A) = algebraMap O A (algebraMap ℤ_[q] O (q : ℤ_[q])) := by
      rw [map_natCast, map_natCast]
    rw [this, ← RingHom.comp_apply, hc]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hqO
  have hnilA : IsNilpotent (maximalIdeal A) := by
    rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]; exact IsArtinianRing.isNilpotent_jacobson_bot
  have hqnil : IsNilpotent ((q : ℕ) : A) := by
    obtain ⟨n, hn⟩ := hnilA
    exact ⟨n, by have := Ideal.pow_mem_pow hqA n; rw [hn] at this; exact (Submodule.mem_bot A).mp this⟩

  set sA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ℤ_[q]) :=
    Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O))) with hsA
  set s₀ : Spec (CommRingCat.of (ResidueField O)) ⟶ Spec (CommRingCat.of ℤ_[q]) :=
    Spec.map (CommRingCat.ofHom ((residue O).comp (algebraMap ℤ_[q] O))) with hs₀
  have hss : Spec.map (CommRingCat.ofHom resA) ≫ sA = s₀ := by
    rw [hsA, hs₀, ← Spec.map_comp]; congr 1
    rw [← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hc]

  set x : Spec (CommRingCat.of A) ⟶ M := Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y with hxdef
  have hx : x ≫ πM = sA := by
    rw [hxdef, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq']
    have h3 : StructureSheaf.toStalk ℤ_[q] (πM y) ≫ πM.stalkMap y ≫ CommRingCat.ofHom ψ =
        CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)) := by
      apply CommRingCat.hom_ext
      exact P2mWs2Ta.ringHom_padicInt_ext_of_isNilpotent hqnil _ _
    have h4 := congrArg Spec.map h3
    rw [Spec.map_comp, Spec.map_comp] at h4
    rw [hsA, ← h4, Category.assoc]
    rfl

  obtain ⟨u, hu⟩ := hM.ptF_surjective A sA ⟨x, hx⟩

  have hred : FakeEllipticCurve.WithFullLevel.IsPullback resA u u₀ := by
    rw [CerednikDrinfeld.QM.IsFineModuli.isPullback_iff_ptF_eq_specMap_comp_ptF hM A (ResidueField O) resA sA s₀ hss u u₀,
      hu₀, hu]
    show Spec.map (CommRingCat.ofHom xbar) ≫ M.fromSpecStalk y = Spec.map (CommRingCat.ofHom resA) ≫ x
    rw [hxdef]
    exact ((AlgebraicGeometry.Scheme.existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
      M y (ResidueField O) xbar hxbar A resA hs).1 ψ hψ).symm
  obtain ⟨g, hg, hmul, hact, hlev, hP⟩ := hred
  refine ⟨u, g, ⟨hg, hmul, hact, hlev⟩, hP, ?_⟩
  rw [hu]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_ptF_eq_of_ringHom_stalk (solution)
