-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b7bce0fa-5b01-5993-8e10-74b28c94d0b6

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_WithFullLevel_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM IsLocalRing

namespace P2mWs2Ta5

theorem mul_val_congr {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
    {T : Scheme.{0}} {s₁ s₂ : T ⟶ Spec (CommRingCat.of S)} (h : s₁ = s₂)
    (P₁ Q₁ : SchemeHomOver s₁ f) (P₂ Q₂ : SchemeHomOver s₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul s₁ P₁ Q₁).1 = (L.mul s₂ P₂ Q₂).1 := by
  subst h
  obtain ⟨P₁, hP₁⟩ := P₁; obtain ⟨P₂, hP₂⟩ := P₂; obtain ⟨Q₁, hQ₁⟩ := Q₁; obtain ⟨Q₂, hQ₂⟩ := Q₂
  simp only at hP hQ
  subst hP; subst hQ
  rfl

end P2mWs2Ta5

open P2mWs2Ta5 in
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
    (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
    (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA') (hc' : resA'.comp (algebraMap O A') = residue O)
    (f : A →ₐ[O] A') (hf : resA'.comp f.toRingHom = resA)
    (u : FakeEllipticCurve.WithFullLevel Λ 1 m A) (g : u₀.1.A ⟶ u.1.A)
    (hg : FakeEllipticCurve.IsPullbackVia resA u.1 u₀.1 g) (hP : (u₀.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom resA) ≫ (u.2.P).1)
    (ψ : M.presheaf.stalk y →+* A) (hpt : (ptF A (Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O)))) u).1 = (Spec.map (CommRingCat.ofHom ψ) ≫ M.fromSpecStalk y)) :
    ∃ (u' : FakeEllipticCurve.WithFullLevel Λ 1 m A') (k : u'.1.A ⟶ u.1.A) (g' : u₀.1.A ⟶ u'.1.A),
      FakeEllipticCurve.IsPullbackVia f.toRingHom u.1 u'.1 k ∧
      FakeEllipticCurve.IsPullbackVia resA' u'.1 u₀.1 g' ∧
      g' ≫ k = g ∧
      (u₀.2.P).1 ≫ g' = Spec.map (CommRingCat.ofHom resA') ≫ (u'.2.P).1 ∧
      (ptF A' (Spec.map (CommRingCat.ofHom ((algebraMap O A').comp (algebraMap ℤ_[q] O)))) u').1 = (Spec.map (CommRingCat.ofHom (f.toRingHom.comp ψ)) ≫ M.fromSpecStalk y) := by

  obtain ⟨u', k, hk, hkmul, hkact, hklev, hklev', hkP⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.exists_isPullback_levelIff f.toRingHom u
  obtain ⟨hgc, hgmul, hgact, hglev⟩ := hg

  have hres : Spec.map (CommRingCat.ofHom resA') ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom resA) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hf]

  have hcompat : g ≫ u.1.f = (u₀.1.f ≫ Spec.map (CommRingCat.ofHom resA')) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
    rw [Category.assoc, hres]; exact hgc.w
  let g' : u₀.1.A ⟶ u'.1.A := hk.lift g (u₀.1.f ≫ Spec.map (CommRingCat.ofHom resA')) hcompat
  have hg'k : g' ≫ k = g := hk.lift_fst _ _ _
  have hg'f : g' ≫ u'.1.f = u₀.1.f ≫ Spec.map (CommRingCat.ofHom resA') := hk.lift_snd _ _ _

  have hbig : IsPullback (g' ≫ k) u₀.1.f u.1.f
      (Spec.map (CommRingCat.ofHom resA') ≫ Spec.map (CommRingCat.ofHom f.toRingHom)) := by
    rw [hg'k, hres]; exact hgc
  have hg'c : IsPullback g' u₀.1.f u'.1.f (Spec.map (CommRingCat.ofHom resA')) :=
    IsPullback.of_right hbig hg'f hk
  refine ⟨u', k, g', ⟨hk, hkmul, hkact, hklev⟩, ⟨hg'c, ?_, ?_, ?_⟩, hg'k, ?_, ?_⟩
  ·
    intro T t' P Q
    apply hk.hom_ext
    · rw [Category.assoc, hkmul]
      conv_lhs => rw [hg'k]
      rw [hgmul t' P Q]
      apply mul_val_congr
      · rw [Category.assoc, hres]
      · show P.1 ≫ g = (P.1 ≫ g') ≫ k
        rw [Category.assoc, hg'k]
      · show Q.1 ≫ g = (Q.1 ≫ g') ≫ k
        rw [Category.assoc, hg'k]
    · rw [Category.assoc, (u'.1.L.mul _ _ _).2, hg'f, ← Category.assoc, (u₀.1.L.mul t' P Q).2]
  ·
    intro x
    apply hk.hom_ext
    · rw [Category.assoc, hg'k, Category.assoc, hkact, ← Category.assoc, hg'k, hgact]
    · rw [Category.assoc, hg'f, ← Category.assoc, u₀.1.act_over, Category.assoc, u'.1.act_over, hg'f]
  ·
    intro T t' P hPl
    obtain ⟨P₁, hP₁⟩ := hglev t' P hPl
    have := hklev' (t' ≫ Spec.map (CommRingCat.ofHom resA'))
      ⟨P.1 ≫ g', by rw [Category.assoc, hg'f, ← Category.assoc, P.2]⟩ ⟨P₁, by rw [hP₁, ← hg'k, Category.assoc]⟩
    exact this
  ·
    apply hk.hom_ext
    · rw [Category.assoc, hg'k, hP, Category.assoc, hkP, ← Category.assoc, hres]
    · rw [Category.assoc, hg'f, ← Category.assoc, (u₀.2.P).2, Category.id_comp, Category.assoc, (u'.2.P).2,
        Category.comp_id]
  ·
    have hss' : Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap O A).comp (algebraMap ℤ_[q] O))) =
        Spec.map (CommRingCat.ofHom ((algebraMap O A').comp (algebraMap ℤ_[q] O))) := by
      have hfa : f.toRingHom.comp (algebraMap O A) = algebraMap O A' := RingHom.ext fun x => f.commutes x
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hfa]
    have hpb : FakeEllipticCurve.WithFullLevel.IsPullback f.toRingHom u u' :=
      ⟨k, hk, hkmul, hkact, hklev, hkP⟩
    rw [hM.ptF_pullback A A' f.toRingHom _ _ hss' u u' hpb, hpt, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]

end S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_exists_withFullLevel_isPullbackVia_comp_eq_ptF_eq_of_algHom (solution)
