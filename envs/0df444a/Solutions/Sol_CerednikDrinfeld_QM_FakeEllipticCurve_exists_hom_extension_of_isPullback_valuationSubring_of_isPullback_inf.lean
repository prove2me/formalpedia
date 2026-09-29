-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/095e71f1-958a-5278-9a17-275770a7e06f

import Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_genericFibre_squares_of_isPullback_inf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_levelRaise_squares_of_isPullback_inf
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_intermediateField_forall_hom_of_isPullback_algebraMap
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_inf_toSubring_of_ne_top
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.QM.FakeEllipticCurve
open scoped Quaternion

namespace E1Asm

def jOf (O : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(O.toSubring ⊓ K.toSubring) →+* ↥K where
  toFun x := ⟨(x : AlgebraicClosure ℚ), (Subring.mem_inf.mp x.2).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem jOf_coe (O : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(O.toSubring ⊓ K.toSubring)) : ((jOf O K x : ↥K) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := rfl

def iOf (O : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ↥(O.toSubring ⊓ K.toSubring) →+* ↥O where
  toFun x := ⟨(x : AlgebraicClosure ℚ), (Subring.mem_inf.mp x.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem iOf_coe (O : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(O.toSubring ⊓ K.toSubring)) : ((iOf O K x : ↥O) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := rfl

end E1Asm

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (O : ValuationSubring (AlgebraicClosure ℚ))
    (𝒜 𝒟 : FakeEllipticCurve Λ N ↥O) (E d : FakeEllipticCurve Λ N (AlgebraicClosure ℚ))

    (K' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K']
    (ι₀ : ↥(O.toSubring ⊓ K'.toSubring) →+* ↥O) (hι₀ : ∀ x : ↥(O.toSubring ⊓ K'.toSubring), (ι₀ x : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ))
    (𝒜₀ 𝒟₀ : FakeEllipticCurve Λ N ↥(O.toSubring ⊓ K'.toSubring))
    (h𝒜₀ : FakeEllipticCurve.IsPullback ι₀ 𝒜₀ 𝒜) (h𝒟₀ : FakeEllipticCurve.IsPullback ι₀ 𝒟₀ 𝒟)
    (gE : E.A ⟶ 𝒜.A) (hgE : CategoryTheory.IsPullback gE E.f 𝒜.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgE_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' E.f),
      (E.L.mul t' P Q).1 ≫ gE =
        (𝒜.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gE, by rw [Category.assoc, hgE.w, ← Category.assoc, Q.2]⟩).1)
    (hgE_act : ∀ x : ↥Λ, E.act x ≫ gE = gE ≫ 𝒜.act x)
    (gd : d.A ⟶ 𝒟.A) (hgd : CategoryTheory.IsPullback gd d.f 𝒟.f (Spec.map (CommRingCat.ofHom O.subtype)))
    (hgd_mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t' d.f),
      (d.L.mul t' P Q).1 ≫ gd =
        (𝒟.L.mul (t' ≫ Spec.map (CommRingCat.ofHom O.subtype))
          ⟨P.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ gd, by rw [Category.assoc, hgd.w, ← Category.assoc, Q.2]⟩).1)
    (hgd_act : ∀ x : ↥Λ, d.act x ≫ gd = gd ≫ 𝒟.act x)
    (φ : E.A ⟶ d.A) (hφ : φ ≫ d.f = E.f)
    (hφ_mul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (P Q : SchemeHomOver t E.f),
      mapPt φ hφ (E.L.mul t P Q) = d.L.mul t (mapPt φ hφ P) (mapPt φ hφ Q))
    (hφ_act : ∀ x : ↥Λ, E.act x ≫ φ = φ ≫ d.act x) :
    ∃ (Φ : 𝒜.A ⟶ 𝒟.A) (hΦ : Φ ≫ 𝒟.f = 𝒜.f),
      gE ≫ Φ = φ ≫ gd ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥O)) (P Q : SchemeHomOver t 𝒜.f),
        mapPt Φ hΦ (𝒜.L.mul t P Q) = 𝒟.L.mul t (mapPt Φ hΦ P) (mapPt Φ hΦ Q)) ∧
      (∀ x : ↥Λ, 𝒜.act x ≫ Φ = Φ ≫ 𝒟.act x) := by
  classical
  by_cases hOtop : O = ⊤
  ·
    have hbij : Function.Bijective O.subtype := ⟨Subtype.val_injective, fun x => ⟨⟨x, hOtop ▸ ValuationSubring.mem_top x⟩, rfl⟩⟩
    let eO : ↥O ≃+* AlgebraicClosure ℚ := RingEquiv.ofBijective O.subtype hbij
    haveI : IsIso (CommRingCat.ofHom O.subtype) :=
      (inferInstance : IsIso (eO.toCommRingCatIso).hom)
    haveI : IsIso (Spec.map (CommRingCat.ofHom O.subtype)) := inferInstance
    haveI : IsIso gE := hgE.isIso_fst_of_isIso
    let Φ : 𝒜.A ⟶ 𝒟.A := inv gE ≫ φ ≫ gd
    have hΦ : Φ ≫ 𝒟.f = 𝒜.f := by
      simp only [Φ, Category.assoc]
      rw [hgd.w, reassoc_of% hφ, ← hgE.w, IsIso.inv_hom_id_assoc]
    have hext : gE ≫ Φ = φ ≫ gd := by simp only [Φ, IsIso.hom_inv_id_assoc]
    obtain ⟨hmul, hact⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
        O 𝒜 𝒟 E d gE hgE hgE_mul hgE_act gd hgd hgd_mul hgd_act φ hφ hφ_mul hφ_act Φ hΦ hext
    exact ⟨Φ, hΦ, hext, hmul, hact⟩
  ·
    let j₀ := E1Asm.jOf O K'
    have hj₀ : ∀ x, ((j₀ x : ↥K') : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x => rfl
    obtain ⟨E₀, p𝒜, hp𝒜, g₀, hg₀, gE', hgE', hp𝒜_mul, hp𝒜_act, hg₀_mul, hg₀_act, hgE'_mul, hgE'_act, hcubeE⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf O K' ι₀ hι₀ j₀ hj₀ 𝒜₀ 𝒜 h𝒜₀ E gE hgE hgE_mul hgE_act
    obtain ⟨d₀, p𝒟, hp𝒟, g₀d, hg₀d, gd', hgd', hp𝒟_mul, hp𝒟_act, hg₀d_mul, hg₀d_act, hgd'_mul, hgd'_act, hcubed⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_genericFibre_squares_of_isPullback_inf O K' ι₀ hι₀ j₀ hj₀ 𝒟₀ 𝒟 h𝒟₀ d gd hgd hgd_mul hgd_act

    obtain ⟨Kφ, finKφ, hle, H⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_intermediateField_forall_hom_of_isPullback_algebraMap K' E₀ d₀ E d
        gE' hgE' hgE'_mul hgE'_act gd' hgd' hgd'_mul hgd'_act φ hφ hφ_mul hφ_act
    haveI := finKφ

    let j : ↥K' →+* ↥Kφ := (IntermediateField.inclusion hle).toRingHom
    have hj : ∀ x : ↥K', ((j x : ↥Kφ) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x => rfl
    let ι₁ := E1Asm.iOf O Kφ
    have hι₁ : ∀ x, ((ι₁ x : ↥O) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x => rfl
    let j₁ := E1Asm.jOf O Kφ
    have hj₁ : ∀ x, ((j₁ x : ↥Kφ) : AlgebraicClosure ℚ) = (x : AlgebraicClosure ℚ) := fun x => rfl
    obtain ⟨𝒜₁, E₂, p₁, hp₁, rE, hrE, hrE_mul, hrE_act, gE₂, hgE₂, hgE₂_mul, hgE₂_act, qE, hqE, hqE_mul, hqE_act, hrqE, hcube₁⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelRaise_squares_of_isPullback_inf O K' Kφ j hj ι₀ hι₀ j₀ hj₀ ι₁ hι₁ j₁ hj₁
        𝒜₀ 𝒜 E E₀ p𝒜 hp𝒜 g₀ hg₀ hg₀_mul hg₀_act gE hgE hgE_mul hgE_act gE' hgE' hgE'_mul hgE'_act hcubeE
    obtain ⟨𝒟₁, d₂, p₁d, hp₁d, rd, hrd, hrd_mul, hrd_act, gd₂, hgd₂, hgd₂_mul, hgd₂_act, qd, hqd, hqd_mul, hqd_act, hrqd, hcube₁d⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_levelRaise_squares_of_isPullback_inf O K' Kφ j hj ι₀ hι₀ j₀ hj₀ ι₁ hι₁ j₁ hj₁
        𝒟₀ 𝒟 d d₀ p𝒟 hp𝒟 g₀d hg₀d hg₀d_mul hg₀d_act gd hgd hgd_mul hgd_act gd' hgd' hgd'_mul hgd'_act hcubed

    obtain ⟨φ₂, hφ₂, hcomm₂, hom₂, act₂⟩ := H Kφ le_rfl j hj E₂ d₂ rE hrE hrE_mul hrE_act qE hqE hqE_mul hqE_act hrqE
      rd hrd hrd_mul hrd_act qd hqd hqd_mul hqd_act hrqd

    obtain ⟨hDVR, hfrac⟩ := ValuationSubring.isDiscreteValuationRing_inf_toSubring_of_ne_top O hOtop Kφ
    letI algR : Algebra ↥(O.toSubring ⊓ Kφ.toSubring) ↥Kφ := j₁.toAlgebra
    haveI : IsFractionRing ↥(O.toSubring ⊓ Kφ.toSubring) ↥Kφ := by
      rw [IsFractionRing, isLocalization_iff]
      have hinj : Function.Injective j₁ := fun x y h => Subtype.ext (by rw [← hj₁ x, ← hj₁ y, h])
      refine ⟨?_, ?_, ?_⟩
      · intro y
        exact isUnit_iff_ne_zero.mpr (fun h0 => nonZeroDivisors.ne_zero y.2 (hinj (by rw [map_zero]; exact h0)))
      · intro z
        obtain ⟨a', b', ha', hb', hb0, hz⟩ := hfrac (z : AlgebraicClosure ℚ) z.2
        refine ⟨⟨⟨a', ha'⟩, ⟨⟨b', hb'⟩, mem_nonZeroDivisors_of_ne_zero (fun h => hb0 (congrArg Subtype.val h))⟩⟩, ?_⟩
        apply Subtype.ext
        show (z : AlgebraicClosure ℚ) * ((j₁ ⟨b', hb'⟩ : ↥Kφ) : AlgebraicClosure ℚ) = ((j₁ ⟨a', ha'⟩ : ↥Kφ) : AlgebraicClosure ℚ)
        rw [hj₁, hj₁]; exact hz
      · intro x y h
        exact ⟨1, by rw [hinj h]⟩
    haveI := hDVR

    obtain ⟨Φ₁, hΦ₁, hext₁, hmul₁, hact₁⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.exists_hom_extension_of_isPullback_of_isDiscreteValuationRing
        (R := ↥(O.toSubring ⊓ Kφ.toSubring)) (K := ↥Kφ) 𝒜₁ 𝒟₁ E₂ d₂ gE₂ hgE₂ hgE₂_mul hgE₂_act gd₂ hgd₂ hgd₂_mul hgd₂_act
        φ₂ hφ₂ hom₂ act₂

    let Φ : 𝒜.A ⟶ 𝒟.A := hp₁d.lift (p₁ ≫ Φ₁) 𝒜.f (by rw [Category.assoc, hΦ₁]; exact hp₁.w)
    have hΦ : Φ ≫ 𝒟.f = 𝒜.f := hp₁d.lift_snd _ _ _
    have hΦp : Φ ≫ p₁d = p₁ ≫ Φ₁ := hp₁d.lift_fst _ _ _

    have hext : gE ≫ Φ = φ ≫ gd := by
      apply hp₁d.hom_ext
      · simp only [Category.assoc]
        rw [hΦp, reassoc_of% hcube₁, hext₁, reassoc_of% hcomm₂, hcube₁d]
      · rw [Category.assoc, hΦ, Category.assoc, hgd.w, ← Category.assoc, hφ, hgE.w]

    obtain ⟨hmul, hact⟩ :=
      CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_act_comp_of_comp_eq_of_isPullback_valuationSubring
        O 𝒜 𝒟 E d gE hgE hgE_mul hgE_act gd hgd hgd_mul hgd_act φ hφ hφ_mul hφ_act Φ hΦ hext
    exact ⟨Φ, hΦ, hext, hmul, hact⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_hom_extension_of_isPullback_valuationSubring_of_isPullback_inf (solution)
