-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b7c93bb9-2ef3-53a7-88a8-f7d873dcb2d4

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Polarisation

open scoped Quaternion TensorProduct NumberField

namespace FecTowerStep

universe u

theorem mul_coe_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (h : t₁ = t₂)
    (P₁ Q₁ : SchemeHomOver t₁ f) (P₂ Q₂ : SchemeHomOver t₂ f) (hP : P₁.1 = P₂.1) (hQ : Q₁.1 = Q₂.1) :
    (L.mul t₁ P₁ Q₁).1 = (L.mul t₂ P₂ Q₂).1 := by
  subst h
  obtain rfl : P₁ = P₂ := Subtype.ext hP
  obtain rfl : Q₁ = Q₂ := Subtype.ext hQ
  rfl

end FecTowerStep

open FecTowerStep in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B₁ B₀ : Type) [CommRing B₁] [CommRing B₀] [Algebra B₁ B₀]
    (E : FakeEllipticCurve Λ N B₁) (E₀ : FakeEllipticCurve Λ N B₀) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (algebraMap B₁ B₀) E E₀ g)
    (K : Ideal B₁) (hK : ∀ x ∈ K, algebraMap B₁ B₀ x = 0) :
    ∃ (E' : FakeEllipticCurve Λ N (B₁ ⧸ K)) (g₁ : E'.A ⟶ E.A) (g₀ : E₀.A ⟶ E'.A),
      FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.mk K) E E' g₁ ∧
      FakeEllipticCurve.IsPullbackVia (Ideal.Quotient.lift K (algebraMap B₁ B₀) hK) E' E₀ g₀ ∧
      g₀ ≫ g₁ = g := by
  obtain ⟨E', g₁, hg₁, hom₁, act₁, lev₁, lev₁'⟩ :=
    CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff (Ideal.Quotient.mk K) E
  obtain ⟨hgpb, homg, actg, levg⟩ := hg
  set ψ : B₁ ⧸ K →+* B₀ := Ideal.Quotient.lift K (algebraMap B₁ B₀) hK with hψ
  have hfac : algebraMap B₁ B₀ = ψ.comp (Ideal.Quotient.mk K) :=
    RingHom.ext fun x => (Ideal.Quotient.lift_mk K (algebraMap B₁ B₀) hK).symm
  have hSpec : Spec.map (CommRingCat.ofHom (algebraMap B₁ B₀)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hfac]
  have w : g ≫ E.f =
      (E₀.f ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)) := by
    rw [Category.assoc, ← hSpec]; exact hgpb.w
  let g₀ : E₀.A ⟶ E'.A := hg₁.lift g (E₀.f ≫ Spec.map (CommRingCat.ofHom ψ)) w
  have hg₀g₁ : g₀ ≫ g₁ = g := hg₁.lift_fst _ _ _
  have hg₀f : g₀ ≫ E'.f = E₀.f ≫ Spec.map (CommRingCat.ofHom ψ) := hg₁.lift_snd _ _ _
  have hg₀pb : IsPullback g₀ E₀.f E'.f (Spec.map (CommRingCat.ofHom ψ)) := by
    refine IsPullback.of_right ?_ hg₀f hg₁
    rw [hg₀g₁, ← hSpec]; exact hgpb
  refine ⟨E', g₁, g₀, ⟨hg₁, hom₁, act₁, lev₁⟩, ⟨hg₀pb, ?_, ?_, ?_⟩, hg₀g₁⟩
  · intro T t' P Q
    apply hg₁.hom_ext
    · have e1 : ((E₀.L.mul t' P Q).1 ≫ g₀) ≫ g₁ = (E₀.L.mul t' P Q).1 ≫ g := by
        rw [Category.assoc, hg₀g₁]
      rw [e1, homg, hom₁]
      exact mul_coe_congr E.L (by rw [Category.assoc, ← hSpec]) _ _ _ _
        (by show P.1 ≫ g = (P.1 ≫ g₀) ≫ g₁; rw [Category.assoc, hg₀g₁])
        (by show Q.1 ≫ g = (Q.1 ≫ g₀) ≫ g₁; rw [Category.assoc, hg₀g₁])
    · rw [Category.assoc, hg₀f, ← Category.assoc, (E₀.L.mul t' P Q).2, (E'.L.mul _ _ _).2]
  · intro x
    apply hg₁.hom_ext
    · rw [Category.assoc, hg₀g₁, actg, Category.assoc, act₁, ← Category.assoc, hg₀g₁]
    · rw [Category.assoc, hg₀f, ← Category.assoc, E₀.act_over, Category.assoc, E'.act_over, hg₀f]
  · intro T t' P hP
    obtain ⟨P₀, hP₀⟩ := levg t' P hP
    exact lev₁' (t' ≫ Spec.map (CommRingCat.ofHom ψ))
      ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀f, ← Category.assoc, P.2]⟩
      ⟨P₀, by rw [hP₀, Category.assoc, hg₀g₁]⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_quotient_comp_eq_of_isPullbackVia_of_le_ker (solution)
