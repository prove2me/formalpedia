-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e6328239-1772-5188-990d-0b23db795f0f

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullback_levelIff
import Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_isAtkinLehnerQuotient_of_isPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace GammaSol

theorem main
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N r : ℕ)

    (R : Type) [CommRing R] (𝒪₀ : Type) [CommRing 𝒪₀] (K : Type) [CommRing K] (C : Type) [CommRing C]
    (sbar : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (cK : K →+* C) (c₀ : 𝒪₀ →+* C)

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (ar : 𝒳₀ ⟶ 𝒳₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)

    (u : pullback πX (Spec.map (CommRingCat.ofHom cK) ≫ sbar) ≅ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C)) (E : FakeEllipticCurve Λ N S),
      pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).1 s
          (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).2 ≫ u.hom =
        pullback.lift (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).1 s
          (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).2)

    (aC : pullback f₀ (Spec.map (CommRingCat.ofHom c₀)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (haC₁ : aC ≫ pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) ≫ ar)
    (haC₂ : aC ≫ pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)))

    (E E' : FakeEllipticCurve Λ N K) (hEE' : FakeEllipticCurve.IsAtkinLehnerQuotient r E E') :
    (pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E).1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E).2, Category.id_comp]) ≫ u.hom) ≫ aC =
      pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E').1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E').2, Category.id_comp]) ≫ u.hom := by
  obtain ⟨EC, g, hg, hmul, hact, hlev, -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff cK E
  obtain ⟨EC', g', hg', hmul', hact', hlev', -⟩ := CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullback_levelIff cK E'
  have hP : FakeEllipticCurve.IsPullback cK E EC := ⟨g, hg, hmul, hact, hlev⟩
  have hP' : FakeEllipticCurve.IsPullback cK E' EC' := ⟨g', hg', hmul', hact', hlev'⟩
  have hAL : FakeEllipticCurve.IsAtkinLehnerQuotient r EC EC' :=
    CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_of_isPullback cK r E E' EC EC' hP hP' hEE'

  have ptC : ∀ (s₁ s₂ : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R)) (h : s₁ = s₂) (F : FakeEllipticCurve Λ N C),
      (pt C s₁ F).1 = (pt C s₂ F).1 := by
    intro s₁ s₂ h F; subst h; rfl
  have h1 := pt_pullback K C cK sbar (Spec.map (CommRingCat.ofHom cK) ≫ sbar) rfl E EC hP
  have h1' := pt_pullback K C cK sbar (Spec.map (CommRingCat.ofHom cK) ≫ sbar) rfl E' EC' hP'
  have hu := hupt C (𝟙 _) EC
  have hu' := hupt C (𝟙 _) EC'
  have hq := har C (𝟙 _ ≫ Spec.map (CommRingCat.ofHom c₀)) EC EC' hAL
  have eL : pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E).1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E).2, Category.id_comp]) =
      pullback.lift (pt C (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) EC).1 (𝟙 _)
        (pt C (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) EC).2 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst, ← h1]
      exact ptC _ _ (Category.id_comp _).symm EC
    · rw [pullback.lift_snd, pullback.lift_snd]
  have eL' : pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E').1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E').2, Category.id_comp]) =
      pullback.lift (pt C (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) EC').1 (𝟙 _)
        (pt C (𝟙 _ ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) EC').2 := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst, ← h1']
      exact ptC _ _ (Category.id_comp _).symm EC'
    · rw [pullback.lift_snd, pullback.lift_snd]
  rw [eL, eL', hu, hu']
  apply pullback.hom_ext
  · rw [Category.assoc, haC₁, ← Category.assoc, pullback.lift_fst, pullback.lift_fst, hq]
  · rw [Category.assoc, haC₂, pullback.lift_snd, pullback.lift_snd]

end GammaSol

theorem solution
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N r : ℕ)

    (R : Type) [CommRing R] (𝒪₀ : Type) [CommRing 𝒪₀] (K : Type) [CommRing K] (C : Type) [CommRing C]
    (sbar : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) (cK : K →+* C) (c₀ : 𝒪₀ →+* C)

    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of R))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of R)),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)

    (𝒳₀ : Scheme.{0}) (f₀ : 𝒳₀ ⟶ Spec (CommRingCat.of 𝒪₀))
    (pt₀ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)),
      FakeEllipticCurve Λ N S → SchemeHomOver s f₀)
    (ar : 𝒳₀ ⟶ 𝒳₀)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪₀)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt₀ S s E).1 ≫ ar = (pt₀ S s E').1)

    (u : pullback πX (Spec.map (CommRingCat.ofHom cK) ≫ sbar) ≅ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (hupt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of C)) (E : FakeEllipticCurve Λ N S),
      pullback.lift (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).1 s
          (pt S (s ≫ (Spec.map (CommRingCat.ofHom cK) ≫ sbar)) E).2 ≫ u.hom =
        pullback.lift (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).1 s
          (pt₀ S (s ≫ Spec.map (CommRingCat.ofHom c₀)) E).2)

    (aC : pullback f₀ (Spec.map (CommRingCat.ofHom c₀)) ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom c₀)))
    (haC₁ : aC ≫ pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.fst f₀ (Spec.map (CommRingCat.ofHom c₀)) ≫ ar)
    (haC₂ : aC ≫ pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)) = pullback.snd f₀ (Spec.map (CommRingCat.ofHom c₀)))

    (E E' : FakeEllipticCurve Λ N K) (hEE' : FakeEllipticCurve.IsAtkinLehnerQuotient r E E') :
    (pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E).1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E).2, Category.id_comp]) ≫ u.hom) ≫ aC =
      pullback.lift (Spec.map (CommRingCat.ofHom cK) ≫ (pt K sbar E').1) (𝟙 _)
        (by rw [Category.assoc, (pt K sbar E').2, Category.id_comp]) ≫ u.hom :=
  GammaSol.main Λ N r R 𝒪₀ K C sbar cK c₀ X πX pt pt_pullback 𝒳₀ f₀ pt₀ ar har u hupt aC haC₁ haC₂ E E' hEE'

end S_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_lift_pt_comp_atkinLehnerBaseChange_eq_of_isAtkinLehnerQuotient (solution)
