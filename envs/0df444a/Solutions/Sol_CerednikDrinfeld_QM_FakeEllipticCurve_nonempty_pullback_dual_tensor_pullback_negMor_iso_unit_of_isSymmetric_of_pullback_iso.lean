-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e33ec66d-4729-5d2b-8d3c-29f60b916a71

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_negMor_eq_negMor_comp_of_compatible_univ
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Polarisation_locIsoOnBase_iff_nonempty_iso_of_isLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)

    (R₁ R₀ : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁]
    [CommRing R₀] [Nontrivial R₀] [Algebra S R₁] [Algebra S R₀]
    (φ : R₁ →ₐ[S] R₀) (hφ : Function.Surjective φ)
    (hsmall : ∀ x ∈ RingHom.ker φ.toRingHom, ∀ m ∈ IsLocalRing.maximalIdeal R₁, x * m = 0)

    (t : pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
    (ht₁ : t ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
    (ht₂ : t ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))

    (L₁ : RelativeGroupLaw R₁ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))))
    (hL₁ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₁))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))),
        (L₁.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₁))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (L₀ : RelativeGroupLaw R₀ (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))))
    (hL₀ : ∀ (T : Scheme) (t' : T ⟶ Spec (CommRingCat.of R₀))
        (P Q : SchemeHomOver t' (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))),
        (L₀.mul t' P Q).1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))) =
          (E.L.mul (t' ≫ (Spec.map (CommRingCat.ofHom (algebraMap S R₀))))
            ⟨P.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀))), by rw [Category.assoc, pullback.condition, ← Category.assoc, Q.2]⟩).1)
    (h2 : IsUnit (2 : R₁))
    (𝓛₀ : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))).Modules) (h𝓛₀ : Scheme.Modules.IsInvertible 𝓛₀) (hsym₀ : IsSymmetric (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) L₀ 𝓛₀)
    (𝓛₁' : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))).Modules) (hinv₁' : Scheme.Modules.IsInvertible 𝓛₁') (hiso' : Nonempty ((Scheme.Modules.pullback t).obj 𝓛₁' ≅ 𝓛₀)) :
    Nonempty ((Scheme.Modules.pullback t).obj
        (Scheme.Modules.dual 𝓛₁' ⊗ (Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj 𝓛₁') ≅ 𝟙_ _) := by
  classical
  have hφc : φ.toRingHom.comp (algebraMap S R₁) = algebraMap S R₀ := RingHom.ext fun x => φ.commutes x
  haveI : IsLocalRing R₀ := IsLocalRing.of_surjective' φ.toRingHom hφ

  have hcomm := RelativeGroupLaw.comp_negMor_eq_negMor_comp_of_compatible_univ E.L R₁ R₀ φ.toRingHom hφc L₁ L₀ hL₁ hL₀ t ht₁ ht₂
  obtain ⟨e⟩ := hiso'

  obtain ⟨es⟩ := (locIsoOnBase_iff_nonempty_iso_of_isLocalRing (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₀)))) _ _).1 hsym₀

  obtain ⟨-, ⟨eLd⟩⟩ := Scheme.Modules.IsInvertible.dual_monoidalV2 hinv₁'

  have e1 : (Scheme.Modules.pullback t).obj ((Scheme.Modules.pullback (negMor (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R₁)))) L₁)).obj 𝓛₁') ≅
      (Scheme.Modules.pullback t).obj 𝓛₁' :=
    (Scheme.Modules.pullbackComp t _).app 𝓛₁' ≪≫ (Scheme.Modules.pullbackCongr hcomm).app 𝓛₁' ≪≫
      ((Scheme.Modules.pullbackComp _ t).app 𝓛₁').symm ≪≫ (Scheme.Modules.pullback _).mapIso e ≪≫ es ≪≫ e.symm
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ e1) ≪≫
    (Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback t).mapIso (β_ _ _ ≪≫ eLd) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso _⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_nonempty_pullback_dual_tensor_pullback_negMor_iso_unit_of_isSymmetric_of_pullback_iso (solution)
