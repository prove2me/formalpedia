-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/2004b6e4-5162-564a-a8ab-5f4d1a7c8d9c

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_AdicThickening
import Theorems.Thm_AlgebraicGeometry_exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_pullback_iso_of_affHom_pushforward_adicThickening_surjective_ker_eq_pow_smul_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open scoped TensorProduct Quaternion
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

set_option maxHeartbeats 6400000 in
theorem solution
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (N : ℕ) (S : Type) [CommRing S] (E : FakeEllipticCurve Λ N S)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] [Algebra S R]

    (j : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))
    (hj₁ : ∀ k, j k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hj₂ : ∀ k, j k ≫ pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))) =
      pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (t : ∀ k : ℕ, pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))) ⟶ pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))))
    (ht₁ : ∀ k, t k ≫ pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1 + 1))))) = pullback.fst E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)

    (𝓛k : ∀ k : ℕ, (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)))))).Modules)
    (hinv : ∀ k, Scheme.Modules.IsInvertible (𝓛k k))
    (hcompat : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (t k)).obj (𝓛k (k + 1)) ≅ 𝓛k k))

    (hGE : ∀ (F : ℕ → AlgebraicGeometry.OModulePresheaf (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))))
      (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
      (φ : ∀ k, AlgebraicGeometry.OModulePresheaf.AffHom (F (k + 1)) (F k))
      (hφs : ∀ (k : ℕ) (U : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).affineOpens), Function.Surjective ((φ k).app U))
      (hφk : ∀ (k : ℕ) (U : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).affineOpens),
        LinearMap.ker ((φ k).app U) =
          IsLocalRing.maximalIdeal R ^ (k + 1) • (⊤ : Submodule R ((F (k + 1)).obj U.1))),
      ∃ (G : AlgebraicGeometry.OModulePresheaf (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R))))) (ψ : ∀ k, AlgebraicGeometry.OModulePresheaf.AffHom G (F k)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ (k : ℕ) (U : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).affineOpens), Function.Surjective ((ψ k).app U)) ∧
        (∀ (k : ℕ) (U : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).affineOpens),
          LinearMap.ker ((ψ k).app U) = IsLocalRing.maximalIdeal R ^ (k + 1) • (⊤ : Submodule R (G.obj U.1))) ∧
        (∀ (k : ℕ) (U : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U)) :
    ∃ 𝓛 : (pullback E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))).Modules,
      Scheme.Modules.IsInvertible 𝓛 ∧ ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓛 ≅ 𝓛k k) := by
  obtain ⟨L, hL, hLc, hback⟩ := AlgebraicGeometry.exists_isInvertible_adicThickening_forall_nonempty_pullback_iso_of_forall_pullback_algebraMap_quotient (IsLocalRing.maximalIdeal R) E.f j hj₁ hj₂ t ht₁ ht 𝓛k hinv hcompat
  obtain ⟨hcoh, hqc, φ, hφs, hφk⟩ := AlgebraicGeometry.OModulePresheaf.exists_affHom_pushforward_ofModules_adicThickening_surjective_ker_eq_pow_smul_top (IsLocalRing.maximalIdeal R) (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L hL hLc
  obtain ⟨G, ψ, hGc, hGq, hψs, hψk, -⟩ := hGE _ hcoh hqc φ hφs hφk
  haveI : IsProper E.f := E.bundle.proper
  haveI : IsProper (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) := inferInstance
  have hI : IsLocalRing.maximalIdeal R ≤ (⊥ : Ideal R).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  obtain ⟨M, hM, hMn⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_pullback_iso_of_affHom_pushforward_adicThickening_surjective_ker_eq_pow_smul_top (IsLocalRing.maximalIdeal R) hI (pullback.snd E.f (Spec.map (CommRingCat.ofHom (algebraMap S R)))) L hL G hGc hGq ψ hψs hψk
  exact ⟨M, hM, hback M hMn⟩

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isInvertible_pullback_iso_of_forall_thickening_of_forall_exists_isCoherent (solution)
