-- Prove2me | solution 1 for AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/1b08070b-94c6-53f4-9ed3-faaeb68a1abb

import Theorems.Thm_Ideal_ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime
import Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
import Theorems.Thm_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "AutomorphicForm.SplitPlace.string_castSucc AutomorphicForm.SplitPlace.reindex_symm_apply AutomorphicForm.SplitPlace.psiLeft_apply AutomorphicForm.SplitPlace.psiHomeomorph_apply AutomorphicForm.SplitPlace.psiLinearEquiv_apply AutomorphicForm.SplitPlace.psiEquiv_apply AutomorphicForm.SplitPlace.psi_tmul AutomorphicForm.SplitPlace.psiLinear_apply AutomorphicForm.SplitPlace.coords_apply_val AutomorphicForm.SplitPlace.string_last AutomorphicForm.SplitPlace.psiGL_apply_val AutomorphicForm.SplitPlace.dedekindMatrix_apply AutomorphicForm.SplitPlace.reindex_apply AutomorphicForm.adeleArchAlgHom_apply AutomorphicForm.tensorPlaceHom_tmul AutomorphicForm.tensorArchHom_tmul AutomorphicForm.adelePlaceAlgHom_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply AutomorphicForm.gl2Weyl_val LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace WWRED

theorem isGalois_of_finrank_prime_of_ne_one (K L : Type) [Field K] [Field L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) : IsGalois K L := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
  apply IsGalois.of_fixedField_eq_bot
  have hcard : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
      Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    IntermediateField.finrank_fixedField_eq_card ⊤
  have htower := Module.finrank_mul_finrank K (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  have h2 : 1 < Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) := by
    rw [Subgroup.card_top]
    haveI : Nontrivial (L ≃ₐ[K] L) := ⟨⟨σ, 1, hσ⟩⟩
    exact Finite.one_lt_card
  have hdvd : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L ∣ Module.finrank K L :=
    Dvd.intro_left _ htower
  rcases (Nat.dvd_prime hprime).mp hdvd with h1 | hp
  · exfalso
    rw [hcard] at h1
    omega
  · apply IntermediateField.finrank_eq_one_iff.mp
    rw [hp] at htower
    exact (Nat.mul_eq_right hprime.ne_zero).mp htower

end WWRED

open AutomorphicForm in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hprime : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b)
    (α β : (L ⊗[K] v.adicCompletion K)ˣ)
    (hN : AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a b))
    (τ : @Measure (AutomorphicForm.localCentralizer K v (diagUnits2 a b))
      (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (diagUnits2 a b)) τ)
    (hτ1 : τ {t | (t : GL (Fin 2) (v.adicCompletion K)) ∈ AutomorphicForm.localIntegralSet K v} = 1)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)))
    (hτ' : @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈
      AutomorphicForm.semiLocalIntegralSet K L v} = 1)
    (J J' : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegral K v (diagUnits2 a b) τ
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ e ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j e *
            ∑ ι : Fin (e 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (e 1))⁻¹ * x))
      J)
    (hJ' : AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ'
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((AutomorphicForm.semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
              ((List.ofFn fun m => rL (ι m)).prod * z ^ j)))⁻¹ * x))
      J') :
    J' = (Module.finrank K L : ℂ) * J := by
  classical

  have hf : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1 ∨ v.asIdeal.inertiaDeg' (ws v).1.asIdeal = Module.finrank K L := by

    haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hprime.pos
    have hGal : IsGalois K L := WWRED.isGalois_of_finrank_prime_of_ne_one K L hprime σ hσ
    haveI := hGal
    haveI : (ws v).1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal (ws v).2).symm⟩
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    rcases Ideal.ncard_primesOver_ramificationIdx_inertiaDeg_trichotomy_of_isGalois_of_finrank_prime K L hprime v.asIdeal v.ne_bot (ws v).1.asIdeal with h | h | h
    · exact Or.inl h.2.2
    · exfalso
      have he := hv (ws v).1 (ws v).2
      rw [(ws v).2] at he
      rw [he] at h
      exact hprime.ne_one h.2.1.symm
    · exact Or.inr h.2.2
  rcases hf with hsplit | hinert
  · exact AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one
      K L hprime σ hσ v hv ws hsplit ϖ hϖ hϖ0 n rL hrL z hz ϖK hϖK hϖK0 nK rK hrK zK hzK k j a b hab α β hN τ hτ hτ1 τ' hτ' hτ'1 J J' hJ hJ'
  · exact AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_finrank
      K L hprime σ hσ v hv ws hinert ϖ hϖ hϖ0 n rL hrL z hz ϖK hϖK hϖK0 nK rK hrK zK hzK k j a b hab α β hN τ hτ hτ1 τ' hτ' hτ'1 J J' hJ hJ'

end S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified
end P2MW
export P2MW.S_AutomorphicForm_twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_unramified (solution)
