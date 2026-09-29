-- Prove2me | solution 1 for AutomorphicForm.twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e87ba1dd-60be-56e7-828a-f801ae97660f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_InfinitePlaceTransport
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_AutomorphicForm_measurePreserving_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_continuous_rightConv_and_contDiff_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

noncomputable section

section

open NumberField NumberField.AdelicLevel
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"
open scoped NumberField.PlaceTransport

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsFactorizableTestFn IsIsotypicCuspFormAt isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule continuous_sigmaSectionActOn twistedConvOp twistedConvOp_smul twistedConvOp_add IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archRowIsometryInclAt₀ glArch_rowIsometryInclAt₀ adelicGLHaar_mul_right_centreCutSiegelSet_lt_top IsGenuineCuspRealizationAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_add IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem rightConv sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul continuous_sigmaAdelicAct sigmaAdelicAct_globalPoints rowIsometrySubgroup₀ archComponent_archGLIncl_self measurePreserving_sigmaAdelicAct SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite continuous_and_hasCompactSupport_of_isFactorizableTestFn continuous_unipotentGL2 continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre IsBoundedOnSiegelWindows"
namespace SigmaLevelGroup
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem map_toRingEquiv_map_algebraMap (σ : L ≃ₐ[K] L) (NK : Ideal (𝓞 K)) :
    Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L)
        (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
      = Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK := by
  have hcomp :
      ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L).comp
          (algebraMap (𝓞 K) (𝓞 L))
        = algebraMap (𝓞 K) (𝓞 L) :=
    RingHom.ext fun k => RingOfIntegers.ext (σ.commutes (k : K))
  rw [Ideal.map_map, hcomp]

omit [NumberField K] in
private theorem idealBound_smul_of_map_eq (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)}
    (hN : Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N
      = N)
    (w : HeightOneSpectrum (𝓞 L)) :
    idealBound (𝓞 L) N (σ • w) = idealBound (𝓞 L) N w := by
  by_cases h0 : N = ⊥
  · subst h0
    rw [idealBound_bot, idealBound_bot]
  have key : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : ℕ),
      k ≤ (Associates.mk P.asIdeal).count (Associates.mk N).factors ↔ N ≤ P.asIdeal ^ k := fun P k => by
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.2 h0)
        (Associates.irreducible_mk.2 P.irreducible),
      ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
  have hσ : ∀ k : ℕ, N ≤ (σ • w).asIdeal ^ k ↔ N ≤ w.asIdeal ^ k := fun k => by
    rw [NumberField.PlaceTransport.smul_asIdeal_eq_map, ← Ideal.map_pow]
    conv_lhs => rw [← hN]
    rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
    exact Ideal.comap_le_comap_iff_of_surjective
      (f := (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ).symm) (RingEquiv.surjective _) _ _
  have hc : (Associates.mk (σ • w).asIdeal).count (Associates.mk N).factors
      = (Associates.mk w.asIdeal).count (Associates.mk N).factors :=
    le_antisymm ((key _ _).2 ((hσ _).1 ((key _ _).1 le_rfl)))
      ((key _ _).2 ((hσ _).2 ((key _ _).1 le_rfl)))
  rw [idealBound_of_ne_bot h0, idealBound_of_ne_bot h0, hc]

private theorem act_snd_mem_integralFiniteAdeles (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L}
    (hx : x.2 ∈ integralFiniteAdeles (𝓞 L) L) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 ∈ integralFiniteAdeles (𝓞 L) L := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff]
  exact hx _

private theorem act_snd_mem_idealBall (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)}
    (hN : Ideal.map ((MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) : 𝓞 L →+* 𝓞 L) N
      = N)
    {x : AdeleRing (𝓞 L) L} (hx : x.2 ∈ idealBall (𝓞 L) L N) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 ∈ idealBall (𝓞 L) L N := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.valued_transport]
  have h := idealBound_smul_of_map_eq σ hN (σ⁻¹ • w')
  rw [smul_inv_smul] at h
  exact (hx _).trans h.symm.le

private theorem act_fst_eq_zero (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 0) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 0 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_zero _

private theorem act_fst_eq_one (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 1 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_one _

private theorem isLevelOneMatrix_glFin_sigmaAdelicAct (σ : L ≃ₐ[K] L) (NK : Ideal (𝓞 K))
    {g : GL (Fin 2) (AdeleRing (𝓞 L) L)}
    (hg : IsLevelOneMatrix (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
      (glFin (𝓞 L) L g : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L))) :
    IsLevelOneMatrix (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
      (glFin (𝓞 L) L (sigmaAdelicAct K L (M4aHerbrand.GenuineDescent.genuineDescentDatum K L) σ g) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  integral i j :=
    act_snd_mem_integralFiniteAdeles σ (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j)
      (hg.integral i j)
  lowerLeft :=
    act_snd_mem_idealBall σ (map_toRingEquiv_map_algebraMap σ NK)
      (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0) hg.lowerLeft
  lowerRight := by
    have h := act_snd_mem_idealBall σ (map_toRingEquiv_map_algebraMap σ NK)
      (x := (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 - 1) hg.lowerRight
    rwa [map_sub, map_one] at h

private theorem sigmaAdelicAct_mem_levelOne_inf_finiteAdelicGL2Subgroup
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (NK : Ideal (𝓞 K))
    {g : GL (Fin 2) (AdeleRing (𝓞 L) L)}
    (hg : g ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) :
    sigmaAdelicAct K L D σ g
      ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : D = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨h₁, h₂⟩ := mem_finiteLevelOne_iff.1 (mem_levelOne_iff.1 hlev)
  refine Subgroup.mem_inf.2 ⟨mem_levelOne_iff.2 (mem_finiteLevelOne_iff.2 ⟨?_, ?_⟩), ?_⟩
  · exact isLevelOneMatrix_glFin_sigmaAdelicAct σ NK h₁
  · rw [← map_inv, ← map_inv]
    refine isLevelOneMatrix_glFin_sigmaAdelicAct σ NK ?_
    rw [map_inv]
    exact h₂
  · rw [mem_finiteAdelicGL2Subgroup_iff] at harch ⊢
    have hentry : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1
        = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
      intro i j
      have h := glArch_apply (𝓞 L) L g i j
      rw [harch, Units.val_one] at h
      exact h.symm
    refine Units.ext ?_
    rw [Units.val_one]
    ext i j
    rw [glArch_apply, Matrix.one_apply]
    have h := hentry i j
    rw [Matrix.one_apply] at h
    split_ifs at h ⊢ with hij
    · exact act_fst_eq_one σ h
    · exact act_fst_eq_zero σ h

end AutomorphicForm.SigmaLevelGroup

end

section

open NumberField IsDedekindDomain

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsFactorizableTestFn IsIsotypicCuspFormAt isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule continuous_sigmaSectionActOn twistedConvOp twistedConvOp_smul twistedConvOp_add IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archRowIsometryInclAt₀ glArch_rowIsometryInclAt₀ adelicGLHaar_mul_right_centreCutSiegelSet_lt_top IsGenuineCuspRealizationAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_add IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem rightConv sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul continuous_sigmaAdelicAct sigmaAdelicAct_globalPoints rowIsometrySubgroup₀ archComponent_archGLIncl_self measurePreserving_sigmaAdelicAct SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite continuous_and_hasCompactSupport_of_isFactorizableTestFn continuous_unipotentGL2 continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre IsBoundedOnSiegelWindows"
namespace LevelFiniteFactor
p2m_open "AutomorphicForm"

variable {K : Type} [Field K] [NumberField K]

private theorem exists_heightOneSpectrum_comap_eq_span (p : ℕ) (hp : p.Prime) :
    ∃ P : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) P.asIdeal = Ideal.span {(p : ℤ)} := by
  have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hp0).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQprime, hQcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
    (Ideal.span {(p : ℤ)}) (⊥ : Ideal (𝓞 K)) (Ideal.comap_bot_le_of_injective _ hinj)
  refine ⟨⟨Q, hQprime, fun hQ => ?_⟩, hQcomap⟩
  rw [hQ, Ideal.comap_bot_of_injective _ hinj] at hQcomap
  exact hp0 (Ideal.span_singleton_eq_bot.1 hQcomap.symm)

private theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ N → p ∈ S) : N ≠ ⊥ := by
  rintro rfl
  have hall : ∀ p : HeightOneSpectrum (𝓞 K), p ∈ S := fun p =>
    hNS p (by rw [← Ideal.zero_eq_bot]; exact dvd_zero _)
  choose P hP using fun q : {p : ℕ | Nat.Prime p} =>
    exists_heightOneSpectrum_comap_eq_span (K := K) q.1 q.2
  haveI : Infinite {p : ℕ | Nat.Prime p} := Set.infinite_coe_iff.2 Nat.infinite_setOf_prime
  refine not_injective_infinite_finite (fun q : {p : ℕ | Nat.Prime p} => (⟨P q, hall (P q)⟩ : S))
    fun q₁ q₂ h => ?_
  have h' : P q₁ = P q₂ := congrArg Subtype.val h
  have hspan : Ideal.span {((q₁ : ℕ) : ℤ)} = Ideal.span {((q₂ : ℕ) : ℤ)} := by
    rw [← hP q₁, ← hP q₂, h']
  have hq := Int.eq_of_associated_of_nonneg (Ideal.span_singleton_eq_span_singleton.1 hspan)
    (by positivity) (by positivity)
  exact Subtype.ext (by exact_mod_cast hq)

end AutomorphicForm.LevelFiniteFactor

end

section

open NumberField IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "semiLocalHomeomorph piIntegers semiLocalIntegers semiLocalIntegers_eq_preimage semiLocalIntegralSet semiLocalEval semiLocalComponent IsUnitFactorizableAboveOfType mem_integralUnitsSet IsFactorizableTestFn IsIsotypicCuspFormAt isotypicCuspSubmodule continuous_of_mem_isotypicCuspSubmodule continuous_sigmaSectionActOn twistedConvOp twistedConvOp_smul twistedConvOp_add IsRightEquivariant typeSubmodule mem_typeSubmodule_of_isRightEquivariant rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule mem_archCutSubmodule_iff archRowIsometryInclAt₀ glArch_rowIsometryInclAt₀ adelicGLHaar_mul_right_centreCutSiegelSet_lt_top IsGenuineCuspRealizationAt CarrierPins productionPinsOf AdelicGL2 globalPoints centralScalar IsLsXiFunction finiteAdelicGL2Subgroup mem_finiteAdelicGL2Subgroup_iff IsKfSmooth isKfSmooth_iff IsSmoothCuspAutomorphicFnAt lsXiMemberAt_iff IsAutomorphicFnAt unipotentGL2 unipotentGL2_add IsCuspidalFn HeckeEigensystem.cNorm HeckeEigensystem.toRawCentral_b SmoothCuspRealizationAt HeckeEigensystem rightConv sigmaAdelicAct sigmaSectionActOn sigmaAdelicAct_one sigmaAdelicAct_mul continuous_sigmaAdelicAct sigmaAdelicAct_globalPoints rowIsometrySubgroup₀ archComponent_archGLIncl_self measurePreserving_sigmaAdelicAct SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite continuous_and_hasCompactSupport_of_isFactorizableTestFn continuous_unipotentGL2 continuous_rightConv_and_contDiff_of_isFactorizableTestFn rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre IsBoundedOnSiegelWindows"
namespace LevelFiniteFactor
p2m_open "AutomorphicForm"

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem map_algebraMap_ne_bot {NK : Ideal (𝓞 K)} (hNK : NK ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
  fun h => hNK ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective K L)).1 h)

end AutomorphicForm.LevelFiniteFactor

end

section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain MeasureTheory HeckeIntegralSeam
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm AutomorphicForm.SmoothCusp"
open scoped NumberField.PlaceTransport

namespace Q09StabH

private abbrev pinsL (L : Type) [Field L] [NumberField L] (X : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L X (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
    (adelicBox L)

private abbrev window (L : Type) [Field L] [NumberField L] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    Set (AdelicGL2 (𝓞 L) L) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂

section Pins

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]

private theorem mem_Z (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : z ∈ (pinsL L X).Z := by
  show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)
  exact Subgroup.mem_top z

private def toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : (pinsL L X).Z := ⟨z, mem_Z X z⟩

@[scoped simp] private theorem coe_toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((toZ X z : (pinsL L X).Z) : (AdeleRing (𝓞 L) L)ˣ) = z := rfl

private theorem toZ_coe (X : Set (AdelicGL2 (𝓞 L) L)) (z : (pinsL L X).Z) : toZ X (z : (AdeleRing (𝓞 L) L)ˣ) = z :=
  Subtype.ext rfl

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem unitsAct_coe (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((Dsc.unitsAct σ z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L) = Dsc.act σ (z : AdeleRing (𝓞 L) L) := rfl

private theorem unitsAct_unitsAct_inv (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Dsc.unitsAct σ (Dsc.unitsAct σ⁻¹ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem unitsAct_inv_unitsAct (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    Dsc.unitsAct σ⁻¹ (Dsc.unitsAct σ z) = z := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

private def twistChar (σ : L ≃ₐ[K] L) (Y : Set (AdelicGL2 (𝓞 L) L)) {X : Set (AdelicGL2 (𝓞 L) L)}
    (ξ : (pinsL L X).Z →* ℂˣ) : (pinsL L Y).Z →* ℂˣ where
  toFun z := ξ (toZ X (Dsc.unitsAct σ (z : (AdeleRing (𝓞 L) L)ˣ)))
  map_one' := by
    have h : toZ (L := L) X (Dsc.unitsAct σ ((1 : (pinsL L Y).Z) : (AdeleRing (𝓞 L) L)ˣ)) = 1 :=
      Subtype.ext (by simp only [coe_toZ, OneMemClass.coe_one, map_one])
    rw [h, map_one]
  map_mul' a b := by
    have h : toZ (L := L) X (Dsc.unitsAct σ ((a * b : (pinsL L Y).Z) : (AdeleRing (𝓞 L) L)ˣ))
        = toZ X (Dsc.unitsAct σ (a : (AdeleRing (𝓞 L) L)ˣ)) * toZ X (Dsc.unitsAct σ (b : (AdeleRing (𝓞 L) L)ˣ)) :=
      Subtype.ext (by simp only [coe_toZ, Subgroup.coe_mul, map_mul])
    rw [h, map_mul]

private theorem twistChar_apply (σ : L ≃ₐ[K] L) (Y : Set (AdelicGL2 (𝓞 L) L)) {X : Set (AdelicGL2 (𝓞 L) L)}
    (ξ : (pinsL L X).Z →* ℂˣ) (z : (pinsL L Y).Z) :
    twistChar Dsc σ Y ξ z = ξ (toZ X (Dsc.unitsAct σ (z : (AdeleRing (𝓞 L) L)ˣ))) := rfl

private def recastChar {X : Set (AdelicGL2 (𝓞 L) L)} (Y : Set (AdelicGL2 (𝓞 L) L)) (ξ : (pinsL L X).Z →* ℂˣ) :
    (pinsL L Y).Z →* ℂˣ where
  toFun z := ξ (toZ X (z : (AdeleRing (𝓞 L) L)ˣ))
  map_one' := by
    have h : toZ (L := L) X ((1 : (pinsL L Y).Z) : (AdeleRing (𝓞 L) L)ˣ) = 1 :=
      Subtype.ext (by simp only [coe_toZ, OneMemClass.coe_one])
    rw [h, map_one]
  map_mul' a b := by
    have h : toZ (L := L) X ((a * b : (pinsL L Y).Z) : (AdeleRing (𝓞 L) L)ˣ)
        = toZ X (a : (AdeleRing (𝓞 L) L)ˣ) * toZ X (b : (AdeleRing (𝓞 L) L)ˣ) :=
      Subtype.ext (by simp only [coe_toZ, Subgroup.coe_mul])
    rw [h, map_mul]

private theorem recastChar_self {X : Set (AdelicGL2 (𝓞 L) L)} (ξ : (pinsL L X).Z →* ℂˣ) : recastChar X ξ = ξ :=
  MonoidHom.ext fun z => by
    show ξ (toZ X (z : (AdeleRing (𝓞 L) L)ˣ)) = ξ z
    rw [toZ_coe]

end Pins

section Action

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem act_inv_act (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ⁻¹ (sigmaAdelicAct K L Dsc σ g) = g := by
  have h := sigmaAdelicAct_mul K L Dsc σ⁻¹ σ
  rw [inv_mul_cancel, sigmaAdelicAct_one] at h
  exact (DFunLike.congr_fun h g).symm

private theorem act_act_inv (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ (sigmaAdelicAct K L Dsc σ⁻¹ g) = g := by
  have h := sigmaAdelicAct_mul K L Dsc σ σ⁻¹
  rw [mul_inv_cancel, sigmaAdelicAct_one] at h
  exact (DFunLike.congr_fun h g).symm

private theorem act_surjective (σ : L ≃ₐ[K] L) : Function.Surjective (sigmaAdelicAct K L Dsc σ) :=
  fun g => ⟨sigmaAdelicAct K L Dsc σ⁻¹ g, act_act_inv Dsc σ g⟩

private theorem act_injective (σ : L ≃ₐ[K] L) : Function.Injective (sigmaAdelicAct K L Dsc σ) :=
  Function.LeftInverse.injective (act_inv_act Dsc σ)

private def actEmb (σ : L ≃ₐ[K] L) : AdelicGL2 (𝓞 L) L ↪ AdelicGL2 (𝓞 L) L :=
  ⟨sigmaAdelicAct K L Dsc σ, act_injective Dsc σ⟩

@[scoped simp] private theorem actEmb_apply (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    actEmb Dsc σ g = sigmaAdelicAct K L Dsc σ g := rfl

private theorem act_entry (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) (i j : Fin 2) :
    ((sigmaAdelicAct K L Dsc σ g : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      = Dsc.act σ ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j g

private theorem sigmaSectionActOn_apply (σ : L ≃ₐ[K] L) (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u g = u (sigmaAdelicAct K L Dsc σ g) := rfl

private theorem act_centralScalar (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L Dsc σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (Dsc.unitsAct σ z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [act_entry]
  by_cases hij : i = j
  · subst hij
    rw [centralScalar_apply_eq, centralScalar_apply_eq, unitsAct_coe]
  · rw [centralScalar_apply_ne _ hij, centralScalar_apply_ne _ hij, map_zero]

omit [NumberField L] in
private theorem map_map_inv (σ : L ≃ₐ[K] L) (γ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Matrix.GeneralLinearGroup.map (σ : L →+* L) (Matrix.GeneralLinearGroup.map ((σ⁻¹ : L ≃ₐ[K] L) : L →+* L) γ)
      = γ := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.map_apply]
  exact σ.apply_symm_apply _

private theorem act_globalPoints (σ : L ≃ₐ[K] L) (γ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaAdelicAct K L Dsc σ (globalPoints (𝓞 L) L γ)
      = globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ) :=
  sigmaAdelicAct_globalPoints K L Dsc σ γ

private theorem twist_right_invariant (σ : L ≃ₐ[K] L) {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    (hU : ∀ k ∈ U, sigmaAdelicAct K L Dsc σ k ∈ U) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ U, u (g * k) = u g) (g : AdelicGL2 (𝓞 L) L) :
    ∀ k ∈ U, sigmaSectionActOn K L Dsc σ u (g * k) = sigmaSectionActOn K L Dsc σ u g := fun k hk => by
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul]
  exact hu _ _ (hU k hk)

private theorem twist_left_invariant (σ : L ≃ₐ[K] L) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * g) = u g)
    (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u (globalPoints (𝓞 L) L γ * g) = sigmaSectionActOn K L Dsc σ u g := by
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul, act_globalPoints]
  exact hu _ _

private theorem twist_central_transform (σ : L ≃ₐ[K] L) {X Y : Set (AdelicGL2 (𝓞 L) L)} {ξ : (pinsL L X).Z →* ℂˣ}
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ (z : (pinsL L X).Z) (g : AdelicGL2 (𝓞 L) L),
      u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * g) = ((ξ z : ℂˣ) : ℂ) * u g)
    (z : (pinsL L Y).Z) (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * g)
      = ((twistChar Dsc σ Y ξ z : ℂˣ) : ℂ) * sigmaSectionActOn K L Dsc σ u g := by
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul, act_centralScalar, twistChar_apply]
  exact hu (toZ X (Dsc.unitsAct σ (z : (AdeleRing (𝓞 L) L)ˣ))) _

end Action

section FinitePart

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem act_snd_mem_integralFiniteAdeles (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L}
    (hx : x.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  refine fun w' => ?_
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ x (smul_inv_smul σ w'),
    NumberField.PlaceTransport.transport_mem_adicCompletionIntegers_iff]
  exact hx _

private theorem act_fst_eq_zero (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 0) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 0 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_zero _

private theorem act_fst_eq_one (σ : L ≃ₐ[K] L) {x : AdeleRing (𝓞 L) L} (hx : x.1 = 1) :
    ((M4aHerbrand.GenuineDescent.genuineDescentDatum K L).act σ x).1 = 1 := by
  funext w'
  rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ x (smul_inv_smul σ w'), hx]
  exact map_one _

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem act_mem_finiteAdelicGL2Subgroup (σ : L ≃ₐ[K] L) {g : AdelicGL2 (𝓞 L) L}
    (hg : g ∈ finiteAdelicGL2Subgroup L) : sigmaAdelicAct K L Dsc σ g ∈ finiteAdelicGL2Subgroup L := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : Dsc = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [mem_finiteAdelicGL2Subgroup_iff] at hg ⊢
  have hentry : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j).1
      = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j := by
    intro i j
    have h := glArch_apply (𝓞 L) L g i j
    rw [hg, Units.val_one] at h
    exact h.symm
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply, act_entry, Matrix.one_apply]
  have h := hentry i j
  rw [Matrix.one_apply] at h
  split_ifs at h ⊢ with hij
  · exact act_fst_eq_one σ h
  · exact act_fst_eq_zero σ h

private theorem glFin_act_mem_finiteIntegralGL2 (σ : L ≃ₐ[K] L) {g : AdelicGL2 (𝓞 L) L}
    (hg : glFin (𝓞 L) L g ∈ finiteIntegralGL2 (𝓞 L) L) :
    glFin (𝓞 L) L (sigmaAdelicAct K L Dsc σ g) ∈ finiteIntegralGL2 (𝓞 L) L := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : Dsc = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  rw [mem_finiteIntegralGL2_iff] at hg ⊢
  obtain ⟨h₁, h₂⟩ := hg
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, act_entry]
    have h := h₁ i j
    rw [glFin_apply] at h
    exact act_snd_mem_integralFiniteAdeles σ h
  · rw [← map_inv, ← map_inv, glFin_apply, act_entry]
    have h := h₂ i j
    rw [← map_inv, glFin_apply] at h
    exact act_snd_mem_integralFiniteAdeles σ h

end FinitePart

section NormedTransport

variable {A B : Type*} [NormedField A] [NormedField B]

private theorem map_entry (e : A ≃+* B) (m : GL (Fin 2) A) (i j : Fin 2) :
    ((Matrix.GeneralLinearGroup.map (e : A →+* B) m : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) i j
      = e ((m : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j m

private theorem det_map (e : A ≃+* B) (m : GL (Fin 2) A) :
    ((Matrix.GeneralLinearGroup.map (e : A →+* B) m : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).det
      = e (m : Matrix (Fin 2) (Fin 2) A).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, map_entry, map_entry, map_entry, map_entry, map_sub, map_mul,
    map_mul]

private theorem rowNormSq_map (e : A ≃+* B) (he : ∀ x : A, ‖e x‖ = ‖x‖) (m : GL (Fin 2) A) :
    rowNormSq ((Matrix.GeneralLinearGroup.map (e : A →+* B) m : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)
      = rowNormSq (m : Matrix (Fin 2) (Fin 2) A) := by
  unfold rowNormSq
  rw [map_entry, map_entry, he, he]

private theorem topNormSq_map (e : A ≃+* B) (he : ∀ x : A, ‖e x‖ = ‖x‖) (m : GL (Fin 2) A) :
    topNormSq ((Matrix.GeneralLinearGroup.map (e : A →+* B) m : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B)
      = topNormSq (m : Matrix (Fin 2) (Fin 2) A) := by
  unfold topNormSq
  rw [map_entry, map_entry, he, he]

private theorem localHeight_map (e : A ≃+* B) (he : ∀ x : A, ‖e x‖ = ‖x‖) (m : GL (Fin 2) A) :
    localHeight (Matrix.GeneralLinearGroup.map (e : A →+* B) m) = localHeight m := by
  unfold localHeight
  rw [det_map, he, rowNormSq_map e he]

private theorem xWindowSq_map (e : A ≃+* B) (he : ∀ x : A, ‖e x‖ = ‖x‖) (m : GL (Fin 2) A) :
    xWindowSq (Matrix.GeneralLinearGroup.map (e : A →+* B) m) = xWindowSq m := by
  unfold xWindowSq
  rw [topNormSq_map e he, rowNormSq_map e he, localHeight_map e he]

private theorem norm_det_map (e : A ≃+* B) (he : ∀ x : A, ‖e x‖ = ‖x‖) (m : GL (Fin 2) A) :
    ‖((Matrix.GeneralLinearGroup.map (e : A →+* B) m : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B).det‖
      = ‖(m : Matrix (Fin 2) (Fin 2) A).det‖ := by
  rw [det_map, he]

end NormedTransport

section ArchPart

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem norm_transport (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (x : w.Completion) :
    ‖InfinitePlaceTransport.transport σ h x‖ = ‖x‖ := by
  have hc : Isometry (WithAbs.congr w.1 w'.1 ((σ : L ≃ₐ[K] L) : L ≃+* L)) :=
    AddMonoidHomClass.isometry_of_norm _ fun y => by
      rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
      exact InfinitePlaceTransport.apply_apply_of_smul_eq h _
  have hT : Isometry (InfinitePlaceTransport.transport σ h) := by
    have hfun : (InfinitePlaceTransport.transport σ h : w.Completion → w'.Completion) =
        NumberField.InfinitePlace.Completion.ofCompletion ∘ UniformSpace.Completion.map _ ∘
          NumberField.InfinitePlace.Completion.toCompletion :=
      funext (InfinitePlaceTransport.transport_apply σ h)
    rw [hfun]
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion w').symm.isometry.comp
      (hc.completion_map.comp (NumberField.InfinitePlace.Completion.isometry_toCompletion w))
  have hd := hT.dist_eq x 0
  rwa [map_zero, dist_zero_right, dist_zero_right] at hd

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem archComponent_act (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (g : AdelicGL2 (𝓞 L) L) :
    archComponent L w' (glArch (𝓞 L) L (sigmaAdelicAct K L Dsc σ g))
      = Matrix.GeneralLinearGroup.map (InfinitePlaceTransport.transport σ h : w.Completion →+* w'.Completion)
          (archComponent L w (glArch (𝓞 L) L g)) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : Dsc = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [map_entry, archComponent_apply, archComponent_apply, glArch_apply, glArch_apply, act_entry]
  exact M4aHerbrand.GenuineDescent.genuineDescentDatum_act_fst_apply K L σ _ h

private theorem localHeight_act (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (g : AdelicGL2 (𝓞 L) L) :
    localHeight (archComponent L w' (glArch (𝓞 L) L (sigmaAdelicAct K L Dsc σ g)))
      = localHeight (archComponent L w (glArch (𝓞 L) L g)) := by
  rw [archComponent_act Dsc σ h, localHeight_map _ (norm_transport σ h)]

private theorem xWindowSq_act (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (g : AdelicGL2 (𝓞 L) L) :
    xWindowSq (archComponent L w' (glArch (𝓞 L) L (sigmaAdelicAct K L Dsc σ g)))
      = xWindowSq (archComponent L w (glArch (𝓞 L) L g)) := by
  rw [archComponent_act Dsc σ h, xWindowSq_map _ (norm_transport σ h)]

private theorem archDetNorm_act (σ : L ≃ₐ[K] L) {w w' : InfinitePlace L} (h : σ • w = w') (g : AdelicGL2 (𝓞 L) L) :
    archDetNorm w' (sigmaAdelicAct K L Dsc σ g) = archDetNorm w g := by
  unfold archDetNorm
  rw [archComponent_act Dsc σ h, norm_det_map _ (norm_transport σ h)]

private theorem act_mem_centreCutSiegelSet (σ : L ≃ₐ[K] L) {c u d₁ d₂ : ℝ} {g : AdelicGL2 (𝓞 L) L}
    (hg : g ∈ centreCutSiegelSet L c u d₁ d₂) : sigmaAdelicAct K L Dsc σ g ∈ centreCutSiegelSet L c u d₁ d₂ := by
  obtain ⟨hfin, hfloor, hwin, hdet⟩ := hg
  refine ⟨glFin_act_mem_finiteIntegralGL2 Dsc σ hfin, fun w' => ?_, fun w' => ?_, fun w' => ?_⟩
  · rw [localHeight_act Dsc σ (smul_inv_smul σ w')]
    exact hfloor _
  · rw [xWindowSq_act Dsc σ (smul_inv_smul σ w')]
    exact hwin _
  · rw [archDetNorm_act Dsc σ (smul_inv_smul σ w')]
    exact hdet _

private theorem act_mem_centreCutSiegelSet_iff (σ : L ≃ₐ[K] L) {c u d₁ d₂ : ℝ} (g : AdelicGL2 (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ g ∈ centreCutSiegelSet L c u d₁ d₂ ↔ g ∈ centreCutSiegelSet L c u d₁ d₂ := by
  refine ⟨fun h => ?_, act_mem_centreCutSiegelSet Dsc σ⟩
  have h' := act_mem_centreCutSiegelSet Dsc σ⁻¹ h
  rwa [act_inv_act] at h'

private abbrev transportT (σ : L ≃ₐ[K] L) (T : Finset (AdelicGL2 (𝓞 L) L)) : Finset (AdelicGL2 (𝓞 L) L) :=
  T.map (actEmb Dsc σ⁻¹)

private theorem preimage_window (σ : L ≃ₐ[K] L) (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    sigmaAdelicAct K L Dsc σ ⁻¹' window L c u d₁ d₂ T = window L c u d₁ d₂ (transportT Dsc σ T) := by
  ext g
  rw [Set.mem_preimage]
  constructor
  · intro hg
    obtain ⟨x, hx, s, hs, hsx⟩ := Set.mem_iUnion₂.mp hg
    have hsx' : s * x = sigmaAdelicAct K L Dsc σ g := hsx
    refine Set.mem_iUnion₂.mpr ⟨actEmb Dsc σ⁻¹ x, Finset.mem_map_of_mem (f := actEmb Dsc σ⁻¹) hx,
      sigmaAdelicAct K L Dsc σ⁻¹ s, act_mem_centreCutSiegelSet Dsc σ⁻¹ hs, ?_⟩
    show sigmaAdelicAct K L Dsc σ⁻¹ s * sigmaAdelicAct K L Dsc σ⁻¹ x = g
    rw [← map_mul, hsx', act_inv_act]
  · intro hg
    obtain ⟨y, hy, s, hs, hsy⟩ := Set.mem_iUnion₂.mp hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    have hsy' : s * sigmaAdelicAct K L Dsc σ⁻¹ x = g := hsy
    refine Set.mem_iUnion₂.mpr ⟨x, hx, sigmaAdelicAct K L Dsc σ s, act_mem_centreCutSiegelSet Dsc σ hs, ?_⟩
    show sigmaAdelicAct K L Dsc σ s * x = sigmaAdelicAct K L Dsc σ g
    rw [← hsy', map_mul, act_act_inv]

end ArchPart

section SquareIntegrable

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

attribute [local instance] NumberField.AdelicHaar.glBorel

private theorem measurableSet_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    MeasurableSet (window L c u d₁ d₂ T) := by
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  rw [Set.image_mul_right]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet c u d₁ d₂)

omit [NumberField K] in
private theorem memLp_twist (σ : L ≃ₐ[K] L) {X : Set (AdelicGL2 (𝓞 L) L)} (hX : MeasurableSet X)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict X)) :
    MemLp (sigmaSectionActOn K L Dsc σ u) 2
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (sigmaAdelicAct K L Dsc σ ⁻¹' X)) :=
  hu.comp_measurePreserving ((measurePreserving_sigmaAdelicAct K L Dsc σ).restrict_preimage hX)

private theorem memLp_twist_window (σ : L ≃ₐ[K] L) (c u₀ d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L))
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c u₀ d₁ d₂ T))) :
    MemLp (sigmaSectionActOn K L Dsc σ u) 2
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c u₀ d₁ d₂ (transportT Dsc σ T))) := by
  rw [← preimage_window]
  exact memLp_twist Dsc σ (measurableSet_window c u₀ d₁ d₂ T) hu

end SquareIntegrable

section Covering

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private theorem coversModCentre_transport (σ : L ≃ₐ[K] L) {c u d₁ d₂ : ℝ} {T : Finset (AdelicGL2 (𝓞 L) L)}
    (hcov : CoversModCentre L (window L c u d₁ d₂ T)) :
    CoversModCentre L (window L c u d₁ d₂ (transportT Dsc σ T)) := by
  intro g
  obtain ⟨γ, z, hγz⟩ := hcov (sigmaAdelicAct K L Dsc σ g)
  refine ⟨Matrix.GeneralLinearGroup.map ((σ⁻¹ : L ≃ₐ[K] L) : L →+* L) γ, Dsc.unitsAct σ⁻¹ z, ?_⟩
  rw [← preimage_window, Set.mem_preimage, map_mul, map_mul, act_globalPoints, map_map_inv, act_centralScalar,
    unitsAct_unitsAct_inv]
  exact hγz

end Covering

section KfSmooth

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private def finRestrict (σ : L ≃ₐ[K] L) (k : finiteAdelicGL2Subgroup L) : finiteAdelicGL2Subgroup L :=
  ⟨sigmaAdelicAct K L Dsc σ k, act_mem_finiteAdelicGL2Subgroup Dsc σ k.2⟩

private theorem continuous_finRestrict (σ : L ≃ₐ[K] L) : Continuous (finRestrict Dsc σ) :=
  ((continuous_sigmaAdelicAct K L Dsc σ).comp continuous_subtype_val).subtype_mk _

open FLT.SmoothVectors in
private theorem stabilizer_twist (σ : L ≃ₐ[K] L) (u : AdelicGL2 (𝓞 L) L → ℂ) :
    ((MulAction.stabilizer (finiteAdelicGL2Subgroup L)
        (RightTranslationFn.mk (sigmaSectionActOn K L Dsc σ u) :
          RightTranslationFn (AdelicGL2 (𝓞 L) L) ℂ) : Subgroup (finiteAdelicGL2Subgroup L)) :
        Set (finiteAdelicGL2Subgroup L))
      = finRestrict Dsc σ ⁻¹'
          ((MulAction.stabilizer (finiteAdelicGL2Subgroup L)
            (RightTranslationFn.mk u : RightTranslationFn (AdelicGL2 (𝓞 L) L) ℂ) :
              Subgroup (finiteAdelicGL2Subgroup L)) : Set (finiteAdelicGL2Subgroup L)) := by
  ext k
  simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
  constructor
  · intro hk
    refine RightTranslationFn.ext fun x => ?_
    have hx : sigmaSectionActOn K L Dsc σ u (sigmaAdelicAct K L Dsc σ⁻¹ x * (k : AdelicGL2 (𝓞 L) L))
        = sigmaSectionActOn K L Dsc σ u (sigmaAdelicAct K L Dsc σ⁻¹ x) :=
      congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 L) L) ℂ =>
        RightTranslationFn.toFun f (sigmaAdelicAct K L Dsc σ⁻¹ x)) hk
    rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul, act_act_inv] at hx
    show u (x * sigmaAdelicAct K L Dsc σ (k : AdelicGL2 (𝓞 L) L)) = u x
    exact hx
  · intro hk
    refine RightTranslationFn.ext fun x => ?_
    have hx : u (sigmaAdelicAct K L Dsc σ x * sigmaAdelicAct K L Dsc σ (k : AdelicGL2 (𝓞 L) L))
        = u (sigmaAdelicAct K L Dsc σ x) :=
      congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 L) L) ℂ =>
        RightTranslationFn.toFun f (sigmaAdelicAct K L Dsc σ x)) hk
    show sigmaSectionActOn K L Dsc σ u (x * (k : AdelicGL2 (𝓞 L) L)) = sigmaSectionActOn K L Dsc σ u x
    rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul]
    exact hx

private theorem isKfSmooth_twist (σ : L ≃ₐ[K] L) {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsKfSmooth L u) :
    IsKfSmooth L (sigmaSectionActOn K L Dsc σ u) := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer, stabilizer_twist]
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_isOpen_stabilizer] at hu
  exact hu.preimage (continuous_finRestrict Dsc σ)

end KfSmooth

section Generic

variable {G : Type*} [Group G] {U : Subgroup G}

private theorem doubleCoset_mul_of_mem {g k : G} (hk : k ∈ U) :
    HeckePair.doubleCoset U (g * k) = HeckePair.doubleCoset U g := by
  ext x
  rw [HeckePair.mem_doubleCoset_iff, HeckePair.mem_doubleCoset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, k * b, U.mul_mem hk hb, by group⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha, k⁻¹ * b, U.mul_mem (U.inv_mem hk) hb, by group⟩

private theorem cosetSystem_of_doubleCoset_eq {g g' : G}
    (hgg : HeckePair.doubleCoset U g' = HeckePair.doubleCoset U g) {ι : Type*} {reps : ι → G}
    (h : IsHeckeCosetSystem U g' reps) : IsHeckeCosetSystem U g reps where
  mem_doubleCoset i := hgg ▸ h.mem_doubleCoset i
  covers x hx := h.covers x (hgg ▸ hx)
  mk_injective := h.mk_injective

private theorem cosetSystem_of_mul_mem {g k : G} (hk : k ∈ U) {ι : Type*} {reps : ι → G}
    (h : IsHeckeCosetSystem U (g * k) reps) : IsHeckeCosetSystem U g reps :=
  cosetSystem_of_doubleCoset_eq (doubleCoset_mul_of_mem hk) h

private theorem cosetSystem_comp_equiv {g : G} {ι ι' : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps)
    (e : ι' ≃ ι) : IsHeckeCosetSystem U g (reps ∘ e) where
  mem_doubleCoset i := h.mem_doubleCoset (e i)
  covers x hx := by
    obtain ⟨i, hi⟩ := h.covers x hx
    exact ⟨e.symm i, by simpa only [Function.comp, Equiv.apply_symm_apply] using hi⟩
  mk_injective i j hij := e.injective (h.mk_injective hij)

private theorem cosetSystem_map {g : G} {ι : Type*} {reps : ι → G} (h : IsHeckeCosetSystem U g reps) (α : G ≃* G)
    (hU : ∀ x : G, α x ∈ U ↔ x ∈ U) : IsHeckeCosetSystem U (α g) (fun i => α (reps i)) where
  mem_doubleCoset i := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp (h.mem_doubleCoset i)
    exact HeckePair.mem_doubleCoset_iff.mpr
      ⟨α a, (hU a).mpr ha, α b, (hU b).mpr hb, by rw [← map_mul, ← map_mul, hab]⟩
  covers x hx := by
    obtain ⟨a, ha, b, hb, hab⟩ := HeckePair.mem_doubleCoset_iff.mp hx
    have hy : α.symm x ∈ HeckePair.doubleCoset U g := by
      refine HeckePair.mem_doubleCoset_iff.mpr ⟨α.symm a, ?_, α.symm b, ?_, ?_⟩
      · rw [← hU, MulEquiv.apply_symm_apply]; exact ha
      · rw [← hU, MulEquiv.apply_symm_apply]; exact hb
      · apply α.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hab]
    obtain ⟨i, hi⟩ := h.covers _ hy
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have h2 := (hU _).mpr hi
    rwa [map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
  mk_injective i j hij := by
    apply h.mk_injective
    simp only at hij ⊢
    rw [QuotientGroup.eq] at hij ⊢
    rw [← map_inv, ← map_mul, hU] at hij
    exact hij

private theorem comap_comap_eq_of_fix {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (e : S →+* S)
    (he : ∀ r : R, e (algebraMap R S r) = algebraMap R S r) (P : Ideal S) :
    Ideal.comap (algebraMap R S) (Ideal.comap e P) = Ideal.comap (algebraMap R S) P := by
  rw [Ideal.comap_comap]
  congr 1
  exact RingHom.ext he

private def algEquivOfRingEquiv {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (e : S ≃+* S)
    (he : ∀ r : R, e (algebraMap R S r) = algebraMap R S r) : S ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := e) he

private theorem inertiaDeg_map_of_fix {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (e : S ≃+* S)
    (he : ∀ r : R, e (algebraMap R S r) = algebraMap R S r) (p : Ideal R) (P : Ideal S) :
    p.inertiaDeg' (Ideal.map (e : S →+* S) P) = p.inertiaDeg' P :=
  Ideal.inertiaDeg_map_eq p P (algEquivOfRingEquiv e he)

private theorem absNorm_map_ringEquiv {S : Type*} [CommRing S] [Nontrivial S] [IsDedekindDomain S] [Module.Free ℤ S]
    (e : S ≃+* S) (I : Ideal S) : Ideal.absNorm (Ideal.map (e : S →+* S) I) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv I (Ideal.map (e : S →+* S) I) e rfl).toEquiv).symm

end Generic

section Places

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem toRingEquiv_algebraMap (σ : L ≃ₐ[K] L) (k : 𝓞 K) :
    (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ : 𝓞 L ≃+* 𝓞 L) (algebraMap (𝓞 K) (𝓞 L) k)
      = algebraMap (𝓞 K) (𝓞 L) k :=
  RingOfIntegers.ext (σ.commutes (k : K))

omit [NumberField K] [NumberField L] in
private theorem under_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    (σ • w).under (𝓞 K) = w.under (𝓞 K) := by
  refine HeightOneSpectrum.ext ?_
  show Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) (σ • w).asIdeal = Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) w.asIdeal
  rw [NumberField.PlaceTransport.smul_asIdeal]
  exact comap_comap_eq_of_fix _ (toRingEquiv_algebraMap σ⁻¹) _

omit [NumberField K] [NumberField L] in
private theorem inertiaDeg_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    ((σ • w).under (𝓞 K)).asIdeal.inertiaDeg' (σ • w).asIdeal = (w.under (𝓞 K)).asIdeal.inertiaDeg' w.asIdeal := by
  rw [under_smul, NumberField.PlaceTransport.smul_asIdeal_eq_map]
  exact inertiaDeg_map_of_fix _ (toRingEquiv_algebraMap σ) _ _

omit [NumberField K] in
private theorem absNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Ideal.absNorm (σ • w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [NumberField.PlaceTransport.smul_asIdeal_eq_map]
  exact absNorm_map_ringEquiv _ _

private def genIndexEquiv (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    Fin (Ideal.absNorm w.asIdeal + 1) ≃ Fin (Ideal.absNorm (σ • w).asIdeal + 1) :=
  finCongr (by rw [absNorm_smul])

omit [NumberField K] [NumberField L] in
private theorem smul_mem_SL_iff
    (σ : L ≃ₐ[K] L) {SK : Finset (HeightOneSpectrum (𝓞 K))} {SL : Finset (HeightOneSpectrum (𝓞 L))}
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ w.under (𝓞 K) ∈ SK) (w : HeightOneSpectrum (𝓞 L)) :
    σ • w ∈ SL ↔ w ∈ SL := by
  rw [hSL, hSL, under_smul]

private theorem idealBound_map_eq_one_of_not_mem {NK : Ideal (𝓞 K)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ w.under (𝓞 K) ∈ SK)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) :
    idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1 := by
  apply idealBound_eq_one_of_not_dvd hN
  intro hdvd
  refine hw ((hSL w).mpr (hNS _ ?_))
  show (w.asIdeal.under (𝓞 K)) ∣ NK
  rw [Ideal.dvd_iff_le] at hdvd ⊢
  exact Ideal.le_comap_map.trans (Ideal.comap_mono hdvd)

end Places

section Action

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

private def actEquiv (σ : L ≃ₐ[K] L) : AdelicGL2 (𝓞 L) L ≃* AdelicGL2 (𝓞 L) L where
  toFun := sigmaAdelicAct K L Dsc σ
  invFun := sigmaAdelicAct K L Dsc σ⁻¹
  left_inv := act_inv_act Dsc σ
  right_inv := act_act_inv Dsc σ
  map_mul' := map_mul _

omit [NumberField K] in
private theorem actEquiv_apply
    (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) : actEquiv Dsc σ g = sigmaAdelicAct K L Dsc σ g := rfl

omit [NumberField K] in
private theorem det_act (σ : L ≃ₐ[K] L) (g : AdelicGL2 (𝓞 L) L) :
    Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L Dsc σ g) = Dsc.unitsAct σ (Matrix.GeneralLinearGroup.det g) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, unitsAct_coe, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.det_fin_two, Matrix.det_fin_two, act_entry, act_entry, act_entry, act_entry, map_sub, map_mul, map_mul]

private def tUnit (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    (w₂.adicCompletion L)ˣ :=
  Units.map ((NumberField.PlaceTransport.transport σ h : w₁.adicCompletion L →+* w₂.adicCompletion L) :
    w₁.adicCompletion L →* w₂.adicCompletion L) t

omit [NumberField K] in
private theorem coe_tUnit
    (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    ((tUnit σ h t : (w₂.adicCompletion L)ˣ) : w₂.adicCompletion L)
      = NumberField.PlaceTransport.transport σ h (t : w₁.adicCompletion L) := rfl

omit [NumberField K] in
private theorem valued_tUnit
    (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) (t : (w₁.adicCompletion L)ˣ) :
    Valued.v ((tUnit σ h t : (w₂.adicCompletion L)ˣ) : w₂.adicCompletion L) = Valued.v (t : w₁.adicCompletion L) := by
  rw [coe_tUnit, NumberField.PlaceTransport.valued_transport]

private theorem act_heckeGenAt (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂)
    (t : (w₁.adicCompletion L)ˣ) :
    sigmaAdelicAct K L Dsc σ (heckeGenAt (𝓞 L) L w₁ t) = heckeGenAt (𝓞 L) L w₂ (tUnit σ h t) := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 L) K L
  obtain rfl : Dsc = M4aHerbrand.GenuineDescent.genuineDescentDatum K L := Subsingleton.elim _ _
  subst h
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [act_entry]
  refine Prod.ext ?_ ?_
  · rw [heckeGenAt_fst]
    have h1 := heckeGenAt_fst t i j
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hij
    · exact act_fst_eq_one σ h1
    · exact act_fst_eq_zero σ h1
  · refine FiniteAdeleRing.ext L fun v' => ?_
    by_cases hv : v' = σ • w₁
    · subst hv
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (rfl : σ • w₁ = σ • w₁),
        heckeGenAt_snd_apply_self, heckeGenAt_snd_apply_self]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
        fin_cases i
        · exact (coe_tUnit σ rfl t).symm
        · exact map_one _
      · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij, map_zero]
    · have hne : σ⁻¹ • v' ≠ w₁ := fun hh => hv (by rw [← hh, smul_inv_smul])
      rw [M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply K L σ _ (smul_inv_smul σ v'),
        heckeGenAt_snd_apply_of_ne t hne, heckeGenAt_snd_apply_of_ne (tUnit σ rfl t) hv, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs
      · exact map_one _
      · exact map_zero _

private theorem act_heckeGen (σ : L ≃ₐ[K] L) {w₁ w₂ : HeightOneSpectrum (𝓞 L)} (h : σ • w₁ = w₂) :
    ∃ s : (w₂.adicCompletion L)ˣ, Valued.v (s : w₂.adicCompletion L) = 1 ∧
      sigmaAdelicAct K L Dsc σ (heckeGen (𝓞 L) L w₁) = heckeGen (𝓞 L) L w₂ * heckeGenAt (𝓞 L) L w₂ s := by
  refine ⟨(uniformizerUnit L w₂)⁻¹ * tUnit σ h (uniformizerUnit L w₁), ?_, ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, valued_tUnit, valued_uniformizerUnit,
      valued_uniformizerUnit, inv_mul_cancel₀ WithZero.exp_ne_zero]
  · unfold heckeGen
    rw [act_heckeGenAt Dsc σ h, ← map_mul, mul_inv_cancel_left]

end Action

section Level

variable {L : Type} [Field L] [NumberField L]

private abbrev UN (L : Type) [Field L] [NumberField L] (N : Ideal (𝓞 L)) : Subgroup (AdelicGL2 (𝓞 L) L) :=
  levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L

private theorem glArch_heckeGenAt (v : HeightOneSpectrum (𝓞 L)) (s : (v.adicCompletion L)ˣ) :
    glArch (𝓞 L) L (heckeGenAt (𝓞 L) L v s) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply, heckeGenAt_fst]

private theorem heckeGenAt_mem_UN (N : Ideal (𝓞 L)) {v : HeightOneSpectrum (𝓞 L)} {s : (v.adicCompletion L)ˣ}
    (hs : Valued.v (s : v.adicCompletion L) = 1) : heckeGenAt (𝓞 L) L v s ∈ UN L N := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h := heckeGenAt_inv_mul_heckeGenAt_mem_levelOne (R := 𝓞 L) (K := L) (v := v) 1 s
      (by rw [Units.val_one, map_one, hs]) N
    rwa [map_one, inv_one, one_mul] at h
  · exact (mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_heckeGenAt v s)

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show (Matrix.diagonal ![(a : A), 1]).det = a
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_heckeGenAt (v : HeightOneSpectrum (𝓞 L)) (s : (v.adicCompletion L)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L v s) = Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v s) :=
  det_diagOne _

private theorem localUnit_mem_integralFiniteAdeles {v : HeightOneSpectrum (𝓞 L)} {s : (v.adicCompletion L)ˣ}
    (hs : Valued.v (s : v.adicCompletion L) = 1) :
    ((localUnit (𝓞 L) L v s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L)
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 L) L := by
  intro w
  classical
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, HeightOneSpectrum.mem_adicCompletionIntegers, hs]
  · rw [localUnit_apply_of_ne (𝓞 L) L v s hw]; exact one_mem _

private theorem localUnit_sub_one_mem_idealBall
    {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)} (hb : idealBound (𝓞 L) N v = 1)
    {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    ((localUnit (𝓞 L) L v s : (FiniteAdeleRing (𝓞 L) L)ˣ) : FiniteAdeleRing (𝓞 L) L) - 1 ∈ idealBall (𝓞 L) L N := by
  intro w
  rw [coe_sub_apply, coe_one_apply]
  by_cases hw : w = v
  · subst hw
    rw [localUnit_apply_self, hb]
    exact (Valuation.map_sub _ _ _).trans (max_le (le_of_eq hs) (le_of_eq (map_one _)))
  · rw [localUnit_apply_of_ne (𝓞 L) L v s hw, sub_self, map_zero]
    exact zero_le'

private theorem coe_units_map_finIncl_snd (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ((Units.map (finIncl (𝓞 L) L) z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).2
      = (z : FiniteAdeleRing (𝓞 L) L) := rfl

private theorem coe_units_map_finIncl_fst (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    ((Units.map (finIncl (𝓞 L) L) z : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L).1 = 1 := rfl

private theorem isLevelOneMatrix_glFin_centralScalar {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N v = 1) {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    IsLevelOneMatrix (𝓞 L) L N
      (glFin (𝓞 L) L (centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) (localUnit (𝓞 L) L v s))) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := by
  refine ⟨⟨fun i j => ?_, ?_⟩, ?_⟩
  · by_cases hij : i = j
    · subst hij
      rw [glFin_apply, centralScalar_apply_eq, coe_units_map_finIncl_snd]
      exact localUnit_mem_integralFiniteAdeles hs
    · rw [glFin_apply, centralScalar_apply_ne _ hij]
      exact zero_mem_integralFiniteAdeles
  · rw [glFin_apply, centralScalar_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    exact zero_mem_idealBall N
  · rw [glFin_apply, centralScalar_apply_eq, coe_units_map_finIncl_snd]
    exact localUnit_sub_one_mem_idealBall hb hs

private theorem glArch_centralScalar_units_map_finIncl (z : (FiniteAdeleRing (𝓞 L) L)ˣ) :
    glArch (𝓞 L) L (centralScalar (𝓞 L) L (Units.map (finIncl (𝓞 L) L) z)) = 1 := by
  refine Units.ext ?_
  rw [Units.val_one]
  ext i j
  rw [glArch_apply]
  by_cases hij : i = j
  · subst hij
    rw [centralScalar_apply_eq, coe_units_map_finIncl_fst, Matrix.one_apply_eq]
  · rw [centralScalar_apply_ne _ hij, Matrix.one_apply_ne hij]
    rfl

private theorem centralScalar_det_heckeGenAt_mem_UN {N : Ideal (𝓞 L)} {v : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N v = 1) {s : (v.adicCompletion L)ˣ} (hs : Valued.v (s : v.adicCompletion L) = 1) :
    centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 L) L v s)) ∈ UN L N := by
  rw [det_heckeGenAt]
  have hsi : Valued.v ((s⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hs, inv_one]
  refine Subgroup.mem_inf.mpr ⟨mem_levelOne_iff.mpr ?_,
    (mem_finiteAdelicGL2Subgroup_iff L _).mpr (glArch_centralScalar_units_map_finIncl _)⟩
  show _ ∧ _
  refine ⟨isLevelOneMatrix_glFin_centralScalar hb hs, ?_⟩
  rw [← map_inv, ← map_inv, ← map_inv, ← map_inv]
  exact isLevelOneMatrix_glFin_centralScalar hb hsi

end Level

section Transport

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

omit [NumberField K] in
private theorem actEquiv_inv_mem_iff (σ : L ≃ₐ[K] L) {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    (hstab : ∀ τ : L ≃ₐ[K] L, ∀ x ∈ U, sigmaAdelicAct K L Dsc τ x ∈ U) (x : AdelicGL2 (𝓞 L) L) :
    actEquiv Dsc σ⁻¹ x ∈ U ↔ x ∈ U := by
  rw [actEquiv_apply]
  refine ⟨fun hx => ?_, hstab σ⁻¹ x⟩
  have h := hstab σ _ hx
  rwa [act_act_inv] at h

omit [NumberField K] in
private theorem heckeCosetSum_twist (σ : L ≃ₐ[K] L) {n m : ℕ} (reps : Fin m → AdelicGL2 (𝓞 L) L) (e : Fin n ≃ Fin m)
    (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    heckeCosetSum L (fun i => sigmaAdelicAct K L Dsc σ⁻¹ (reps (e i))) (sigmaSectionActOn K L Dsc σ u) g
      = heckeCosetSum L reps u (sigmaAdelicAct K L Dsc σ g) := by
  unfold heckeCosetSum
  rw [← e.sum_comp fun j => u (sigmaAdelicAct K L Dsc σ g * reps j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  show u (sigmaAdelicAct K L Dsc σ (g * sigmaAdelicAct K L Dsc σ⁻¹ (reps (e i))))
    = u (sigmaAdelicAct K L Dsc σ g * reps (e i))
  rw [map_mul, act_act_inv]

private theorem isHeckeCosetEigenfunctionAt_twist (σ : L ≃ₐ[K] L) (N : Ideal (𝓞 L))
    (hstab : ∀ τ : L ≃ₐ[K] L, ∀ x ∈ UN L N, sigmaAdelicAct K L Dsc τ x ∈ UN L N) {u : AdelicGL2 (𝓞 L) L → ℂ}
    {w : HeightOneSpectrum (𝓞 L)} {c : ℂ}
    (h : IsHeckeCosetEigenfunctionAt L (UN L N) (heckeGen (𝓞 L) L (σ • w)) (σ • w) u c) :
    IsHeckeCosetEigenfunctionAt L (UN L N) (heckeGen (𝓞 L) L w) w (sigmaSectionActOn K L Dsc σ u) c := by
  obtain ⟨reps, hsys, hsum⟩ := h
  obtain ⟨s, hs, hgen⟩ := act_heckeGen Dsc σ⁻¹ (inv_smul_smul σ w)
  refine ⟨fun i => sigmaAdelicAct K L Dsc σ⁻¹ (reps (genIndexEquiv σ w i)), ?_, fun g => ?_⟩
  · have hs' := cosetSystem_comp_equiv (cosetSystem_map hsys (actEquiv Dsc σ⁻¹) (actEquiv_inv_mem_iff Dsc σ hstab))
      (genIndexEquiv σ w)
    rw [actEquiv_apply, hgen] at hs'
    exact cosetSystem_of_mul_mem (heckeGenAt_mem_UN N hs) hs'
  · rw [heckeCosetSum_twist, hsum, sigmaSectionActOn_apply]

private theorem central_eigen_twist (σ : L ≃ₐ[K] L) {N : Ideal (𝓞 L)} {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ UN L N, u (g * k) = u g) {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N (σ • w) = 1) {b : ℂ}
    (h : ∀ g : AdelicGL2 (𝓞 L) L,
      u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (σ • w))) * g) = b * u g)
    (g : AdelicGL2 (𝓞 L) L) :
    sigmaSectionActOn K L Dsc σ u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g)
      = b * sigmaSectionActOn K L Dsc σ u g := by
  obtain ⟨s, hs, hgen⟩ := act_heckeGen Dsc σ (rfl : σ • w = σ • w)
  rw [sigmaSectionActOn_apply, sigmaSectionActOn_apply, map_mul, act_centralScalar, ← det_act, hgen, map_mul, map_mul,
    mul_assoc, h, ← mul_centralScalar_comm, hlev _ _ (centralScalar_det_heckeGenAt_mem_UN hb hs)]

end Transport

section CuspCore

variable {Q : Type*} [AddCommGroup Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [LocallyCompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q]

private theorem setIntegral_comp_eq_smul (μ : Measure Q) [μ.IsAddHaarMeasure] (θ : Q ≃ₜ Q)
    (hθ : ∀ x y : Q, θ (x + y) = θ x + θ y) (Γ : AddSubgroup Q) [Countable Γ] (hΓ : ∀ γ : Q, γ ∈ Γ ↔ θ γ ∈ Γ)
    (B : Set Q) (hBc : IsCompact (closure B)) (hB : ∀ ν : Measure Q, IsAddFundamentalDomain Γ B ν) (F : Q → ℂ)
    (hF : ∀ γ ∈ Γ, ∀ x : Q, F (γ + x) = F x) :
    ∃ c : ℝ, ∫ x in B, F (θ x) ∂μ = c • ∫ x in B, F x ∂μ := by
  let θe : Q ≃+ Q := AddEquiv.mk' θ.toEquiv hθ
  haveI hμ' : (μ.map θ).IsAddHaarMeasure := θe.isAddHaarMeasure_map μ θ.continuous θ.symm.continuous
  have hqmp : Measure.QuasiMeasurePreserving θ μ (μ.map θ) :=
    ⟨θ.continuous.measurable, Measure.AbsolutelyContinuous.rfl⟩
  let e : Γ → Γ := fun γ => ⟨θ.symm γ, (hΓ _).mpr (by rw [Homeomorph.apply_symm_apply]; exact γ.2)⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => Subtype.ext (θ.symm.injective (congrArg Subtype.val hab)), fun b => ?_⟩
    refine ⟨⟨θ b, (hΓ _).mp b.2⟩, Subtype.ext ?_⟩
    show θ.symm (θ b) = b
    exact θ.symm_apply_apply b
  have hpre : IsAddFundamentalDomain Γ (θ ⁻¹' B) μ :=
    (hB (μ.map θ)).preimage_of_equiv hqmp he fun γ x => by
      show θ (θ.symm γ + x) = γ + θ x
      rw [hθ, Homeomorph.apply_symm_apply]
  have hFθ : ∀ (γ : Γ) (x : Q), F (θ (γ +ᵥ x)) = F (θ x) := fun γ x => by
    show F (θ (γ + x)) = F (θ x)
    rw [hθ]
    exact hF _ ((hΓ _).mp γ.2) _
  have hres : (μ.map θ).restrict B = Measure.addHaarScalarFactor (μ.map θ) μ • μ.restrict B := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs]
    exact Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure (μ.map θ) μ
      (hBc.of_isClosed_subset isClosed_closure (closure_mono Set.inter_subset_right))
  refine ⟨(Measure.addHaarScalarFactor (μ.map θ) μ : ℝ), ?_⟩
  have hmap : Measure.map θ.toMeasurableEquiv μ = μ.map θ := rfl
  calc ∫ x in B, F (θ x) ∂μ = ∫ x in θ ⁻¹' B, F (θ x) ∂μ := (hB μ).setIntegral_eq hpre hFθ
    _ = ∫ y in B, F y ∂(μ.map θ) := by rw [← hmap, setIntegral_map_equiv]; rfl
    _ = (Measure.addHaarScalarFactor (μ.map θ) μ : ℝ) • ∫ x in B, F x ∂μ := by
      rw [hres, integral_smul_nnreal_measure]
      exact NNReal.smul_def _ _

private theorem integral_cond_comp_eq_zero (μ : Measure Q) [μ.IsAddHaarMeasure] (θ : Q ≃ₜ Q)
    (hθ : ∀ x y : Q, θ (x + y) = θ x + θ y) (Γ : AddSubgroup Q) [Countable Γ] (hΓ : ∀ γ : Q, γ ∈ Γ ↔ θ γ ∈ Γ)
    (B : Set Q) (hBc : IsCompact (closure B)) (hB : ∀ ν : Measure Q, IsAddFundamentalDomain Γ B ν) (F : Q → ℂ)
    (hF : ∀ γ ∈ Γ, ∀ x : Q, F (γ + x) = F x) (h0 : ∫ x, F x ∂(ProbabilityTheory.cond μ B) = 0) :
    ∫ x, F (θ x) ∂(ProbabilityTheory.cond μ B) = 0 := by
  obtain ⟨c, hc⟩ := setIntegral_comp_eq_smul μ θ hθ Γ hΓ B hBc hB F hF
  rw [ProbabilityTheory.cond, integral_smul_measure] at h0 ⊢
  rw [hc, smul_comm, h0]
  simp

end CuspCore

section Cusp

variable {K L : Type} [Field K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

private theorem adeleAct_inv_act (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) : Dsc.act σ⁻¹ (Dsc.act σ x) = x := by
  have h : Dsc.act σ⁻¹ * Dsc.act σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  exact DFunLike.congr_fun h x

private theorem adeleAct_act_inv (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) : Dsc.act σ (Dsc.act σ⁻¹ x) = x := by
  have h : Dsc.act σ * Dsc.act σ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

private def actHomeo (σ : L ≃ₐ[K] L) : AdeleRing (𝓞 L) L ≃ₜ AdeleRing (𝓞 L) L where
  toFun := Dsc.act σ
  invFun := Dsc.act σ⁻¹
  left_inv := adeleAct_inv_act Dsc σ
  right_inv := adeleAct_act_inv Dsc σ
  continuous_toFun := Dsc.continuous_act σ
  continuous_invFun := Dsc.continuous_act σ⁻¹

private theorem actHomeo_apply (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) : actHomeo Dsc σ x = Dsc.act σ x := rfl

private theorem act_unipotentGL2 (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    sigmaAdelicAct K L Dsc σ (unipotentGL2 x) = unipotentGL2 (Dsc.act σ x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [act_entry]
  fin_cases i <;> fin_cases j <;> simp

private theorem globalPoints_entry (γ : Matrix.GeneralLinearGroup (Fin 2) L) (i j : Fin 2) :
    ((globalPoints (𝓞 L) L γ : AdelicGL2 (𝓞 L) L) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j
      = algebraMap L (AdeleRing (𝓞 L) L) ((γ : Matrix (Fin 2) (Fin 2) L) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j γ

private theorem globalPoints_unipotentGL2 (k : L) :
    globalPoints (𝓞 L) L (unipotentGL2 k) = unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) k) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [globalPoints_entry]
  fin_cases i <;> fin_cases j <;> simp

private theorem mem_principalSubgroup_iff_act (σ : L ≃ₐ[K] L) (x : AdeleRing (𝓞 L) L) :
    x ∈ AdeleRing.principalSubgroup (𝓞 L) L ↔ Dsc.act σ x ∈ AdeleRing.principalSubgroup (𝓞 L) L := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨σ k, (Dsc.compat σ k).symm⟩
  · rintro ⟨k, hk⟩
    refine ⟨σ⁻¹ k, ?_⟩
    rw [← Dsc.compat σ⁻¹ k, hk, adeleAct_inv_act]

private theorem countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 L) L) := by
  haveI : Countable L := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℚ L
    exact hf.countable
  refine Function.Surjective.countable (f := fun k : L =>
    (⟨algebraMap L (AdeleRing (𝓞 L) L) k, k, rfl⟩ : AdeleRing.principalSubgroup (𝓞 L) L)) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

private theorem isCompact_closure_adelicBox : IsCompact (closure (adelicBox L)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset L
  exact hC.closure_of_subset hsub

private theorem cusp_integrand_periodic {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * g) = u g)
    (y : AdelicGL2 (𝓞 L) L) :
    ∀ γ ∈ AdeleRing.principalSubgroup (𝓞 L) L, ∀ x : AdeleRing (𝓞 L) L,
      u (unipotentGL2 (γ + x) * y) = u (unipotentGL2 x * y) := by
  rintro _ ⟨k, rfl⟩ x
  rw [unipotentGL2_add, mul_assoc, ← globalPoints_unipotentGL2, hu]

private theorem isCuspidalFn_twist (σ : L ≃ₐ[K] L) {X Y : Set (AdelicGL2 (𝓞 L) L)} {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L), u (globalPoints (𝓞 L) L γ * g) = u g)
    (hc : @IsCuspidalFn _ (pinsL L X).nS _ _ (pinsL L X).ν unipotentGL2 u) :
    @IsCuspidalFn _ (pinsL L Y).nS _ _ (pinsL L Y).ν unipotentGL2 (sigmaSectionActOn K L Dsc σ u) := by
  intro g
  haveI := countable_principalSubgroup (L := L)
  have h0 : ∫ x, u (unipotentGL2 x * sigmaAdelicAct K L Dsc σ g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) = 0 := hc (sigmaAdelicAct K L Dsc σ g)
  have key := integral_cond_comp_eq_zero (adelicAddHaar (𝓞 L) L) (actHomeo Dsc σ) (fun x y => map_add (Dsc.act σ) x y)
    (AdeleRing.principalSubgroup (𝓞 L) L) (mem_principalSubgroup_iff_act Dsc σ) (adelicBox L)
    (isCompact_closure_adelicBox (L := L)) (isAddFundamentalDomain_adelicBox L)
    (fun x => u (unipotentGL2 x * sigmaAdelicAct K L Dsc σ g)) (cusp_integrand_periodic hu _) h0
  show ∫ x, sigmaSectionActOn K L Dsc σ u (unipotentGL2 x * g)
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 L) L) (adelicBox L)) = 0
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun x => ?_)) key
  show u (sigmaAdelicAct K L Dsc σ (unipotentGL2 x * g))
    = u (unipotentGL2 (actHomeo Dsc σ x) * sigmaAdelicAct K L Dsc σ g)
  rw [map_mul, act_unipotentGL2, actHomeo_apply]

end Cusp

section Unique

variable {L : Type} [Field L] [NumberField L]

private theorem centralChar_eq_of_isIsotypicCuspFormAt {X : Set (AdelicGL2 (𝓞 L) L)} {ξ₁ ξ₂ : (pinsL L X).Z →* ℂˣ}
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 L))} {Ψ : HeckeEigensystem L ℂ}
    {u w : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsIsotypicCuspFormAt L (pinsL L X) ξ₁ N S Ψ u) (hu0 : u ≠ 0)
    (hw : IsIsotypicCuspFormAt L (pinsL L X) ξ₂ N S Ψ w) (hw0 : w ≠ 0) : ξ₁ = ξ₂ := by
  let ΨN : HeckeEigensystem L ℂ := ⟨N, hN, Ψ.a, Ψ.b⟩
  let R : SmoothCuspRealizationAt L (pinsL L X) ΨN.toRawCentral :=
    { toFun := u
      exists_ne_zero := Function.ne_iff.mp hu0
      centralChar := ξ₁
      smoothCusp := hu.smoothCusp
      level_invariant := hu.level_invariant
      exceptionalSet := S
      hecke_eigen := hu.hecke_eigen
      central_eigen := hu.central_eigen }
  let R' : SmoothCuspRealizationAt L (pinsL L X) ΨN.toRawCentral :=
    { toFun := w
      exists_ne_zero := Function.ne_iff.mp hw0
      centralChar := ξ₂
      smoothCusp := hw.smoothCusp
      level_invariant := hw.level_invariant
      exceptionalSet := S
      hecke_eigen := hw.hecke_eigen
      central_eigen := hw.central_eigen }
  have hR : IsGenuineCuspRealizationAt L (pinsL L X) ΨN.toRawCentral R := hu.continuous
  have hR' : IsGenuineCuspRealizationAt L (pinsL L X) ΨN.toRawCentral R' := hw.continuous
  exact SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite L X ΨN ΨN ⟨∅, fun _ _ => ⟨rfl, rfl⟩⟩ R hR R' hR'

end Unique

section Assembly

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

omit [NumberField K] in
private theorem cNorm_smul (σ : L ≃ₐ[K] L) (w : HeightOneSpectrum (𝓞 L)) :
    HeckeEigensystem.cNorm (σ • w) = HeckeEigensystem.cNorm w := by
  unfold HeckeEigensystem.cNorm
  rw [absNorm_smul]

omit [NumberField K] in
private theorem toRawCentral_b_smul (σ : L ≃ₐ[K] L) {SL : Finset (HeightOneSpectrum (𝓞 L))} {Ψ : HeckeEigensystem L ℂ}
    (hfib : ∀ 𝔓₁ ∉ SL, ∀ 𝔓₂ ∉ SL, 𝔓₁.under (𝓞 K) = 𝔓₂.under (𝓞 K) →
      (𝔓₁.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₁.asIdeal = (𝔓₂.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Ψ.a 𝔓₁ = Ψ.a 𝔓₂ ∧ Ψ.b 𝔓₁ = Ψ.b 𝔓₂)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ SL) (hw' : σ • w ∉ SL) :
    Ψ.a (σ • w) = Ψ.a w ∧ Ψ.toRawCentral.b (σ • w) = Ψ.toRawCentral.b w := by
  obtain ⟨ha, hb⟩ := hfib (σ • w) hw' w hw (under_smul σ w) (inertiaDeg_smul σ w)
  refine ⟨ha, ?_⟩
  rw [HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b, cNorm_smul, hb]

private theorem isIsotypicCuspFormAt_twist (σ : L ≃ₐ[K] L) (c u₀ d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L))
    {ξ : (pinsL L (window L c u₀ d₁ d₂ T)).Z →* ℂˣ} {NK : Ideal (𝓞 K)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ w.under (𝓞 K) ∈ SK)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) {Ψ : HeckeEigensystem L ℂ}
    (hfib : ∀ 𝔓₁ ∉ SL, ∀ 𝔓₂ ∉ SL, 𝔓₁.under (𝓞 K) = 𝔓₂.under (𝓞 K) →
      (𝔓₁.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₁.asIdeal = (𝔓₂.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Ψ.a 𝔓₁ = Ψ.a 𝔓₂ ∧ Ψ.b 𝔓₁ = Ψ.b 𝔓₂)
    (hstab : ∀ τ : L ≃ₐ[K] L, ∀ x ∈ UN L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK),
      sigmaAdelicAct K L Dsc τ x ∈ UN L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK))
    (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (h : IsIsotypicCuspFormAt L (pinsL L (window L c u₀ d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ f) :
    IsIsotypicCuspFormAt L (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T)))
      (twistChar Dsc σ (window L c u₀ d₁ d₂ (transportT Dsc σ T)) ξ) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
      (sigmaSectionActOn K L Dsc σ f) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  obtain ⟨hls, hL2⟩ := (lsXiMemberAt_iff (𝓞 L) L (pinsL L (window L c u₀ d₁ d₂ T)).μ
    (pinsL L (window L c u₀ d₁ d₂ T)).Z ξ (pinsL L (window L c u₀ d₁ d₂ T)).D f).mp h.smoothCusp.1.1
  have hauto : IsAutomorphicFnAt L (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T)))
      (twistChar Dsc σ (window L c u₀ d₁ d₂ (transportT Dsc σ T)) ξ) (sigmaSectionActOn K L Dsc σ f) :=
    (lsXiMemberAt_iff (𝓞 L) L (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T))).μ
      (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T))).Z _ (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T))).D
      _).mpr
      ⟨⟨twist_left_invariant Dsc σ hls.left_invariant, twist_central_transform Dsc σ hls.central_transform⟩,
        memLp_twist_window Dsc σ c u₀ d₁ d₂ T hL2⟩
  have hsmooth : IsSmoothCuspAutomorphicFnAt L (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T)))
      (twistChar Dsc σ (window L c u₀ d₁ d₂ (transportT Dsc σ T)) ξ) (sigmaSectionActOn K L Dsc σ f) :=
    ⟨⟨hauto, isCuspidalFn_twist Dsc σ hls.left_invariant h.smoothCusp.1.2⟩, isKfSmooth_twist Dsc σ h.smoothCusp.2⟩
  refine ⟨hsmooth, continuous_sigmaSectionActOn K L Dsc σ h.continuous, fun g k hk => ?_, fun w hw => ?_,
    fun w hw g => ?_⟩
  · exact twist_right_invariant Dsc σ (hstab σ) h.level_invariant g k hk
  · have hw' : σ • w ∉ SL := fun hc => hw ((smul_mem_SL_iff σ hSL w).mp hc)
    have ha := (toRawCentral_b_smul σ hfib hw hw').1
    have hE := isHeckeCosetEigenfunctionAt_twist Dsc σ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) hstab
      (h.hecke_eigen (σ • w) hw')
    rw [ha] at hE
    exact hE
  · have hw' : σ • w ∉ SL := fun hc => hw ((smul_mem_SL_iff σ hSL w).mp hc)
    have hb := (toRawCentral_b_smul σ hfib hw hw').2
    have hC := central_eigen_twist Dsc σ (N := Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) h.level_invariant
      (idealBound_map_eq_one_of_not_mem hSL hNS hN hw')
      (h.central_eigen (σ • w) hw') g
    rw [hb] at hC
    exact hC

end Assembly

end Q09StabH
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar NumberField.AdelicVolume
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain MeasureTheory HeckeIntegralSeam
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm AutomorphicForm.SmoothCusp"
open scoped NumberField.PlaceTransport

namespace Q09StabH

section Glue

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (Dsc : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

omit [NumberField K] in
private theorem twistedConvOp_zero (σ : L ≃ₐ[K] L) (φ : AdelicGL2 (𝓞 L) L → ℂ) : twistedConvOp K L Dsc σ φ 0 = 0 := by
  have h := twistedConvOp_smul K L Dsc σ φ 0 0
  rwa [zero_smul, zero_smul] at h

omit [NumberField K] in
private theorem mem_isotypicCuspSubmodule_of_twistChar
    (σ : L ≃ₐ[K] L) {X : Set (AdelicGL2 (𝓞 L) L)} {ξ : (pinsL L X).Z →* ℂˣ}
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) {S : Finset (HeightOneSpectrum (𝓞 L))} {Ψ : HeckeEigensystem L ℂ}
    {g v : AdelicGL2 (𝓞 L) L → ℂ} (hg : IsIsotypicCuspFormAt L (pinsL L X) ξ N S Ψ g) (hg0 : g = 0 → v = 0)
    (hv : IsIsotypicCuspFormAt L (pinsL L X) (twistChar Dsc σ X ξ) N S Ψ v) :
    v ∈ isotypicCuspSubmodule L (pinsL L X) ξ N S Ψ := by
  by_cases hv0 : v = 0
  · rw [hv0]
    exact Submodule.zero_mem _
  · have hg' : g ≠ 0 := fun h => hv0 (hg0 h)
    have hξ : ξ = twistChar Dsc σ X ξ := centralChar_eq_of_isIsotypicCuspFormAt hN hg hg' hv hv0
    have key := hv.mem_isotypicCuspSubmodule
    rwa [← hξ] at key

private theorem twistedConvOp_mem_isotypicCuspSubmodule
    (σ : L ≃ₐ[K] L) (c u₀ d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L))
    {ξ : (pinsL L (window L c u₀ d₁ d₂ T)).Z →* ℂˣ} {NK : Ideal (𝓞 K)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {SL : Finset (HeightOneSpectrum (𝓞 L))} (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ w.under (𝓞 K) ∈ SK)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK) {Ψ : HeckeEigensystem L ℂ}
    (hfib : ∀ 𝔓₁ ∉ SL, ∀ 𝔓₂ ∉ SL, 𝔓₁.under (𝓞 K) = 𝔓₂.under (𝓞 K) →
      (𝔓₁.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₁.asIdeal = (𝔓₂.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Ψ.a 𝔓₁ = Ψ.a 𝔓₂ ∧ Ψ.b 𝔓₁ = Ψ.b 𝔓₂)
    (hstab : ∀ τ : L ≃ₐ[K] L, ∀ x ∈ UN L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK),
      sigmaAdelicAct K L Dsc τ x ∈ UN L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK))
    (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥) {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ)
    (hconv : ∀ v : AdelicGL2 (𝓞 L) L → ℂ,
      IsIsotypicCuspFormAt L (pinsL L (window L c u₀ d₁ d₂ (transportT Dsc σ T)))
        (twistChar Dsc σ (window L c u₀ d₁ d₂ (transportT Dsc σ T)) ξ) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ v →
      IsIsotypicCuspFormAt L (pinsL L (window L c u₀ d₁ d₂ T)) (twistChar Dsc σ (window L c u₀ d₁ d₂ T) ξ)
        (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ (rightConv L v φ))
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (pinsL L (window L c u₀ d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK)
      SL Ψ) :
    twistedConvOp K L Dsc σ φ u
      ∈ isotypicCuspSubmodule L (pinsL L (window L c u₀ d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ := by
  refine Submodule.span_induction (p := fun u _ => twistedConvOp K L Dsc σ φ u
    ∈ isotypicCuspSubmodule L (pinsL L (window L c u₀ d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ)
    ?_ ?_ ?_ ?_ hu
  · intro g hg
    exact mem_isotypicCuspSubmodule_of_twistChar Dsc σ hN hg (fun h => by rw [h, twistedConvOp_zero])
      (hconv _ (isIsotypicCuspFormAt_twist Dsc σ c u₀ d₁ d₂ T hSL hNS hfib hstab hN hg))
  · simp only [twistedConvOp_zero, Submodule.zero_mem]
  · intro x y hx hy ihx ihy
    rw [twistedConvOp_add K L Dsc σ hφc hφs (continuous_of_mem_isotypicCuspSubmodule hx)
      (continuous_of_mem_isotypicCuspSubmodule hy)]
    exact Submodule.add_mem _ ihx ihy
  · intro a x _ ih
    rw [twistedConvOp_smul]
    exact Submodule.smul_mem _ a ih

end Glue
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end Q09StabH
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section CTpart

noncomputable section

namespace Q09

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section Transport

variable {H G : Type*} [Group H] [Group G]

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section ConvTransport

open MeasureTheory

variable {H G : Type*} [Group H] [Group G]

private theorem conv_integrand_eq (u θ : G → ℂ) (k y x : G) :
    u (y * k * (k⁻¹ * x)) * θ (k⁻¹ * x)⁻¹ = u (y * x) * θ (x⁻¹ * k) := by
  rw [mul_assoc, mul_inv_cancel_left, mul_inv_rev, inv_inv]

variable [MeasurableSpace G] (μ : Measure G) (u : G → ℂ)

private def convDomain : Submodule ℂ (G → ℂ) where
  carrier := {θ | ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ}
  zero_mem' := by
    intro y
    simp
  add_mem' := by
    intro θ₁ θ₂ h₁ h₂ y
    have e : (fun x => u (y * x) * (θ₁ + θ₂) x⁻¹) =
        fun x => u (y * x) * θ₁ x⁻¹ + u (y * x) * θ₂ x⁻¹ :=
      funext fun x => by simp only [Pi.add_apply, mul_add]
    rw [e]
    exact (h₁ y).add (h₂ y)
  smul_mem' := by
    intro c θ h y
    have e : (fun x => u (y * x) * (c • θ) x⁻¹) = fun x => c * (u (y * x) * θ x⁻¹) :=
      funext fun x => by simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [e]
    exact (h y).const_mul c

private theorem mem_convDomain_iff (θ : G → ℂ) :
    θ ∈ convDomain μ u ↔ ∀ y : G, Integrable (fun x => u (y * x) * θ x⁻¹) μ :=
  Iff.rfl

private def convOpOn : convDomain μ u →ₗ[ℂ] (G → ℂ) where
  toFun θ := fun y => ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
  map_add' θ₁ θ₂ := funext fun y => by
    have h₁ := (mem_convDomain_iff μ u _).mp θ₁.2 y
    have h₂ := (mem_convDomain_iff μ u _).mp θ₂.2 y
    show (∫ x, u (y * x) * ((θ₁ : G → ℂ) + (θ₂ : G → ℂ)) x⁻¹ ∂μ) =
      (∫ x, u (y * x) * (θ₁ : G → ℂ) x⁻¹ ∂μ) + ∫ x, u (y * x) * (θ₂ : G → ℂ) x⁻¹ ∂μ
    rw [← integral_add h₁ h₂]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [Pi.add_apply, mul_add])
  map_smul' c θ := funext fun y => by
    show (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = c * ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ
    have e : (∫ x, u (y * x) * (c • (θ : G → ℂ)) x⁻¹ ∂μ) = ∫ x, c * (u (y * x) * (θ : G → ℂ) x⁻¹) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm])
    rw [e]
    exact integral_const_mul c _

private theorem convOpOn_apply (θ : convDomain μ u) (y : G) :
    convOpOn μ u θ y = ∫ x, u (y * x) * (θ : G → ℂ) x⁻¹ ∂μ :=
  rfl

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

private theorem comp_mul_mem_convDomain {θ : G → ℂ} (hθ : θ ∈ convDomain μ u) (k : G) :
    (fun x => θ (x * k)) ∈ convDomain μ u := by
  rw [mem_convDomain_iff] at hθ ⊢
  intro y
  refine ((hθ (y * k)).comp_mul_left k⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  exact conv_integrand_eq u θ k y x

private theorem convOpOn_comp_mul (θ : convDomain μ u) (k : G)
    (hk : (fun x => (θ : G → ℂ) (x * k)) ∈ convDomain μ u) (y : G) :
    convOpOn μ u ⟨fun x => (θ : G → ℂ) (x * k), hk⟩ y = convOpOn μ u θ (y * k) := by
  simp only [convOpOn_apply]
  rw [← integral_mul_left_eq_self (fun x => u (y * k * x) * (θ : G → ℂ) x⁻¹) k⁻¹]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (conv_integrand_eq u (θ : G → ℂ) k y x).symm)

private theorem convOpOn_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)]
    [∀ j, Module ℂ (W j)] {ι : H →* G} (hι : Function.Injective ι) (ρ : ∀ j, Representation ℂ H (W j))
    (θ : convDomain μ u) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    convOpOn μ u θ ∈ ⨆ j, typeSubmodule ι (ρ j) :=
  mem_iSup_typeSubmodule_of_intertwines ι hι ρ (convDomain μ u)
    (fun k _ hθ' => comp_mul_mem_convDomain μ u hθ' (ι k)) (convOpOn μ u)
    (fun k θ' y => convOpOn_comp_mul μ u θ' (ι k) _ y) θ hθ

end ConvTransport
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end Q09
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end CTpart
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section CONV1part

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm IsDedekindDomain MeasureTheory FLT.SmoothVectors"
open scoped ProbabilityTheory

noncomputable section

namespace Q09StabH
namespace ConvLeg

private abbrev pinsL (L : Type) [Field L] [NumberField L] (X : Set (AdelicGL2 (𝓞 L) L)) : CarrierPins L :=
  productionPinsOf L X (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
    (adelicBox L)

private abbrev _root_.Q09StabH.ConvLeg.window (L : Type) [Field L] [NumberField L] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    Set (AdelicGL2 (𝓞 L) L) :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet L c u d₁ d₂

p2m_export "Q09StabH.ConvLeg" "window"
section Pins

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem mem_Z (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : z ∈ (pinsL L X).Z := by
  show z ∈ (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ)
  exact Subgroup.mem_top z

private def toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) : (pinsL L X).Z := ⟨z, mem_Z X z⟩

@[scoped simp] private theorem coe_toZ (X : Set (AdelicGL2 (𝓞 L) L)) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ((toZ X z : (pinsL L X).Z) : (AdeleRing (𝓞 L) L)ˣ) = z := rfl

private theorem toZ_coe (X : Set (AdelicGL2 (𝓞 L) L)) (z : (pinsL L X).Z) : toZ X (z : (AdeleRing (𝓞 L) L)ˣ) = z :=
  Subtype.ext rfl

end Pins
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section Interchange

private noncomputable def integralCLM {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ] :
    C(Y, ℂ) →L[ℝ] ℂ :=
  haveI : IsFiniteMeasureOnCompacts ρ :=
    isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace.mp inferInstance
  have hint : ∀ F : C(Y, ℂ), Integrable (fun y => F y) ρ := fun F =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  LinearMap.mkContinuous
    { toFun := fun F => ∫ y, F y ∂ρ
      map_add' := fun F₁ F₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint F₁) (hint F₂)
      map_smul' := fun r F => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul r fun y => F y }
    (ρ.real Set.univ) fun F => by
      refine (norm_integral_le_of_norm_le_const (μ := ρ)
        (Filter.Eventually.of_forall fun y => F.norm_coe_le_norm y)).trans ?_
      rw [mul_comm]

private theorem integralCLM_apply {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ]
    (F : C(Y, ℂ)) : integralCLM ρ F = ∫ y, F y ∂ρ :=
  rfl

section Slices

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  {Q : Type*} [TopologicalSpace Q] (S : Set Q)
  {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ} (hf : Continuous f)
  (g : G)

private def sliceFn : C(G × S, ℂ) :=
  ⟨fun p => φ (u p.2 * g * p.1) * f p.1, by fun_prop⟩

private noncomputable def slice (x : G) : C(S, ℂ) :=
  (sliceFn S hu hφ hf g).curry x

private theorem slice_apply (x : G) (q : S) : slice S hu hφ hf g x q = φ (u q * g * x) * f x :=
  rfl

private theorem continuous_slice : Continuous (slice S hu hφ hf g) :=
  (sliceFn S hu hφ hf g).curry.continuous

private theorem hasCompactSupport_slice (hfs : HasCompactSupport f) :
    HasCompactSupport (slice S hu hφ hf g) := by
  refine hfs.mono fun x hx => ?_
  rw [Function.mem_support] at hx ⊢
  intro hfx
  apply hx
  ext q
  rw [slice_apply, hfx, mul_zero, ContinuousMap.zero_apply]

end Slices
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

private theorem integral_integral_eq_zero
    {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
    [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    {Q : Type*} [TopologicalSpace Q] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (ν : Measure Q) [IsFiniteMeasure ν] {S : Set Q} (hS : IsCompact S) (hνS : ∀ᵐ q ∂ν, q ∈ S)
    {u : Q → G} (hu : Continuous u) {φ : G → ℂ} (hφ : Continuous φ) {f : G → ℂ}
    (hf : Continuous f) (hfs : HasCompactSupport f) (g : G)
    (hzero : ∀ h : G, ∫ q, φ (u q * h) ∂ν = 0) :
    ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν = 0 := by
  haveI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hνS

  have hsub : ∀ h : Q → ℂ, ∫ q : S, h q ∂(ν.comap Subtype.val) = ∫ q, h q ∂ν := fun h => by
    rw [integral_subtype_comap hSm, hres]
  have hΦi : Integrable (slice S hu hφ hf g) μ :=
    (continuous_slice S hu hφ hf g).integrable_of_hasCompactSupport
      (hasCompactSupport_slice S hu hφ hf g hfs)

  have hJΦ : ∀ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) = 0 :=
    fun x => by
      rw [integralCLM_apply]
      simp only [slice_apply]
      rw [hsub fun q => φ (u q * g * x) * f x, integral_mul_const]
      simp only [mul_assoc]
      rw [hzero (g * x), zero_mul]

  have hev : ∀ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q = ∫ x, φ (u q * g * x) * f x ∂μ :=
    fun q => by
      rw [ContinuousMap.integral_apply hΦi q]
      simp only [slice_apply]
  calc ∫ q, (∫ x, φ (u q * g * x) * f x ∂μ) ∂ν
      = ∫ q : S, (∫ x, slice S hu hφ hf g x ∂μ) q ∂(ν.comap (Subtype.val : S → Q)) := by
        rw [← hsub fun q => ∫ x, φ (u q * g * x) * f x ∂μ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun q => (hev q).symm)
    _ = integralCLM (ν.comap (Subtype.val : S → Q)) (∫ x, slice S hu hφ hf g x ∂μ) :=
        (integralCLM_apply _ _).symm
    _ = ∫ x, integralCLM (ν.comap (Subtype.val : S → Q)) (slice S hu hφ hf g x) ∂μ :=
        (ContinuousLinearMap.integral_comp_comm _ hΦi).symm
    _ = 0 := by simp only [hJΦ, integral_zero]

end Interchange
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

section Conv

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isFactorizableTestFn_of_tier {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) : IsFactorizableTestFn L φ := by
  obtain ⟨φa, φf, φS, h₁, h₂, -, -, -, h₆⟩ := hφ.1.2
  exact ⟨φa, φf, h₁, h₂, h₆⟩

private theorem rightConv_mul_eq_of_tier {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (g : AdelicGL2 (𝓞 L) L) {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ U) :
    rightConv L u φ (g * k) = rightConv L u φ g := by
  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply L u φ g k]
  have hφk : (fun y => φ (k⁻¹ * y)) = φ := funext fun y => (hφ.1.1 k⁻¹ (inv_mem hk) y).1
  rw [hφk]

private theorem measurableSet_window (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; MeasurableSet (window L c v d₁ d₂ T)) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  haveI := borelSpace_glBorel (Fin 2) (𝓞 L) L
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  have himg : (· * x) '' centreCutSiegelSet L c v d₁ d₂ = (· * x⁻¹) ⁻¹' centreCutSiegelSet L c v d₁ d₂ := by
    ext g
    simp [Set.mem_preimage]
  rw [himg]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet (F := L) c v d₁ d₂)

private theorem measure_window_lt_top {c : ℝ} (hc : 0 < c) (v : ℝ) {d₁ : ℝ} (hd₁ : 0 < d₁) (d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 L) L)) :
    (letI := glBorel (Fin 2) (𝓞 L) L; adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤) := by
  letI := glBorel (Fin 2) (𝓞 L) L
  refine (measure_biUnion_finset_le T _).trans_lt (ENNReal.sum_lt_top.mpr fun x _ => ?_)
  exact adelicGLHaar_mul_right_centreCutSiegelSet_lt_top L hc v hd₁ d₂ x

private theorem isIsotypicCuspFormAt_rightConv_of_hecke
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (c' v' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 L) L)) (hd' : d₁' < d₂')
    (hcov' : CoversModCentre L (window L c' v' d₁' d₂' T'))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L (window L c' v' d₁' d₂' T')).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {N : Ideal (𝓞 L)} (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : IsIsotypicCuspFormAt L (pinsL L (window L c' v' d₁' d₂' T')) ξ' N S Ψ u)
    (hhecke : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ S →
      IsHeckeCosetEigenfunctionAt L ((pinsL L (window L c v d₁ d₂ T)).U N) ((pinsL L (window L c v d₁ d₂ T)).gen w)
        w (rightConv L u φ) (Ψ.a w)) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ N S Ψ (rightConv L u φ) := by
  have hfact : IsFactorizableTestFn L φ := isFactorizableTestFn_of_tier hφ
  obtain ⟨hφc, hφs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ hfact
  have hucont : Continuous u := hu.continuous
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L
  haveI : IsProbabilityMeasure ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) :=
    isProbabilityMeasure_cond_adelicBox L

  have hls : IsLsXiFunction (𝓞 L) L (pinsL L (window L c' v' d₁' d₂' T')).Z ξ' u :=
    ((lsXiMemberAt_iff (𝓞 L) L _ _ ξ' _ u).mp hu.smoothCusp.1.1).1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk => rightConv_mul_eq_of_tier hφ u g hk

  have hcont : Continuous (rightConv L u φ) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn L u hucont φ hfact).1
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, hcont, hlevel, hhecke, ?_⟩
  ·

    refine (lsXiMemberAt_iff (𝓞 L) L _ _ ξ _ _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · intro γ g
      show (∫ x, u (globalPoints (𝓞 L) L γ * g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [mul_assoc, hls.left_invariant])
    · intro z g
      have hz : ∀ y : AdelicGL2 (𝓞 L) L,
          u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * y) =
            ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) * u y :=
        fun y => hls.central_transform (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) y
      have hval : ((ξ' (toZ _ (z : (AdeleRing (𝓞 L) L)ˣ)) : ℂˣ) : ℂ) = ((ξ z : ℂˣ) : ℂ) := by
        rw [hξ, toZ_coe]
      show (∫ x, u (centralScalar (𝓞 L) L (z : (AdeleRing (𝓞 L) L)ˣ) * g * x) * φ x
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        ((ξ z : ℂˣ) : ℂ) * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
      rw [← hval]
      exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
        rw [mul_assoc, hz, mul_assoc])).trans (integral_const_mul _ _)
    ·
      have hbdd : IsBoundedOnSiegelWindows L (rightConv L u φ) :=
        isBoundedOnSiegelWindows_rightConv_of_isCuspAutomorphicFnAt_of_coversModCentre L c' v' d₁' d₂' T' hd'
          hcov' ξ' u hu.smoothCusp.1 hucont φ hfact
      obtain ⟨C, hC⟩ := hbdd c v d₁ d₂ T hc hd₁
      have hlt : adelicGLHaar (Fin 2) (𝓞 L) L (window L c v d₁ d₂ T) < ⊤ := measure_window_lt_top hc v hd₁ d₂ T
      haveI : IsFiniteMeasure ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact hlt⟩
      show MemLp (rightConv L u φ) 2 ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (window L c v d₁ d₂ T))
      refine MemLp.of_bound hcont.aestronglyMeasurable C ?_
      exact ae_restrict_of_forall_mem (measurableSet_window c v d₁ d₂ T) hC
  ·
    intro g
    obtain ⟨S₀, hS₀, hBS⟩ := exists_isCompact_adelicBox_subset L
    have hνS : ∀ᵐ q ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]), q ∈ S₀ :=
      (ProbabilityTheory.ae_cond_mem (measurableSet_adelicBox L)).mono fun q hq => hBS hq
    have hcusp : ∀ h : AdelicGL2 (𝓞 L) L,
        ∫ q, u (unipotentGL2 q * h) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0 :=
      fun h => hu.smoothCusp.1.2 h
    show ∫ q, rightConv L u φ (unipotentGL2 q * g) ∂((adelicAddHaar (𝓞 L) L)[|adelicBox L]) = 0
    exact integral_integral_eq_zero (adelicGLHaar (Fin 2) (𝓞 L) L) ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) hS₀
      hνS continuous_unipotentGL2 hucont hφc hφs g hcusp
  ·
    rw [isKfSmooth_iff, isSmoothVector_iff_exists_isOpen_subgroup]
    refine ⟨(levelOne (𝓞 L) L N).comap (finiteAdelicGL2Subgroup L).subtype, ?_, ?_⟩
    · rw [Subgroup.coe_comap, Subgroup.coe_subtype]
      exact (isOpen_levelOne (𝓞 L) L hN).preimage continuous_subtype_val
    · intro w hw
      rw [Subgroup.smul_def]
      exact RightTranslationFn.ext fun x =>
        hlevel x w (Subgroup.mem_inf.mpr ⟨Subgroup.mem_comap.mp hw, w.2⟩)
  ·
    intro w hw g
    have hce : ∀ y : AdelicGL2 (𝓞 L) L,
        u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * y) =
          Ψ.toRawCentral.b w * u y :=
      fun y => hu.central_eigen w hw y
    show (∫ x, u (centralScalar (𝓞 L) L (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w)) * g * x) * φ x
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      Ψ.toRawCentral.b w * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    exact (integral_congr_ae (Filter.Eventually.of_forall fun x => by
      rw [mul_assoc, hce, mul_assoc])).trans (integral_const_mul _ _)

end Conv
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV1part
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section CONV2part

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm AutomorphicForm.SmoothCusp AdelicDock IsDedekindDomain MeasureTheory"

noncomputable section

namespace Q09StabH
namespace ConvLeg

section OnePlace

variable {L : Type} [Field L] [NumberField L]

private def placeAt (w : HeightOneSpectrum (𝓞 L)) : GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

variable (w : HeightOneSpectrum (𝓞 L))

private theorem glArch_placeAt (m : GL (Fin 2) (w.adicCompletion L)) : glArch (𝓞 L) L (placeAt w m) = 1 :=
  glArch_finEmbed (𝓞 L) L _

private theorem finComponent_glFin_placeAt_self (m : GL (Fin 2) (w.adicCompletion L)) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (placeAt w m)) = m := by
  show finComponent (𝓞 L) L w (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = m
  rw [glFin_finEmbed, finComponent_localEmbed_self]

private theorem finComponent_glFin_placeAt_of_ne (m : GL (Fin 2) (w.adicCompletion L)) {w' : HeightOneSpectrum (𝓞 L)}
    (h : w' ≠ w) : finComponent (𝓞 L) L w' (glFin (𝓞 L) L (placeAt w m)) = 1 := by
  show finComponent (𝓞 L) L w' (glFin (𝓞 L) L (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m))) = 1
  rw [glFin_finEmbed, finComponent_localEmbed_of_ne (𝓞 L) L w m h]

variable {w}

private theorem adelicGL2_ext {a b : AdelicGL2 (𝓞 L) L} (h₁ : glArch (𝓞 L) L a = glArch (𝓞 L) L b)
    (h₂ : ∀ w' : HeightOneSpectrum (𝓞 L),
      finComponent (𝓞 L) L w' (glFin (𝓞 L) L a) = finComponent (𝓞 L) L w' (glFin (𝓞 L) L b)) : a = b := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  refine Prod.ext ?_ ?_
  · have h := congrArg
      (fun g : GL (Fin 2) (InfiniteAdeleRing L) => (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) h₁
    simpa only [glArch_apply] using h
  · refine FiniteAdeleRing.ext L fun w' => ?_
    have h := congrArg
      (fun g : GL (Fin 2) (w'.adicCompletion L) => (g : Matrix (Fin 2) (Fin 2) (w'.adicCompletion L)) i j) (h₂ w')
    simpa only [finComponent_apply, glFin_apply] using h

private theorem placeAt_mul_eq_mul_placeAt (m : GL (Fin 2) (w.adicCompletion L)) {y : AdelicGL2 (𝓞 L) L}
    (hy : finComponent (𝓞 L) L w (glFin (𝓞 L) L y) = 1) : placeAt w m * y = y * placeAt w m := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · simp only [map_mul, glArch_placeAt, one_mul, mul_one]
  · simp only [map_mul]
    by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self, hy, mul_one, one_mul]
    · rw [finComponent_glFin_placeAt_of_ne w m h, one_mul, mul_one]

private theorem finComponent_glFin_mul_inv_placeAt (x : AdelicGL2 (𝓞 L) L) :
    finComponent (𝓞 L) L w (glFin (𝓞 L) L (x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹)) = 1 := by
  simp only [map_mul, map_inv, finComponent_glFin_placeAt_self, mul_inv_cancel]

private theorem heckeGen_eq_placeAt :
    heckeGen (𝓞 L) L w = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) := by
  refine adelicGL2_ext ?_ fun w' => ?_
  · rw [glArch_placeAt]
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [glArch_apply, Units.val_one]
    exact heckeGenAt_fst _ i j
  · by_cases h : w' = w
    · subst h
      rw [finComponent_glFin_placeAt_self]
    · rw [finComponent_glFin_placeAt_of_ne w _ h]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [finComponent_apply, glFin_apply, Units.val_one]
      exact heckeGenAt_snd_apply_of_ne _ h i j

private theorem normalise_aux {G : Type*} [Group G] {p q h y u₁ u₂ : G} (hy : y = u₁ * p⁻¹) (hq : q = p * h)
    (hcomm : q * y = y * q) : u₁ * h * u₂ = q * (y * u₂) := by
  subst hy
  calc u₁ * h * u₂ = (u₁ * p⁻¹) * (p * h) * u₂ := by group
    _ = (u₁ * p⁻¹) * q * u₂ := by rw [hq]
    _ = q * (u₁ * p⁻¹) * u₂ := by rw [← hcomm]
    _ = q * (u₁ * p⁻¹ * u₂) := by rw [mul_assoc]

private theorem mul_heckeGen_mul_eq (u₁ u₂ : AdelicGL2 (𝓞 L) L) :
    u₁ * heckeGen (𝓞 L) L w * u₂ =
      placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁) *
          finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) *
        ((u₁ * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L u₁)))⁻¹) * u₂) :=
  normalise_aux rfl (by rw [map_mul, ← heckeGen_eq_placeAt])
    (placeAt_mul_eq_mul_placeAt _ (finComponent_glFin_mul_inv_placeAt u₁))

private theorem isLocalLevelOne_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (M : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) (hM : ∀ i j, M i j ∈ w.adicCompletionIntegers L) :
    IsLocalLevelOne (𝓞 L) L w N M :=
  ⟨hM, by rw [hb]; exact hM 1 0, by rw [hb]; exact sub_mem (hM 1 1) (one_mem _)⟩

private theorem placeAt_mem_of_integral {N : Ideal (𝓞 L)} (hb : idealBound (𝓞 L) N w = 1)
    (m : GL (Fin 2) (w.adicCompletion L))
    (hm : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    (hm' : ∀ i j, ((m⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L) :
    placeAt w m ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · show finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w m) ∈ levelOne (𝓞 L) L N
    rw [finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    exact ⟨isLocalLevelOne_of_integral hb _ hm, isLocalLevelOne_of_integral hb _ hm'⟩
  · show glArch (𝓞 L) L (placeAt w m) = 1
    exact glArch_placeAt w m

private theorem finComponent_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (finComponent (𝓞 L) L w (glFin (𝓞 L) L k) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L := by
  rw [finComponent_apply]
  have h : (glFin (𝓞 L) L k : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j ∈ integralFiniteAdeles (𝓞 L) L :=
    (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hk)).1.integral i j
  exact h w

private theorem finComponent_inv_integral_of_mem_levelOne {N : Ideal (𝓞 L)} {k : AdelicGL2 (𝓞 L) L}
    (hk : k ∈ levelOne (𝓞 L) L N) (i j : Fin 2) :
    (((finComponent (𝓞 L) L w (glFin (𝓞 L) L k))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
      Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L := by
  rw [← map_inv, ← map_inv]
  exact finComponent_integral_of_mem_levelOne (inv_mem hk) i j

end OnePlace
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Hecke

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem isHeckeCosetEigenfunctionAt_rightConv {N : Ideal (𝓞 L)} {w : HeightOneSpectrum (𝓞 L)}
    (hb : idealBound (𝓞 L) N w = 1) {tys : ArchTypeFamily L} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) SK φ)
    (hsupp : ∀ x : AdelicGL2 (𝓞 L) L, φ x ≠ 0 →
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hucont : Continuous u)
    (hinv : ∀ h : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u (h * k) = u h)
    {a : ℂ}
    (heu : IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      u a) :
    IsHeckeCosetEigenfunctionAt L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (heckeGen (𝓞 L) L w) w
      (rightConv L u φ) a := by
  obtain ⟨reps, hsys, heig⟩ := heu
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ (isFactorizableTestFn_of_tier hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

  have hdc : ∀ i, ∃ u₁ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      ∃ u₂ ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u₁ * heckeGen (𝓞 L) L w * u₂ = reps i :=
    fun i => HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
  choose u₁ hu₁ u₂ hu₂ hrep using hdc

  obtain ⟨r, hr⟩ : ∃ r : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      r i = placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i)) *
        finComponent (𝓞 L) L w (glFin (𝓞 L) L (heckeGen (𝓞 L) L w))) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : Fin (Ideal.absNorm w.asIdeal + 1) → AdelicGL2 (𝓞 L) L, ∀ i,
      s i = (u₁ i * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))))⁻¹) * u₂ i :=
    ⟨_, fun _ => rfl⟩
  have hreps : reps = fun i => r i * s i := funext fun i => by
    show reps i = r i * s i
    rw [← hrep i, hr, hs]
    exact mul_heckeGen_mul_eq (u₁ i) (u₂ i)
  have hsU : ∀ i, s i ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L := fun i => by
    rw [hs]
    have hp : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L (u₁ i))) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ (finComponent_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
        (finComponent_inv_integral_of_mem_levelOne (Subgroup.mem_inf.mp (hu₁ i)).1)
    exact mul_mem (mul_mem (hu₁ i) (inv_mem hp)) (hu₂ i)

  have heig' : ∀ h : AdelicGL2 (𝓞 L) L, (∑ i, u (h * r i)) = a * u h := fun h => by
    have h1 := heig h
    rw [hreps, heckeCosetSum_mul_right L (fun g k hk => hinv g k hk) r s hsU h] at h1
    exact h1

  have hlevel : ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
      rightConv L u φ (g * k) = rightConv L u φ g := fun g k hk => rightConv_mul_eq_of_tier hφ u g hk

  have hL1 : ∀ h : AdelicGL2 (𝓞 L) L,
      Integrable (fun x => u (h * x) * φ x) (adelicGLHaar (Fin 2) (𝓞 L) L) := fun h =>
    ((hucont.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport hφs.mul_left

  have hpt : ∀ (g x : AdelicGL2 (𝓞 L) L), (∑ i, u (g * r i * x) * φ x) = a * (u (g * x) * φ x) := by
    intro g x
    by_cases hx : φ x = 0
    · simp only [hx, mul_zero, Finset.sum_const_zero]
    obtain ⟨hx₁, hx₂⟩ := hsupp x hx
    have hxw : placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) ∈
        levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
      placeAt_mem_of_integral hb _ hx₁ hx₂

    obtain ⟨x', hx'⟩ : ∃ x' : AdelicGL2 (𝓞 L) L,
        x' = x * (placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)))⁻¹ := ⟨_, rfl⟩
    have hxx : x = x' * placeAt w (finComponent (𝓞 L) L w (glFin (𝓞 L) L x)) := by
      rw [hx', inv_mul_cancel_right]
    have hx'w : finComponent (𝓞 L) L w (glFin (𝓞 L) L x') = 1 := by
      rw [hx']
      exact finComponent_glFin_mul_inv_placeAt x
    have hterm : ∀ i, u (g * r i * x) = u (g * x' * r i) := fun i => by
      have hcr : r i * x' = x' * r i := by
        rw [hr]
        exact placeAt_mul_eq_mul_placeAt _ hx'w
      rw [hxx, ← mul_assoc, hinv _ _ hxw, mul_assoc, hcr, ← mul_assoc]
    rw [← Finset.sum_mul, ← mul_assoc]
    congr 1
    simp only [hterm]
    rw [heig' (g * x'), hxx, ← mul_assoc, hinv _ _ hxw]

  refine ⟨reps, hsys, fun g => ?_⟩
  have hsum : heckeCosetSum L reps (rightConv L u φ) g = heckeCosetSum L r (rightConv L u φ) g := by
    rw [hreps]
    exact heckeCosetSum_mul_right L (fun h k hk => hlevel h k hk) r s hsU g
  rw [hsum]
  show (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
    a * ∫ x, u (g * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
  have hswap : (∑ i, ∫ x, u (g * r i * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    (integral_finsetSum Finset.univ fun i _ => hL1 (g * r i)).symm
  have hpt' : (∫ x, (∑ i, u (g * r i * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, a * (u (g * x) * φ x) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => hpt g x)
  rw [hswap, hpt', integral_const_mul]

end Hecke
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV2part
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section CONV3part

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm IsDedekindDomain MeasureTheory"
open scoped TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace Q09StabH
namespace ConvLeg

section Dictionary

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (v : HeightOneSpectrum (𝓞 K))

private theorem semiLocalHomeomorph_semiLocalEval (a : FiniteAdeleRing (𝓞 L) L) (w : v.Extension (𝓞 L)) :
    semiLocalHomeomorph K L v (semiLocalEval K L v a) w = AdelicLevel.finAdeleEval (𝓞 L) L w.1 a := by
  show HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
      ((HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v).symm
        (fun w' : v.Extension (𝓞 L) => AdelicLevel.finAdeleEval (𝓞 L) L w'.1 a)) w =
    AdelicLevel.finAdeleEval (𝓞 L) L w.1 a
  rw [AlgEquiv.apply_symm_apply]

private theorem forall_of_mem_semiLocalIntegers (t : L ⊗[K] v.adicCompletion K) (ht : t ∈ semiLocalIntegers K L v)
    (w : v.Extension (𝓞 L)) : semiLocalHomeomorph K L v t w ∈ w.1.adicCompletionIntegers L := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, piIntegers, Set.mem_univ_pi] at ht
  exact ht w

end Dictionary
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Discharge

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem finComponent_integral_of_ne_zero {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : w.under (𝓞 K) ∉ SK) (x : AdelicGL2 (𝓞 L) L) (hx : φ x ≠ 0) :
      (∀ i j, (finComponent (𝓞 L) L w (glFin (𝓞 L) L x) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
          w.adicCompletionIntegers L) ∧
      (∀ i j, (((finComponent (𝓞 L) L w (glFin (𝓞 L) L x))⁻¹ : GL (Fin 2) (w.adicCompletion L)) :
          Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L)
    := by
  obtain ⟨φa, φf, φS, -, -, -, -, h₅, h₆⟩ := hφ.1.2
  have hf : φf (glFin (𝓞 L) L x) ≠ 0 := fun h0 => hx (by rw [h₆ x, h0, mul_zero])
  have hmem : semiLocalComponent K L (w.under (𝓞 K)) (glFin (𝓞 L) L x) ∈
      semiLocalIntegralSet K L (w.under (𝓞 K)) := by
    by_contra hc
    exact hf (h₅ _ ⟨w.under (𝓞 K), hw, hc⟩)
  unfold semiLocalIntegralSet at hmem
  obtain ⟨hm, hm'⟩ := mem_integralUnitsSet.mp hmem

  let wE : {w' : HeightOneSpectrum (𝓞 L) // w'.under (𝓞 K) = w.under (𝓞 K)} := ⟨w, rfl⟩
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((glFin (𝓞 L) L x : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ (hm i j) wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    exact h
  · have hm'' := hm' i j
    rw [← map_inv (semiLocalComponent K L (w.under (𝓞 K))) (glFin (𝓞 L) L x)] at hm''
    have h : semiLocalHomeomorph K L (w.under (𝓞 K))
        (semiLocalEval K L (w.under (𝓞 K))
          ((((glFin (𝓞 L) L x)⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
            Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) i j)) wE ∈
        w.adicCompletionIntegers L :=
      forall_of_mem_semiLocalIntegers K L (w.under (𝓞 K)) _ hm'' wE
    rw [semiLocalHomeomorph_semiLocalEval] at h
    rw [← map_inv (finComponent (𝓞 L) L w) (glFin (𝓞 L) L x)]
    exact h

private theorem isIsotypicCuspFormAt_rightConv_of_tier
    (c v d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 L) L)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (c' v' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 L) L)) (hd' : d₁' < d₂')
    (hcov' : CoversModCentre L (window L c' v' d₁' d₂' T'))
    (ξ : (pinsL L (window L c v d₁ d₂ T)).Z →* ℂˣ) (ξ' : (pinsL L (window L c' v' d₁' d₂' T')).Z →* ℂˣ)
    (hξ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' (toZ _ z) = ξ (toZ _ z))
    {NK : Ideal (𝓞 K)} (hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥)
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {SL : Finset (HeightOneSpectrum (𝓞 L))}
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ w.under (𝓞 K) ∈ SK)
    (hbound : ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
      idealBound (𝓞 L) (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) w = 1)
    (Ψ : HeckeEigensystem L ℂ) {tys : ArchTypeFamily L} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ)
    {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : IsIsotypicCuspFormAt L (pinsL L (window L c' v' d₁' d₂' T')) ξ'
      (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ u) :
    IsIsotypicCuspFormAt L (pinsL L (window L c v d₁ d₂ T)) ξ (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
      (rightConv L u φ) :=
  isIsotypicCuspFormAt_rightConv_of_hecke c v d₁ d₂ T hc hd₁ c' v' d₁' d₂' T' hd' hcov' ξ ξ' hξ hN SL Ψ hφ hu
    fun w hw =>
      isHeckeCosetEigenfunctionAt_rightConv (hbound w hw) hφ
        (fun x hx => finComponent_integral_of_ne_zero hφ (fun h => hw ((hSL w).mpr h)) x hx)
        hu.continuous hu.level_invariant (hu.hecke_eigen w hw)

end Discharge
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section Arch

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private theorem rightConv_mem_archCutSubmodule {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)}
    {SK : Finset (HeightOneSpectrum (𝓞 K))} {φ : AdelicGL2 (𝓞 L) L → ℂ}
    (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ)
    (hinj : ∀ w : InfinitePlace L, Function.Injective (rowIsometryInclAt₀ L w))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : Continuous u) : rightConv L u φ ∈ archCutSubmodule L tys := by
  obtain ⟨hφc, hφs⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ (isFactorizableTestFn_of_tier hφ)
  letI : MeasurableSpace (AdelicGL2 (𝓞 L) L) := glBorel (Fin 2) (𝓞 L) L
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hdom : (fun x => φ x⁻¹) ∈ Q09.convDomain (adelicGLHaar (Fin 2) (𝓞 L) L) u := by
    rw [Q09.mem_convDomain_iff]
    intro y
    simp only [inv_inv]
    exact ((hu.comp (continuous_const.mul continuous_id)).mul hφc).integrable_of_hasCompactSupport
      hφs.mul_left
  have hconv : Q09.convOpOn (adelicGLHaar (Fin 2) (𝓞 L) L) u ⟨fun x => φ x⁻¹, hdom⟩ = rightConv L u φ := by
    funext y
    rw [Q09.convOpOn_apply]
    show (∫ x, u (y * x) * (fun x => φ x⁻¹) x⁻¹ ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      ∫ x, u (y * x) * φ x ∂(adelicGLHaar (Fin 2) (𝓞 L) L)
    simp only [inv_inv]
  rw [mem_archCutSubmodule_iff]
  intro w
  rw [← hconv]
  exact Q09.convOpOn_mem_iSup_typeSubmodule _ u (hinj w) (fun i => (tys.rep w i).ρ) _
    ((mem_archCutSubmodule_iff L tys _).mp hφ.2.1 w)

private theorem twistedConvOp_mem_archCutSubmodule (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    {tys : ArchTypeFamily L} {U : Subgroup (AdelicGL2 (𝓞 L) L)} {SK : Finset (HeightOneSpectrum (𝓞 K))}
    {φ : AdelicGL2 (𝓞 L) L → ℂ} (hφ : IsUnitFactorizableAboveOfType K L tys U SK φ)
    (hinj : ∀ w : InfinitePlace L, Function.Injective (rowIsometryInclAt₀ L w))
    {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : Continuous u) : twistedConvOp K L D σ φ u ∈ archCutSubmodule L tys :=
  rightConv_mem_archCutSubmodule hφ hinj (continuous_sigmaSectionActOn K L D σ hu)

end Arch
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end Q09StabH.ConvLeg
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end CONV3part
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section

p2m_open "NumberField NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

namespace Q09RowIso

variable (F : Type) [Field F]

private theorem archComponent_archRowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
  archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

private theorem archRowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_archRowIsometryInclAt₀ F w a
  have hb := archComponent_archRowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

variable [NumberField F]

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archRowIsometryInclAt₀ F w k

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

private theorem forall_rowIsometryInclAt₀_injective :
    ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w) :=
  rowIsometryInclAt₀_injective F

end Q09RowIso
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.AutomorphicForm"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (cL uL d₁L d₂L : ℝ) (TL : Finset (AdelicGL2 (𝓞 L) L))
    (hdL : d₁L < d₂L) (hcL : 0 < cL) (hd₁L : 0 < d₁L)
    (hcovL : CoversModCentre L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L))
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
        (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        (adelicBox L)).Z →* ℂˣ)
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L), w ∈ SL ↔ HeightOneSpectrum.under (𝓞 K) w ∈ SK)
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (Ψ : HeckeEigensystem L ℂ)
    (hfib : ∀ 𝔓₁ ∉ SL, ∀ 𝔓₂ ∉ SL,
      𝔓₁.under (𝓞 K) = 𝔓₂.under (𝓞 K) →
      (𝔓₁.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₁.asIdeal = (𝔓₂.under (𝓞 K)).asIdeal.inertiaDeg' 𝔓₂.asIdeal →
      Ψ.a 𝔓₁ = Ψ.a 𝔓₂ ∧ Ψ.b 𝔓₁ = Ψ.b 𝔓₂)
    (tysL : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ : IsUnitFactorizableAboveOfType K L tysL
      (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK φ) :
    ∀ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL,
      twistedConvOp K L D σ φ u ∈ isotypicCuspSubmodule L
          (productionPinsOf L (⋃ x ∈ TL, (· * x) '' centreCutSiegelSet L cL uL d₁L d₂L)
            (fun N => levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
            (adelicBox L)) ξL (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) SL Ψ
        ⊓ archCutSubmodule L tysL := by
  intro u hu
  rw [Submodule.mem_inf] at hu ⊢
  have hN : Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK ≠ ⊥ :=
    AutomorphicForm.LevelFiniteFactor.map_algebraMap_ne_bot
      (AutomorphicForm.LevelFiniteFactor.ne_bot_of_forall_dvd_mem hNS)
  obtain ⟨hφc, hφs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn L φ
    (Q09StabH.ConvLeg.isFactorizableTestFn_of_tier hφ)
  refine ⟨Q09StabH.twistedConvOp_mem_isotypicCuspSubmodule D σ cL uL d₁L d₂L TL (ξ := ξL) hSL hNS hfib
    (fun τ x hx => AutomorphicForm.SigmaLevelGroup.sigmaAdelicAct_mem_levelOne_inf_finiteAdelicGL2Subgroup D τ NK hx)
    hN hφc hφs (fun v hv => ?_) hu.1, ?_⟩
  · exact Q09StabH.ConvLeg.isIsotypicCuspFormAt_rightConv_of_tier cL uL d₁L d₂L TL hcL hd₁L cL uL d₁L d₂L
      (Q09StabH.transportT D σ TL) hdL
      (Q09StabH.coversModCentre_transport D σ (c := cL) (u := uL) (d₁ := d₁L) (d₂ := d₂L) (T := TL) hcovL)
      (Q09StabH.twistChar D σ (Q09StabH.window L cL uL d₁L d₂L TL) ξL)
      (Q09StabH.twistChar D σ (Q09StabH.window L cL uL d₁L d₂L (Q09StabH.transportT D σ TL)) ξL) (fun _ => rfl) hN hSL
      (fun w hw => Q09StabH.idealBound_map_eq_one_of_not_mem hSL hNS hN hw) Ψ hφ hv
  · exact Q09StabH.ConvLeg.twistedConvOp_mem_archCutSubmodule D σ hφ (Q09RowIso.rowIsometryInclAt₀_injective L)
      (AutomorphicForm.continuous_of_mem_isotypicCuspSubmodule hu.1)

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end
p2m_reactivate "P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType.Q09StabH.ConvLeg"

end S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType
end P2MW
export P2MW.S_AutomorphicForm_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_of_isUnitFactorizableAboveOfType (solution)
