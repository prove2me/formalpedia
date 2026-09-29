-- Prove2me | solution 1 for AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e924209b-ddc7-5402-b09a-5b786b63ee84

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Mathlib.Analysis.InnerProductSpace.Basic
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_measurePreserving_sigmaAdelicAct
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_NumberField_SiegelVolume
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Theorems.Thm_AutomorphicForm_exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_SiegelCovering_exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

noncomputable section

namespace WeightedVenueTrace

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Venue

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private def _root_.WeightedVenueTrace.Venue.wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

p2m_export "WeightedVenueTrace.Venue" "wt"
private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')

private theorem wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

private theorem integrable_mul_of_memLp_two {ρ : Measure (AdelicGL2 (𝓞 K) K)} (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ) (ha₂ : MemLp a 2 ρ) (hb₂ : MemLp b 2 ρ) :
    Integrable (fun x => a x * b x) ρ ∧
      ∫ x, ‖a x * b x‖ ∂ρ ≤ ((∫ x, ‖a x‖ ^ 2 ∂ρ) + ∫ x, ‖b x‖ ^ 2 ∂ρ) / 2 := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha).1 ha₂
  have hb' := (memLp_two_iff_integrable_sq_norm hb).1 hb₂
  have hpt : ∀ x, ‖a x * b x‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hint : Integrable (fun x => a x * b x) ρ :=
    Integrable.mono' ((ha'.add hb').div_const 2) (ha.mul hb)
      (Filter.Eventually.of_forall fun x => hpt x)
  refine ⟨hint, ?_⟩
  calc ∫ x, ‖a x * b x‖ ∂ρ ≤ ∫ x, (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 ∂ρ :=
        integral_mono hint.norm ((ha'.add hb').div_const 2) hpt
    _ = ((∫ x, ‖a x‖ ^ 2 ∂ρ) + ∫ x, ‖b x‖ ^ 2 ∂ρ) / 2 := by rw [integral_div, integral_add ha' hb']

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar, pow_two, ideleNorm_mul, pow_two]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

omit [NumberField K] in

private theorem exists_completion_norm_eq (w : InfinitePlace K) (s : ℝ) (hs : 0 ≤ s) :
    ∃ a : w.Completion, ‖a‖ = s := by
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨a, ?_⟩
    have h1 : (InfinitePlace.Completion.extensionEmbedding w a : ℂ) = (s : ℂ) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, ha]
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (s : ℂ)
    refine ⟨a, ?_⟩
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

private theorem exists_ideleNorm_eq (t : ℝ) (ht : 0 < t) : ∃ c : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K c = t := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance

  obtain ⟨a, ha⟩ := exists_completion_norm_eq w (t ^ ((w.mult : ℝ)⁻¹)) (Real.rpow_nonneg ht.le _)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact (Real.rpow_pos_of_pos ht _).ne ha
  refine ⟨archCentralUnit K w (Units.mk0 a ha0), ?_⟩
  unfold ideleNorm
  rw [AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K _ (archCentralUnit_snd w _),
    Finset.prod_eq_single w (fun v _ hv => by rw [archCentralUnit_fst_of_ne w _ hv, norm_one, one_pow])
      (fun h => (h (Finset.mem_univ w)).elim),
    archCentralUnit_fst_self]
  show ‖a‖ ^ w.mult = t
  rw [ha, Real.rpow_inv_natCast_pow ht.le InfinitePlace.mult_ne_zero]

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

private theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

private theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab K α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurable α β))

private theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact (wt_bounds α β σ hα x hx).2

private def ven (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((μ K).restrict Φ₀)}
  zero_mem' := ⟨continuous_zero, ⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφ, hφ₂⟩ ⟨hψc, hψ, hψ₂⟩
    exact ⟨hφc.add hψc,
      ⟨fun γ g => by simp only [Pi.add_apply, hφ.left_invariant, hψ.left_invariant],
        fun z g => by simp only [Pi.add_apply, hφ.central_transform, hψ.central_transform, mul_add]⟩,
      hφ₂.add hψ₂⟩
  smul_mem' := by
    rintro c φ ⟨hφc, hφ, hφ₂⟩
    exact ⟨hφc.const_smul c,
      ⟨fun γ g => by simp only [Pi.smul_apply, hφ.left_invariant],
        fun z g => by simp only [Pi.smul_apply, smul_eq_mul, hφ.central_transform]; ring⟩,
      hφ₂.const_smul c⟩

section Venue

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hαβ : α < β) (hΦ₀ : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)

private def Ven (_hα : 0 < α) (_hαβ : α < β) (_hΦ₀ : Φ₀ ⊆ slab K α β)
    (_hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (σ : ℝ)
    (_hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ) : Type :=
  ↥(ven ξ Φ₀)

private scoped instance : AddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (AddCommGroup ↥(ven ξ Φ₀))

private scoped instance : Module ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (Module ℂ ↥(ven ξ Φ₀))

variable {α β hα hαβ Φ₀ hΦ₀ hFD ξ σ hσ}

private def fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : AdelicGL2 (𝓞 K) K → ℂ := (φ : ↥(ven ξ Φ₀)).1

private theorem fn_add (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (φ + ψ) = fn φ + fn ψ := rfl

private theorem fn_smul (c : ℂ) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (c • φ) = c • fn φ := rfl

private theorem continuous_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : Continuous (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.1

private theorem isLsXiFunction_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : IsLsXiFunction (𝓞 K) K ⊤ ξ (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.2.1

private theorem memLp_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : MemLp (fn φ) 2 ((μ K).restrict Φ₀) :=
  (φ : ↥(ven ξ Φ₀)).2.2.2

private theorem fn_injective : Function.Injective (fn : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ → _) :=
  fun _ _ h => Subtype.ext h

private def pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ℂ :=
  ∫ x in Φ₀, fn ψ x * conj (fn φ x) * wt K σ x ∂(μ K)

private theorem integrable_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Integrable (fun x => fn ψ x * conj (fn φ x) * wt K σ x) ((μ K).restrict Φ₀) := by
  have hψm : AEStronglyMeasurable (fn ψ) ((μ K).restrict Φ₀) := (continuous_fn ψ).aestronglyMeasurable
  have hφm : AEStronglyMeasurable (fun x => conj (fn φ x)) ((μ K).restrict Φ₀) :=
    (Complex.continuous_conj.comp (continuous_fn φ)).aestronglyMeasurable
  have hφ₂ : MemLp (fun x => conj (fn φ x)) 2 ((μ K).restrict Φ₀) :=
    ⟨hφm, by
      rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun x => RCLike.norm_conj (fn φ x))]
      exact (memLp_fn φ).2⟩
  have hprod := (integrable_mul_of_memLp_two (fn ψ) (fun x => conj (fn φ x)) hψm hφm (memLp_fn ψ) hφ₂).1
  simpa only [mul_comm] using
    hprod.bdd_mul (wt_continuous σ).aestronglyMeasurable (wt_ae_bound α β σ hα Φ₀ hΦ₀)

private theorem pair_add_left (φ φ' ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (φ + φ') ψ = pair φ ψ + pair φ' ψ := by
  simp only [pair, fn_add, Pi.add_apply, map_add, mul_add, add_mul]
  exact integral_add (integrable_pair φ ψ) (integrable_pair φ' ψ)

private theorem pair_smul_left (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (c • φ) ψ = conj c * pair φ ψ := by
  simp only [pair, fn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

private theorem conj_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : conj (pair ψ φ) = pair φ ψ := by
  simp only [pair, ← integral_conj, map_mul, Complex.conj_conj, wt, Complex.conj_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

private theorem pair_self_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair φ φ = ((∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) : ℝ) : ℂ) := by
  rw [pair, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [wt, Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]

private theorem re_pair_self_nonneg (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : 0 ≤ RCLike.re (pair φ φ) := by
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (wt_pos σ x).le

private theorem forall_eq_zero_of_measure_inter_eq_zero (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (U : Set (AdelicGL2 (𝓞 K) K)) (hU : IsOpen U) (h : (μ K) ({x | f x ≠ 0} ∩ U) = 0) :
    ∀ x ∈ U, f x = 0 := by
  have hopen : IsOpen ({x | f x ≠ 0} ∩ U) := (isOpen_ne_fun hf continuous_const).inter hU
  have hempty := (hopen.measure_eq_zero_iff (μ := μ K)).1 h
  intro x hx
  by_contra hne
  have hmem : x ∈ {x | f x ≠ 0} ∩ U := ⟨hne, hx⟩
  rw [hempty] at hmem
  exact hmem

private theorem eq_zero_of_pair_self_eq_zero (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (h : pair φ φ = 0) :
    φ = 0 := by

  have h0 : ∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) = 0 := by
    have h' := pair_self_eq φ
    rw [h] at h'
    exact_mod_cast h'.symm
  have hint : Integrable (fun x => ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((μ K).restrict Φ₀) := by
    have h2 := (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
    have hb : ∀ᵐ x ∂((μ K).restrict Φ₀),
        ‖ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
      (wt_ae_bound α β σ hα Φ₀ hΦ₀).mono fun x hx => by simpa only [wt, Complex.norm_real] using hx
    simpa only [mul_comm] using h2.bdd_mul
      ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').aestronglyMeasurable hb

  have hae : ∀ᵐ x ∂((μ K).restrict Φ₀), fn φ x = 0 := by
    have hz := (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (wt_pos σ x).le) hint).1 h0
    filter_upwards [hz] with x hx
    have hx' : ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) = 0 := hx
    rcases mul_eq_zero.1 hx' with h1 | h1
    · exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h1)
    · exact absurd h1 (wt_pos σ x).ne'

  obtain ⟨A, hA⟩ : ∃ A : Set (AdelicGL2 (𝓞 K) K), A = {x | fn φ x ≠ 0} := ⟨_, rfl⟩
  have hAopen : IsOpen A := by
    rw [hA]
    exact isOpen_ne_fun (continuous_fn φ) continuous_const
  have hAmeas : MeasurableSet A := hAopen.measurableSet
  have hAΓ : ∀ γ : Γ K, γ • A = A := fun γ => by
    ext x
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Set.mem_smul_set_iff_inv_smul_mem, hA, Set.mem_setOf_eq, Set.mem_setOf_eq, Γ_smul]
    have hinv : ((γ⁻¹ : Γ K) : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀⁻¹ := by
      rw [Subgroup.coe_inv, hγ₀, map_inv]
    rw [hinv, (isLsXiFunction_fn φ).left_invariant]
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) :=
    smulInvariant_restrict _ (slab_Γ_stable α β)
  haveI : Countable (Γ K) := countable_Γ
  have hAslab : (μ K).restrict (slab K α β) A = 0 := by
    refine hFD.measure_zero_of_invariant A hAΓ ?_
    have hμ : (μ K) (A ∩ Φ₀) = 0 := by
      rw [← Measure.restrict_apply hAmeas, hA]
      exact hae
    exact nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 Measure.restrict_le_self _).trans hμ.le)

  obtain ⟨U, hU⟩ : ∃ U : Set (AdelicGL2 (𝓞 K) K),
      U = {x | ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Ioo α β} := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_Ioo.preimage (continuous_ideleNorm_det K)
  have hUslab : U ⊆ slab K α β := by
    rw [hU]
    exact fun x hx => Set.Ioo_subset_Icc_self hx
  have hAU : (μ K) (A ∩ U) = 0 := by
    have hAs : (μ K) (A ∩ slab K α β) = 0 := by rwa [Measure.restrict_apply hAmeas] at hAslab
    exact measure_mono_null (Set.inter_subset_inter_right _ hUslab) hAs
  have hzeroU : ∀ x ∈ U, fn φ x = 0 := by
    refine forall_eq_zero_of_measure_inter_eq_zero (fn φ) (continuous_fn φ) U hUopen ?_
    rw [← hA]
    exact hAU

  have hall : ∀ g, fn φ g = 0 := by
    intro g
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (α + β) / 2 := ⟨_, rfl⟩
    have htα : α < t := by rw [ht]; linarith
    have htβ : t < β := by rw [ht]; linarith
    have ht0 : 0 < t := hα.trans htα
    have hdg : 0 < ideleNorm K (Matrix.GeneralLinearGroup.det g) := ideleNorm_pos _
    obtain ⟨c, hc⟩ := exists_ideleNorm_eq (K := K)
      (Real.sqrt (t / ideleNorm K (Matrix.GeneralLinearGroup.det g))) (Real.sqrt_pos.2 (div_pos ht0 hdg))
    have hmemU : centralScalar (𝓞 K) K c * g ∈ U := by
      rw [hU, Set.mem_setOf_eq, normDet_central, hc, Real.sq_sqrt (div_pos ht0 hdg).le,
        div_mul_cancel₀ _ hdg.ne']
      exact ⟨htα, htβ⟩
    have h1 := hzeroU _ hmemU
    have h2 := (isLsXiFunction_fn φ).central_transform ⟨c, Subgroup.mem_top c⟩ g
    change fn φ (centralScalar (𝓞 K) K c * g) = _ at h2
    rw [h1] at h2
    exact (mul_eq_zero.1 h2.symm).resolve_left (Units.ne_zero _)
  exact fn_injective (funext hall)

@[reducible] private def venCore : InnerProductSpace.Core ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) where
  inner := pair
  conj_inner_symm φ ψ := conj_pair φ ψ
  re_inner_nonneg φ := re_pair_self_nonneg φ
  add_left φ φ' ψ := pair_add_left φ φ' ψ
  smul_left φ ψ c := pair_smul_left c φ ψ
  definite φ h := eq_zero_of_pair_self_eq_zero φ h

private scoped instance : NormedAddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ venCore

private scoped instance : InnerProductSpace ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  InnerProductSpace.ofCore _

private theorem inner_eq_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    @inner ℂ _ _ φ ψ = ∫ x in Φ₀, fn ψ x * conj (fn φ x) * wt K σ x ∂(μ K) := rfl

private theorem norm_sq_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    ‖φ‖ ^ 2 = ∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  rw [@norm_sq_eq_re_inner ℂ]
  change RCLike.re (pair φ φ) = _
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]

end Venue

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.coe_injective (K := K)).countable

private scoped instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine (Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_)
  intro I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  exact ⟨s, hs⟩

private scoped instance countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Function.Injective.countable (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h

open scoped RestrictedProduct in
private scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

private scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

section Convolution

private theorem continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) := by
  have hconv : rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂(μ K) := funext fun x => rightConv_apply K u g x
  rw [hconv, continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.mul (hgc : IsCompact (tsupport g))).exists_bound_of_continuousOn huc.continuousOn
  refine continuousAt_of_dominated (bound := fun y => M * ‖g y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((huc.comp (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable
  · refine Filter.eventually_of_mem hN fun x hx => Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport g
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mul_mem_mul hx hy)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul M
  · exact Filter.Eventually.of_forall fun y =>
      ((huc.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousAt

private theorem isLsXiFunction_rightConv (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u g : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K u g) where
  left_invariant γ x := by simp only [rightConv, mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [rightConv, mul_assoc, hu.central_transform, integral_const_mul]

private theorem rightConv_add_left (u v g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hvc : Continuous v)
    (hg : Continuous g) (hgc : HasCompactSupport g) : rightConv K (u + v) g = rightConv K u g + rightConv K v g := by
  funext x
  simp only [rightConv, Pi.add_apply, add_mul]
  exact integral_add
    (((huc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)
    (((hvc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)

private theorem rightConv_smul_left (c : ℂ) (u g : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • u) g = c • rightConv K u g := by
  funext x
  simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem flat_continuous (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) :
    Continuous (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) :=
  (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul (wt_continuous σ)

private theorem flat_hasCompactSupport (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) := by
  have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => g y⁻¹) :=
    hgc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  have h2 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹)) :=
    h1.comp_left (map_zero (starRingEnd ℂ))
  exact h2.mul_right

end Convolution

section Operators

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

private def convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ where
  toFun φ := show ↥(ven ξ Φ₀) from
    ⟨rightConv K (fn φ) g,
      continuous_rightConv_of_hasCompactSupport (fn φ) g (continuous_fn φ) hg hgc,
      isLsXiFunction_rightConv ξ (fn φ) g (isLsXiFunction_fn φ),
      (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn φ) (fn φ)
        (isLsXiFunction_fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (continuous_fn φ) (memLp_fn φ) (memLp_fn φ)
        g hg hgc).1⟩
  map_add' φ ψ := fn_injective (by
    change rightConv K (fn φ + fn ψ) g = rightConv K (fn φ) g + rightConv K (fn ψ) g
    exact rightConv_add_left (fn φ) (fn ψ) g (continuous_fn φ) (continuous_fn ψ) hg hgc)
  map_smul' c φ := fn_injective (by
    change rightConv K (c • fn φ) g = c • rightConv K (fn φ) g
    exact rightConv_smul_left c (fn φ) g)

private theorem fn_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (convOp g hg hgc φ) = rightConv K (fn φ) g := rfl

private def evalConv (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (d : AdelicGL2 (𝓞 K) K) : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] ℂ :=
  (LinearMap.proj d ∘ₗ (ven ξ Φ₀).subtype) ∘ₗ convOp g hg hgc

private theorem evalConv_apply (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (d : AdelicGL2 (𝓞 K) K) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    evalConv g hg hgc d φ = rightConv K (fn φ) g d := rfl

private def convOpFlat (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ :=
  convOp (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))
    (flat_continuous σ g hg) (flat_hasCompactSupport σ g hgc)

private theorem inner_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (w v : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    @inner ℂ _ _ (convOp g hg hgc w) v = @inner ℂ _ _ w (convOpFlat g hg hgc v) := by
  have h : pair v (convOp g hg hgc w) = pair (convOpFlat g hg hgc v) w :=
    (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn w) (fn v)
      (isLsXiFunction_fn w) (isLsXiFunction_fn v) (continuous_fn w) (continuous_fn v) (memLp_fn w) (memLp_fn v)
      g hg hgc).2.2
  change pair (convOp g hg hgc w) v = pair w (convOpFlat g hg hgc v)
  rw [← conj_pair, h, conj_pair]

end Operators

section Eigen

private theorem inner_eq_zero_of_eigen {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (φ ψ : E)
    (s l l' : ℂ) (hψψ : @inner ℂ _ _ ψ (l' • ψ) = s * @inner ℂ _ _ (l' • ψ) ψ)
    (hψφ : @inner ℂ _ _ ψ (l • φ) = s * @inner ℂ _ _ (l' • ψ) φ) (hne : l ≠ l') : @inner ℂ _ _ ψ φ = 0 := by
  by_cases hψ : ψ = 0
  · simp [hψ]
  have hself : (@inner ℂ _ _ ψ ψ : ℂ) ≠ 0 := inner_self_ne_zero.2 hψ
  rw [inner_smul_right, inner_smul_left] at hψψ hψφ
  have hl' : l' = s * conj l' := by
    have h0 : (l' - s * conj l') * @inner ℂ _ _ ψ ψ = 0 := by rw [sub_mul, hψψ, mul_assoc, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hself)
  have h1 : (l - l') * @inner ℂ _ _ ψ φ = 0 := by
    rw [sub_mul, hψφ, ← mul_assoc, ← hl', sub_self]
  exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hne)

end Eigen

section Cosets

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

private theorem translate_mem_ven (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (y : AdelicGL2 (𝓞 K) K) :
    (fun x => fn φ (x * y)) ∈ ven ξ Φ₀ :=
  ⟨(continuous_fn φ).comp (continuous_id.mul continuous_const),
    ⟨fun γ x => by simp only [mul_assoc, (isLsXiFunction_fn φ).left_invariant],
      fun z x => by simp only [mul_assoc, (isLsXiFunction_fn φ).central_transform]⟩,
    (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn φ) (fn φ)
      (isLsXiFunction_fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (continuous_fn φ) (memLp_fn φ) (memLp_fn φ)
      y).1⟩

private theorem cosetSum_mem_ven (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) :
    (fun x => ∑ i, fn φ (x * reps i)) ∈ ven ξ Φ₀ := by
  have h : (fun x => ∑ i, fn φ (x * reps i)) = ∑ i, fun x => fn φ (x * reps i) := by
    funext x
    simp only [Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun i _ => translate_mem_ven φ (reps i)

private def cosetOp {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ :=
  show ↥(ven ξ Φ₀) from ⟨fun x => ∑ i, fn φ (x * reps i), cosetSum_mem_ven φ reps⟩

private theorem fn_cosetOp {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    fn (cosetOp reps φ) = fun x => ∑ i, fn φ (x * reps i) := rfl

private theorem inner_cosetOp (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn φ (g * u) = fn φ g)
    (hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn ψ (g * u) = fn ψ g)
    (gv : AdelicGL2 (𝓞 K) K) {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u')
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U, gv⁻¹ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u')) :
    @inner ℂ _ _ ψ (cosetOp reps φ) =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
        @inner ℂ _ _ (cosetOp reps ψ) φ :=
  (cosetSum_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU (fn φ) (fn ψ)
    (isLsXiFunction_fn φ) (isLsXiFunction_fn ψ) (continuous_fn φ) (continuous_fn ψ) (memLp_fn φ) (memLp_fn ψ) hφU hψU
    gv n reps hreps c hc).2.2

private theorem inner_eq_zero_of_cosetOp_eigen (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn φ (g * u) = fn φ g)
    (hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn ψ (g * u) = fn ψ g)
    (gv : AdelicGL2 (𝓞 K) K) {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 K) K)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u')
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U, gv⁻¹ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u'))
    (l l' : ℂ) (hφl : cosetOp reps φ = l • φ) (hψl : cosetOp reps ψ = l' • ψ) (hne : l ≠ l') :
    @inner ℂ _ _ ψ φ = 0 := by
  refine inner_eq_zero_of_eigen φ ψ
    (((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ)) l l' ?_ ?_ hne
  · rw [← hψl]
    exact inner_cosetOp U hU ψ ψ hψU hψU gv reps hreps c hc
  · rw [← hφl, ← hψl]
    exact inner_cosetOp U hU φ ψ hφU hψU gv reps hreps c hc

end Cosets

section HeckeBridge

open HeckeIntegralSeam

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

private theorem cosetSum_eq_of_isHeckeCosetSystem {U : Subgroup (AdelicGL2 (𝓞 K) K)} {gv : AdelicGL2 (𝓞 K) K}
    {ι₀ ι₁ : Type} [Fintype ι₀] [Fintype ι₁] {reps₀ : ι₀ → AdelicGL2 (𝓞 K) K} {reps₁ : ι₁ → AdelicGL2 (𝓞 K) K}
    (h₀ : IsHeckeCosetSystem U gv reps₀) (h₁ : IsHeckeCosetSystem U gv reps₁) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (g : AdelicGL2 (𝓞 K) K) :
    ∑ i, φ (g * reps₀ i) = ∑ j, φ (g * reps₁ j) := by

  have hcov : ∀ i, ∃ j, (QuotientGroup.mk (reps₀ i) : AdelicGL2 (𝓞 K) K ⧸ U) = QuotientGroup.mk (reps₁ j) :=
    fun i => h₁.covers (reps₀ i) (h₀.mem_doubleCoset i)
  choose f hf using hcov
  have hinj : Function.Injective f := by
    intro i i' hii'
    apply h₀.mk_injective
    simp only
    rw [hf i, hf i', hii']
  have hsurj : Function.Surjective f := by
    intro j
    obtain ⟨i, hi⟩ := h₀.covers (reps₁ j) (h₁.mem_doubleCoset j)
    refine ⟨i, h₁.mk_injective ?_⟩
    simp only
    rw [← hf i, hi]
  refine Fintype.sum_bijective f ⟨hinj, hsurj⟩ _ _ fun i => ?_

  have hu : (reps₀ i)⁻¹ * reps₁ (f i) ∈ U := QuotientGroup.eq.1 (hf i)
  have e : reps₁ (f i) = reps₀ i * ((reps₀ i)⁻¹ * reps₁ (f i)) := by group
  rw [e, ← mul_assoc, hφU _ _ hu]

private theorem inner_eq_zero_of_isHeckeCosetEigenfunctionAt (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1) (gv : AdelicGL2 (𝓞 K) K)
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U, gv⁻¹ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u'))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn φ (g * u) = fn φ g)
    (hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn ψ (g * u) = fn ψ g) (a a' : ℂ)
    (hφ : SmoothCusp.IsHeckeCosetEigenfunctionAt K U gv v (fn φ) a)
    (hψ : SmoothCusp.IsHeckeCosetEigenfunctionAt K U gv v (fn ψ) a') (hne : a ≠ a') : @inner ℂ _ _ ψ φ = 0 := by
  obtain ⟨reps, hsys, hφeig⟩ := hφ
  obtain ⟨reps', hsys', hψeig⟩ := hψ
  have hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u' := fun i => by
    obtain ⟨u, hu, u', hu', e⟩ := HeckePair.mem_doubleCoset_iff.1 (hsys.mem_doubleCoset i)
    exact ⟨u, hu, u', hu', e.symm⟩
  refine inner_eq_zero_of_cosetOp_eigen U hU φ ψ hφU hψU gv reps hreps c hc a a' ?_ ?_ hne
  · exact fn_injective (funext fun g => hφeig g)
  · refine fn_injective (funext fun g => ?_)
    change ∑ i, fn ψ (g * reps i) = a' * fn ψ g
    rw [cosetSum_eq_of_isHeckeCosetSystem hsys hsys' (fn ψ) hψU g]
    exact hψeig g

private theorem normDet_pow_eq_one_of_invariant (U : Subgroup (AdelicGL2 (𝓞 K) K))
    (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (hφ0 : φ ≠ 0)
    (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, fn φ (g * u) = fn φ g) (u : AdelicGL2 (𝓞 K) K) (hu : u ∈ U) :
    ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1 := by
  have h := (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn φ) (fn φ)
    (isLsXiFunction_fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (continuous_fn φ) (memLp_fn φ) (memLp_fn φ)
    u).2.2
  have e₁ : ∀ x, fn φ (x * u) = fn φ x := fun x => hφU x u hu
  have e₂ : ∀ x, fn φ (x * u⁻¹) = fn φ x := fun x => hφU x u⁻¹ (U.inv_mem hu)
  simp only [e₁, e₂] at h
  have hself : @inner ℂ _ _ φ φ =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ : ℝ) : ℂ) * @inner ℂ _ _ φ φ := h
  have hne : (@inner ℂ _ _ φ φ : ℂ) ≠ 0 := inner_self_ne_zero.2 hφ0
  have h3 : (((ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ : ℝ) : ℂ) - 1) * @inner ℂ _ _ φ φ = 0 := by
    rw [sub_mul, one_mul, ← hself, sub_self]
  have h4 : ((ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ : ℝ) : ℂ) = 1 :=
    sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  exact_mod_cast h4

end HeckeBridge

section Twist

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

variable (F : Type) [Field F] [Algebra F K] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) F K) (τ : K ≃ₐ[F] K)

private def actUnits : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map ((D.act τ : RingAut (AdeleRing (𝓞 K) K)).toRingHom : AdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)

private theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 K) K)ˣ) :
    sigmaAdelicAct F K D τ (centralScalar (𝓞 K) K z) = centralScalar (𝓞 K) K (actUnits F D τ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  by_cases hij : i = j <;>
    simp [sigmaAdelicAct, centralScalar, actUnits, Matrix.GeneralLinearGroup.map, hij]

private theorem sigmaAdelicAct_globalPoints' (γ : Matrix.GeneralLinearGroup (Fin 2) K) :
    sigmaAdelicAct F K D τ (globalPoints (𝓞 K) K γ) =
      globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.map (τ : K →+* K) γ) :=
  sigmaAdelicAct_globalPoints F K D τ γ

private theorem sigmaAdelicAct_symm_apply (x : AdelicGL2 (𝓞 K) K) :
    sigmaAdelicAct F K D τ⁻¹ (sigmaAdelicAct F K D τ x) = x := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, inv_mul_cancel, sigmaAdelicAct_one, MonoidHom.id_apply]

private theorem sigmaAdelicAct_apply_symm (x : AdelicGL2 (𝓞 K) K) :
    sigmaAdelicAct F K D τ (sigmaAdelicAct F K D τ⁻¹ x) = x := by
  rw [← MonoidHom.comp_apply, ← sigmaAdelicAct_mul, mul_inv_cancel, sigmaAdelicAct_one, MonoidHom.id_apply]

private def actEquiv : AdelicGL2 (𝓞 K) K ≃ AdelicGL2 (𝓞 K) K where
  toFun := sigmaAdelicAct F K D τ
  invFun := sigmaAdelicAct F K D τ⁻¹
  left_inv := sigmaAdelicAct_symm_apply F D τ
  right_inv := sigmaAdelicAct_apply_symm F D τ

private theorem actEquiv_apply (x : AdelicGL2 (𝓞 K) K) : actEquiv F D τ x = sigmaAdelicAct F K D τ x := rfl

private theorem actEquiv_symm_apply (x : AdelicGL2 (𝓞 K) K) :
    (actEquiv F D τ).symm x = sigmaAdelicAct F K D τ⁻¹ x := rfl

private theorem measurable_sigmaAdelicAct : Measurable (sigmaAdelicAct F K D τ) :=
  (continuous_sigmaAdelicAct F K D τ).measurable

private theorem measurableEmbedding_sigmaAdelicAct : MeasurableEmbedding (sigmaAdelicAct F K D τ) :=
  (MeasurableEquiv.mk (actEquiv F D τ) (measurable_sigmaAdelicAct F D τ)
    (measurable_sigmaAdelicAct F D τ⁻¹)).measurableEmbedding

private theorem sigmaAdelicAct_mem_slab_iff (x : AdelicGL2 (𝓞 K) K) :
    sigmaAdelicAct F K D τ x ∈ slab K α β ↔ x ∈ slab K α β := by
  simp only [slab, Set.mem_setOf_eq, ideleNorm_det_sigmaAdelicAct F K D τ]

private theorem preimage_slab : sigmaAdelicAct F K D τ ⁻¹' slab K α β = slab K α β :=
  Set.ext fun x => sigmaAdelicAct_mem_slab_iff F D τ x

private theorem measurePreserving_restrict_slab :
    MeasurePreserving (sigmaAdelicAct F K D τ) ((μ K).restrict (slab K α β)) ((μ K).restrict (slab K α β)) := by
  have h := (measurePreserving_sigmaAdelicAct F K D τ).restrict_preimage (slab_measurable α β)
  rwa [preimage_slab] at h

private def ΓMap (γ : Γ K) : Γ K :=
  ⟨sigmaAdelicAct F K D τ γ, by
    obtain ⟨γ₀, hγ₀⟩ := γ.2
    refine ⟨Matrix.GeneralLinearGroup.map (τ : K →+* K) γ₀, ?_⟩
    rw [← sigmaAdelicAct_globalPoints' F D τ]
    exact congrArg _ hγ₀⟩

private theorem coe_ΓMap (γ : Γ K) : (ΓMap F D τ γ : AdelicGL2 (𝓞 K) K) = sigmaAdelicAct F K D τ γ := rfl

private def ΓEquiv : Γ K ≃ Γ K where
  toFun := ΓMap F D τ
  invFun := ΓMap F D τ⁻¹
  left_inv γ := Subtype.ext (by simp only [coe_ΓMap, sigmaAdelicAct_symm_apply])
  right_inv γ := Subtype.ext (by simp only [coe_ΓMap, sigmaAdelicAct_apply_symm])

private theorem isFundamentalDomain_image (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) :
    IsFundamentalDomain (Γ K) (sigmaAdelicAct F K D τ '' Φ₀) ((μ K).restrict (slab K α β)) := by
  have h := hFD.image_of_equiv (actEquiv F D τ) (measurePreserving_restrict_slab F D τ⁻¹).quasiMeasurePreserving
    (ΓEquiv F D τ⁻¹) ?_
  · exact h
  · intro γ x
    simp only [actEquiv_apply, Γ_smul, ΓEquiv, Equiv.coe_fn_mk, coe_ΓMap, map_mul, sigmaAdelicAct_apply_symm]

private theorem normSq_wt_Γ_invariant (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u)
    (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    ‖u (γ • x)‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det (γ • x)) ^ (-σ) =
      ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  rw [Γ_smul, ← hγ₀, hu.left_invariant, normDet_global]

private theorem integral_normSq_comp (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∫ x in Φ₀, ‖u (sigmaAdelicAct F K D τ x)‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) =
      ∫ x in Φ₀, ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  have himage : sigmaAdelicAct F K D τ '' Φ₀ ⊆ slab K α β := by
    rintro _ ⟨x, hx, rfl⟩
    exact (sigmaAdelicAct_mem_slab_iff F D τ x).2 (hΦ₀ hx)
  haveI : Countable (Γ K) := countable_Γ
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) :=
    smulInvariant_restrict _ (slab_Γ_stable α β)
  calc ∫ x in Φ₀, ‖u (sigmaAdelicAct F K D τ x)‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K)
      = ∫ x in Φ₀, ‖u (sigmaAdelicAct F K D τ x)‖ ^ 2 *
          ideleNorm K (Matrix.GeneralLinearGroup.det (sigmaAdelicAct F K D τ x)) ^ (-σ) ∂(μ K) := by
        simp only [ideleNorm_det_sigmaAdelicAct F K D τ]
    _ = ∫ y in sigmaAdelicAct F K D τ '' Φ₀, ‖u y‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) ∂(μ K) :=
        ((measurePreserving_sigmaAdelicAct F K D τ).setIntegral_image_emb (measurableEmbedding_sigmaAdelicAct F D τ)
          (fun y => ‖u y‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ)) Φ₀).symm
    _ = ∫ y in sigmaAdelicAct F K D τ '' Φ₀, ‖u y‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ)
          ∂((μ K).restrict (slab K α β)) := by rw [Measure.restrict_restrict_of_subset himage]
    _ = ∫ x in Φ₀, ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂((μ K).restrict (slab K α β)) :=
        (isFundamentalDomain_image F D τ hFD).setIntegral_eq hFD (normSq_wt_Γ_invariant u hu)
    _ = ∫ x in Φ₀, ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
        rw [Measure.restrict_restrict_of_subset hΦ₀]

private theorem isLsXiFunction_comp (hξ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ξ ⟨actUnits F D τ z, Subgroup.mem_top _⟩ = ξ z)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (u ∘ sigmaAdelicAct F K D τ) where
  left_invariant γ g := by
    simp only [Function.comp_apply, map_mul, sigmaAdelicAct_globalPoints', hu.left_invariant]
  central_transform z g := by
    simp only [Function.comp_apply, map_mul, sigmaAdelicAct_centralScalar]
    rw [hu.central_transform ⟨actUnits F D τ z, Subgroup.mem_top _⟩, hξ z]

private theorem enormSq_Γ_invariant (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (γ : Γ K)
    (x : AdelicGL2 (𝓞 K) K) : ‖u (γ • x)‖ₑ ^ (2 : ℝ) = ‖u x‖ₑ ^ (2 : ℝ) := by
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  rw [Γ_smul, ← hγ₀, hu.left_invariant]

private theorem sigmaAdelicAct_injective : Function.Injective (sigmaAdelicAct F K D τ) :=
  (actEquiv F D τ).injective

private theorem memLp_comp (u : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    MemLp (fn u ∘ sigmaAdelicAct F K D τ) 2 ((μ K).restrict Φ₀) := by
  have himage : sigmaAdelicAct F K D τ '' Φ₀ ⊆ slab K α β := by
    rintro _ ⟨x, hx, rfl⟩
    exact (sigmaAdelicAct_mem_slab_iff F D τ x).2 (hΦ₀ hx)
  have hfin : ∫⁻ x in Φ₀, ‖fn u x‖ₑ ^ (2 : ℝ) ∂(μ K) < ⊤ := by
    have h := (memLp_fn u).2
    rwa [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
  haveI : Countable (Γ K) := countable_Γ
  haveI : SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) :=
    smulInvariant_restrict _ (slab_Γ_stable α β)
  refine ⟨((continuous_fn u).comp (continuous_sigmaAdelicAct F K D τ)).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Function.comp_apply]
  calc ∫⁻ x in Φ₀, ‖fn u (sigmaAdelicAct F K D τ x)‖ₑ ^ (2 : ℝ) ∂(μ K)
      = ∫⁻ x in sigmaAdelicAct F K D τ ⁻¹' (sigmaAdelicAct F K D τ '' Φ₀),
          ‖fn u (sigmaAdelicAct F K D τ x)‖ₑ ^ (2 : ℝ) ∂(μ K) := by
        rw [Set.preimage_image_eq Φ₀ (sigmaAdelicAct_injective F D τ)]
    _ = ∫⁻ y in sigmaAdelicAct F K D τ '' Φ₀, ‖fn u y‖ₑ ^ (2 : ℝ) ∂(μ K) :=
        (measurePreserving_sigmaAdelicAct F K D τ).setLIntegral_comp_preimage_emb
          (measurableEmbedding_sigmaAdelicAct F D τ) (fun y => ‖fn u y‖ₑ ^ (2 : ℝ)) _
    _ = ∫⁻ y in sigmaAdelicAct F K D τ '' Φ₀, ‖fn u y‖ₑ ^ (2 : ℝ) ∂((μ K).restrict (slab K α β)) := by
        rw [Measure.restrict_restrict_of_subset himage]
    _ = ∫⁻ x in Φ₀, ‖fn u x‖ₑ ^ (2 : ℝ) ∂((μ K).restrict (slab K α β)) :=
        (isFundamentalDomain_image F D τ hFD).setLIntegral_eq hFD _ (enormSq_Γ_invariant (fn u) (isLsXiFunction_fn u))
    _ = ∫⁻ x in Φ₀, ‖fn u x‖ₑ ^ (2 : ℝ) ∂(μ K) := by rw [Measure.restrict_restrict_of_subset hΦ₀]
    _ < ⊤ := hfin

variable (hξ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ξ ⟨actUnits F D τ z, Subgroup.mem_top _⟩ = ξ z)

private def tw : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ where
  toFun u := show ↥(ven ξ Φ₀) from
    ⟨fn u ∘ sigmaAdelicAct F K D τ, (continuous_fn u).comp (continuous_sigmaAdelicAct F K D τ),
      isLsXiFunction_comp F D τ hξ (fn u) (isLsXiFunction_fn u), memLp_comp F D τ u⟩
  map_add' _ _ := fn_injective rfl
  map_smul' _ _ := fn_injective rfl

private theorem tw_apply (u : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    fn (tw F D τ hξ u) = sigmaSectionActOn F K D τ (fn u) := rfl

private theorem norm_tw (u : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ‖tw F D τ hξ u‖ = ‖u‖ := by
  have h : ‖tw F D τ hξ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq, norm_sq_eq]
    exact integral_normSq_comp F D τ (fn u) (isLsXiFunction_fn u) hFD hΦ₀
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

end Twist

end Venue
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ConvolutionAssociativity

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

private abbrev _root_.WeightedVenueTrace.ConvolutionAssociativity.μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

p2m_export "WeightedVenueTrace.ConvolutionAssociativity" "μ"
variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.coe_injective (K := K)).countable

private scoped instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine (Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_)
  intro I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  exact ⟨s, hs⟩

private scoped instance countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Function.Injective.countable (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h

open scoped RestrictedProduct in
private scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

private scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → AdeleRing (𝓞 K) K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

variable (K) in

private theorem kernel_integrable (u g h : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hh : Continuous h) (hhc : HasCompactSupport h) (x : AdelicGL2 (𝓞 K) K) :
    Integrable (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)))
      ((μ K).prod (μ K)) := by
  have hcont : Continuous fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)) :=
    (huc.comp (continuous_const.mul continuous_fst)).mul
      ((hg.comp continuous_snd).mul (hh.comp (continuous_snd.inv.mul continuous_fst)))
  have hsupp : HasCompactSupport
      fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => u (x * p.1) * (g p.2 * h (p.2⁻¹ * p.1)) := by
    refine HasCompactSupport.intro (((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))).prod hgc)
      fun p hp => ?_
    by_contra hne
    apply hp
    have hg' : g p.2 ≠ 0 := fun h0 => hne (by simp [h0])
    have hh' : h (p.2⁻¹ * p.1) ≠ 0 := fun h0 => hne (by simp [h0])
    refine Set.mk_mem_prod ?_ (subset_tsupport g hg')
    have : p.1 = p.2 * (p.2⁻¹ * p.1) := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hg') (subset_tsupport h hh')
  exact hcont.integrable_of_hasCompactSupport hsupp

private theorem rightConv_rightConv_inv (u g h : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hh : Continuous h) (hhc : HasCompactSupport h) :
    rightConv K u (rightConv K g fun y => h y⁻¹) = rightConv K (rightConv K u h) g := by
  funext x

  have e₁ : ∀ z : AdelicGL2 (𝓞 K) K, rightConv K g (fun y => h y⁻¹) z = ∫ y, g y * h (y⁻¹ * z) ∂(μ K) := by
    intro z
    rw [rightConv_apply]
    have hl := integral_mul_left_eq_self (μ := μ K) (fun y => g y * h (y⁻¹ * z)) z
    simp only [mul_inv_rev, inv_mul_cancel_right] at hl
    exact hl

  have e₂ : ∀ y : AdelicGL2 (𝓞 K) K, ∫ z, u (x * z) * h (y⁻¹ * z) ∂(μ K) = rightConv K u h (x * y) := by
    intro y
    rw [rightConv_apply, ← integral_mul_left_eq_self (μ := μ K) (fun z => u (x * z) * h (y⁻¹ * z)) y]
    simp only [inv_mul_cancel_left, mul_assoc]
  have hint := kernel_integrable K u g h huc hg hgc hh hhc x
  calc rightConv K u (rightConv K g fun y => h y⁻¹) x
      = ∫ z, u (x * z) * ∫ y, g y * h (y⁻¹ * z) ∂(μ K) ∂(μ K) := by
        rw [rightConv_apply]
        simp only [e₁]
    _ = ∫ z, ∫ y, u (x * z) * (g y * h (y⁻¹ * z)) ∂(μ K) ∂(μ K) := by
        simp only [integral_const_mul]
    _ = ∫ y, ∫ z, u (x * z) * (g y * h (y⁻¹ * z)) ∂(μ K) ∂(μ K) := integral_integral_swap hint
    _ = ∫ y, g y * ∫ z, u (x * z) * h (y⁻¹ * z) ∂(μ K) ∂(μ K) := by
        congr 1
        funext y
        rw [← integral_const_mul]
        congr 1
        funext z
        ring
    _ = ∫ y, rightConv K u h (x * y) * g y ∂(μ K) := by
        simp only [e₂, mul_comm]
    _ = rightConv K (rightConv K u h) g x := (rightConv_apply K _ _ x).symm

private theorem continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) := by
  have hconv : rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂(μ K) := funext fun x => rightConv_apply K u g x
  rw [hconv, continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.mul (hgc : IsCompact (tsupport g))).exists_bound_of_continuousOn huc.continuousOn
  refine continuousAt_of_dominated (bound := fun y => M * ‖g y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((huc.comp (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable
  · refine Filter.eventually_of_mem hN fun x hx => Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport g
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mul_mem_mul hx hy)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul M
  · exact Filter.Eventually.of_forall fun y =>
      ((huc.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousAt

private theorem hasCompactSupport_rightConv_inv (g h : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) : HasCompactSupport (rightConv K g fun y => h y⁻¹) := by
  refine HasCompactSupport.intro ((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))) fun x hx => ?_
  rw [rightConv_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : h y⁻¹ = 0
  · simp [hy]
  have hgx : g (x * y) = 0 := by
    by_contra hgx
    apply hx
    have : x = x * y * y⁻¹ := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hgx) (subset_tsupport h hy)
  simp [hgx]

private theorem rightConv_add_right (u f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hf₁ : Continuous f₁)
    (hf₁c : HasCompactSupport f₁) (hf₂ : Continuous f₂) (hf₂c : HasCompactSupport f₂) :
    rightConv K u (f₁ + f₂) = rightConv K u f₁ + rightConv K u f₂ := by
  funext x
  simp only [rightConv, Pi.add_apply, mul_add]
  exact integral_add
    (((huc.comp (continuous_const.mul continuous_id)).mul hf₁).integrable_of_hasCompactSupport hf₁c.mul_left)
    (((huc.comp (continuous_const.mul continuous_id)).mul hf₂).integrable_of_hasCompactSupport hf₂c.mul_left)

private theorem rightConv_smul_right (c : ℂ) (u f : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K u (c • f) = c • rightConv K u f := by
  funext x
  simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]

private theorem rightConv_sum_right (u : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (F : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ k, Continuous (F k)) (hFc : ∀ k, HasCompactSupport (F k)) :
    rightConv K u (∑ k, F k) = ∑ k, rightConv K u (F k) := by
  funext x
  simp only [rightConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ =>
    ((huc.comp (continuous_const.mul continuous_id)).mul (hF k)).integrable_of_hasCompactSupport (hFc k).mul_left

private theorem rightConv_eq_sum_of_forall_eq_sum (u f : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (g h : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hg : ∀ k, Continuous (g k)) (hgc : ∀ k, HasCompactSupport (g k))
    (hh : ∀ k, Continuous (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hf : ∀ x, f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x) :
    rightConv K u f = ∑ k, rightConv K (rightConv K u (h k)) (g k) := by
  have hf' : f = ∑ k, rightConv K (g k) fun y => h k y⁻¹ := by
    funext x
    rw [hf x, Finset.sum_apply]
  have hinvc : ∀ k, Continuous fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k => (hh k).comp continuous_inv
  have hinvcs : ∀ k, HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k =>
    (hhc k).comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  rw [hf', rightConv_sum_right u huc _
    (fun k => continuous_rightConv_of_hasCompactSupport (g k) _ (hg k) (hinvc k) (hinvcs k))
    (fun k => hasCompactSupport_rightConv_inv (g k) (h k) (hgc k) (hhc k))]
  exact Finset.sum_congr rfl fun k _ => rightConv_rightConv_inv u (g k) (h k) huc (hg k) (hgc k) (hh k) (hhc k)

end ConvolutionAssociativity
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity"

section

open NumberField IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate Topology Classical

namespace FlatTestFn

variable (K : Type) [Field K]

private abbrev Ent := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private def dt (E : Ent K) : mixedEmbedding.mixedSpace K := E 0 0 * E 1 1 - E 0 1 * E 1 0

private def inv2 (E : Ent K) : Ent K :=
  ![![Ring.inverse (dt K E) * E 1 1, Ring.inverse (dt K E) * (-E 0 1)],
    ![Ring.inverse (dt K E) * (-E 1 0), Ring.inverse (dt K E) * E 0 0]]

private theorem dt_eq (E : Ent K) : dt K E = Matrix.det (Matrix.of E) := by
  rw [Matrix.det_fin_two]
  rfl

private theorem of_inv2 (E : Ent K) : Matrix.of (inv2 K E) = (Matrix.of E)⁻¹ := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, ← dt_eq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [inv2]

private theorem isUnit_dt_inv2 {E : Ent K} (h : IsUnit (dt K E)) : IsUnit (dt K (inv2 K E)) := by
  rw [dt_eq, of_inv2]
  exact Matrix.isUnit_nonsing_inv_det _ (by rwa [← dt_eq])

private theorem inv2_inv2 {E : Ent K} (h : IsUnit (dt K E)) : inv2 K (inv2 K E) = E := by
  apply Matrix.of.injective
  rw [of_inv2, of_inv2]
  exact Matrix.nonsing_inv_nonsing_inv _ (by rwa [← dt_eq])

private theorem of_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix.of (archEntries K g) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K →+* mixedEmbedding.mixedSpace K).mapMatrix
        (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  Matrix.ext fun _ _ => rfl

private theorem isUnit_dt_archEntries (g : GL (Fin 2) (InfiniteAdeleRing K)) : IsUnit (dt K (archEntries K g)) := by
  rw [dt_eq, of_archEntries, ← RingHom.map_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _

private theorem archEntries_inv (g : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K g⁻¹ = inv2 K (archEntries K g) := by
  apply Matrix.of.injective
  rw [of_inv2, of_archEntries, of_archEntries, Matrix.coe_units_inv]
  refine (Matrix.inv_eq_left_inv ?_).symm
  rw [← map_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit), map_one]

private theorem exists_archEntries_eq {E : Ent K} (h : IsUnit (dt K E)) :
    ∃ g : GL (Fin 2) (InfiniteAdeleRing K), archEntries K g = E := by
  have hM : IsUnit (Matrix.of fun i j => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (E i j)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have h' := h.map ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm :
      mixedEmbedding.mixedSpace K →+* InfiniteAdeleRing K)
    rw [dt_eq, RingHom.map_det] at h'
    exact h'
  refine ⟨hM.unit, ?_⟩
  funext i j
  show InfiniteAdeleRing.ringEquiv_mixedSpace K ((hM.unit : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) = E i j
  rw [hM.unit_spec]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

private theorem continuous_archEntries : Continuous (archEntries K) :=
  continuous_pi fun i => continuous_pi fun j =>
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

variable [NumberField K]

private theorem contDiff_entry (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun E : Ent K => E i j) :=
  contDiff_apply_apply ℝ (mixedEmbedding.mixedSpace K) i j

private theorem contDiff_dt : ContDiff ℝ (⊤ : ℕ∞) (dt K) :=
  ((contDiff_entry K 0 0).mul (contDiff_entry K 1 1)).sub ((contDiff_entry K 0 1).mul (contDiff_entry K 1 0))

private theorem contDiffAt_inv2 {E₀ : Ent K} (h : IsUnit (dt K E₀)) : ContDiffAt ℝ (⊤ : ℕ∞) (inv2 K) E₀ := by
  have hinv : ContDiffAt ℝ (⊤ : ℕ∞) (fun E : Ent K => Ring.inverse (dt K E)) E₀ := by
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (Ring.inverse : mixedEmbedding.mixedSpace K → mixedEmbedding.mixedSpace K) (dt K E₀) := by
      have := contDiffAt_ringInverse ℝ (n := (⊤ : ℕ∞)) h.unit
      rwa [h.unit_spec] at this
    exact h1.comp E₀ (contDiff_dt K).contDiffAt
  refine contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · exact hinv.mul (contDiff_entry K 1 1).contDiffAt
  · exact hinv.mul (contDiff_entry K 0 1).contDiffAt.neg
  · exact hinv.mul (contDiff_entry K 1 0).contDiffAt.neg
  · exact hinv.mul (contDiff_entry K 0 0).contDiffAt

private def flatFn (Φ : Ent K → ℂ) (E : Ent K) : ℂ :=
  if IsUnit (dt K E) then conj (Φ (inv2 K E)) else 0

variable {K}

private theorem contDiff_flatFn {Φ : Ent K → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hsupp : HasCompactSupport fa)
    (hfa : ∀ g, fa g = Φ (archEntries K g)) : ContDiff ℝ (⊤ : ℕ∞) (flatFn K Φ) := by
  refine contDiff_iff_contDiffAt.2 fun E₀ => ?_
  by_cases h : IsUnit (dt K E₀)
  · have hloc : flatFn K Φ =ᶠ[𝓝 E₀] fun E => Complex.conjCLE (Φ (inv2 K E)) := by
      filter_upwards [(Units.isOpen.preimage (contDiff_dt K).continuous).mem_nhds h] with E hE
      simp only [flatFn, if_pos (show IsUnit (dt K E) from hE), Complex.conjCLE_apply]
    exact ((Complex.conjCLE.contDiff.comp hΦ).contDiffAt.comp E₀ (contDiffAt_inv2 K h)).congr_of_eventuallyEq hloc
  ·
    have hS : IsCompact (archEntries K '' tsupport fa) := IsCompact.image hsupp (continuous_archEntries K)
    have hunit : ∀ F ∈ archEntries K '' tsupport fa, IsUnit (dt K F) := by
      rintro _ ⟨g, -, rfl⟩
      exact isUnit_dt_archEntries K g
    have hT : IsCompact (inv2 K '' (archEntries K '' tsupport fa)) :=
      hS.image_of_continuousOn fun F hF => (contDiffAt_inv2 K (hunit F hF)).continuousAt.continuousWithinAt
    have hE₀ : E₀ ∉ inv2 K '' (archEntries K '' tsupport fa) := by
      rintro ⟨F, hF, rfl⟩
      exact h (isUnit_dt_inv2 K (hunit F hF))
    have hloc : flatFn K Φ =ᶠ[𝓝 E₀] fun _ => 0 := by
      filter_upwards [hT.isClosed.isOpen_compl.mem_nhds hE₀] with E hE
      have hE' : E ∉ inv2 K '' (archEntries K '' tsupport fa) := hE
      show flatFn K Φ E = 0
      unfold flatFn
      split_ifs with hu
      · obtain ⟨g, hg⟩ := exists_archEntries_eq K (isUnit_dt_inv2 K hu)
        have hfg : fa g = 0 := by
          by_contra hne
          exact hE' ⟨archEntries K g, ⟨g, subset_tsupport _ hne, rfl⟩, by rw [hg]; exact inv2_inv2 K hu⟩
        rw [← hg, ← hfa, hfg, map_zero]
      · rfl
    exact contDiffAt_const.congr_of_eventuallyEq hloc

variable (K)

private theorem isArchTestFactor_conj_comp_inv
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (h : IsArchTestFactor K fa) :
    IsArchTestFactor K (fun g => conj (fa g⁻¹)) := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, hsupp⟩ := h
  refine ⟨⟨flatFn K Φ, contDiff_flatFn hΦ hsupp hfa, fun g => ?_⟩, ?_⟩
  · simp only [flatFn, isUnit_dt_archEntries K g, if_true, hfa g⁻¹, archEntries_inv]
  · exact (hsupp.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)

private theorem isFinTestFactor_conj_comp_inv
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (h : IsFinTestFactor K ff) :
    IsFinTestFactor K (fun g => conj (ff g⁻¹)) :=
  ⟨(h.1.comp_continuous continuous_inv).comp (fun z : ℂ => conj z),
    (h.2.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z : ℂ => conj z) (map_zero _)⟩

private theorem isFactorizableTestFn_conj_comp_inv
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsFactorizableTestFn K f) :
    IsFactorizableTestFn K (fun y => conj (f y⁻¹)) := by
  obtain ⟨fa, ff, hfa, hff, hf⟩ := hf
  refine ⟨fun g => conj (fa g⁻¹), fun g => conj (ff g⁻¹), isArchTestFactor_conj_comp_inv K hfa,
    isFinTestFactor_conj_comp_inv K hff, fun y => ?_⟩
  simp only [hf y⁻¹, map_inv, map_mul]

end FlatTestFn
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace WeightTwist

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.TateGlobal NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

private abbrev _root_.WeightedVenueTrace.WeightTwist.μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

p2m_export "WeightedVenueTrace.WeightTwist" "μ"

private def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')

private theorem _root_.WeightedVenueTrace.WeightTwist.wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

p2m_export "WeightedVenueTrace.WeightTwist" "wt_pos"

private theorem _root_.WeightedVenueTrace.WeightTwist.wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

p2m_export "WeightedVenueTrace.WeightTwist" "wt_bounds"

private def _root_.WeightedVenueTrace.WeightTwist.slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

p2m_export "WeightedVenueTrace.WeightTwist" "slab"
private theorem slab_measurableSet (α β : ℝ) : MeasurableSet (slab (K := K) α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem conv_apply (u g : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    rightConv K u g x = ∫ y, u (x * y) * g y ∂(μ K) := rfl

private theorem _root_.WeightedVenueTrace.WeightTwist.ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab (K := K) α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurableSet α β))

p2m_export "WeightedVenueTrace.WeightTwist" "ae_mem_slab"
private theorem ideleNorm_one' : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [mul_one] at h
  exact (mul_right_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h.symm.trans (one_mul _).symm))

private theorem ideleNorm_inv' (c : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K c⁻¹ = (ideleNorm K c)⁻¹ := by
  have h := ideleNorm_mul (F := K) c c⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact (wt_bounds α β σ hα x hx).2

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar, pow_two, ideleNorm_mul, pow_two]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

private theorem central_comm (c : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K c = centralScalar (𝓞 K) K c * X :=
  AutomorphicForm.SiegelCovering.mul_centralScalar_comm c X

private theorem det_unipotentGL2' (t : AdeleRing (𝓞 K) K) :
    Matrix.GeneralLinearGroup.det (unipotentGL2 t) = 1 := by
  ext
  simp [Matrix.det_fin_two_of]

private theorem wt_def (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    wt K σ x = ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) := rfl

private theorem wt_mul (σ : ℝ) (x y : AdelicGL2 (𝓞 K) K) : wt K σ (x * y) = wt K σ x * wt K σ y := by
  rw [wt_def, wt_def, wt_def, normDet_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, Complex.ofReal_mul]

private theorem wt_global (σ : ℝ) (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    wt K σ (globalPoints (𝓞 K) K γ * x) = wt K σ x := by
  rw [wt_def, wt_def, normDet_global]

private theorem wt_unipotent (σ : ℝ) (t : AdeleRing (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K) :
    wt K σ (unipotentGL2 t * x) = wt K σ x := by
  rw [wt_def, wt_def, normDet_mul, det_unipotentGL2', ideleNorm_one', one_mul]

private theorem sq_rpow_neg {a : ℝ} (ha : 0 < a) (σ : ℝ) : (a ^ 2) ^ (-σ) = a ^ (-(2 * σ)) := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha.le, Nat.cast_ofNat, mul_neg]

private theorem wt_central (σ : ℝ) (z : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    wt K σ (centralScalar (𝓞 K) K z * x) = ((ideleNorm K z ^ (-(2 * σ)) : ℝ) : ℂ) * wt K σ x := by
  rw [wt_def, wt_def, normDet_central, Real.mul_rpow (pow_nonneg (ideleNorm_pos _).le _) (ideleNorm_pos _).le,
    sq_rpow_neg (ideleNorm_pos z), Complex.ofReal_mul]

private def rpowChar (s : ℝ) : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ where
  toFun z := Units.mk0 ((ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ s : ℝ) : ℂ)
    (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (ideleNorm_pos _) s).ne')
  map_one' := Units.ext (by simp [ideleNorm_one'])
  map_mul' z w := Units.ext (by
    simp only [Subgroup.coe_mul, Units.val_mk0, Units.val_mul]
    rw [ideleNorm_mul, Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, Complex.ofReal_mul])

private theorem rpowChar_apply (s : ℝ) (z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) :
    ((rpowChar (K := K) s z : ℂˣ) : ℂ) = ((ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ s : ℝ) : ℂ) := rfl

private def twistChar (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ) :
    (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ :=
  ξ * rpowChar (-(2 * σ))

private theorem norm_twistChar (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) :
    ‖((twistChar ξ σ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ (-σ) := by
  have hpos := ideleNorm_pos (z : (AdeleRing (𝓞 K) K)ˣ)
  rw [twistChar, MonoidHom.mul_apply, Units.val_mul, norm_mul, hσ, rpowChar_apply, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _), ← Real.rpow_add hpos]
  congr 1
  ring

private def twist (σ : ℝ) (u : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) : ℂ := u x * wt K σ x

private theorem continuous_twist (σ : ℝ) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u) :
    Continuous (twist σ u) :=
  hu.mul (wt_continuous σ)

private theorem isLsXiFunction_twist (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) :
    IsLsXiFunction (𝓞 K) K ⊤ (twistChar ξ σ) (twist σ u) where
  left_invariant γ g := by
    simp only [twist, hu.left_invariant, wt_global]
  central_transform z g := by
    simp only [twist, hu.central_transform, wt_central, twistChar, MonoidHom.mul_apply, Units.val_mul, rpowChar_apply]
    ring

private theorem isCuspidalFn_twist (σ : ℝ) (ν : Measure (AdeleRing (𝓞 K) K)) {u : AdelicGL2 (𝓞 K) K → ℂ}
    (hu : IsCuspidalFn ν unipotentGL2 u) : IsCuspidalFn ν unipotentGL2 (twist σ u) := by
  intro g
  have h0 : (∫ t, u (unipotentGL2 t * g) ∂ν) = 0 := hu g
  show (∫ t, twist σ u (unipotentGL2 t * g) ∂ν) = 0
  simp only [twist, wt_unipotent]
  rw [integral_mul_const, h0, zero_mul]

private theorem memLp_twist (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : MemLp u 2 ((μ K).restrict Φ₀)) : MemLp (twist σ u) 2 ((μ K).restrict Φ₀) :=
  (memLp_top_of_bound (wt_continuous σ).aestronglyMeasurable _ (wt_ae_bound α β σ hα Φ₀ hΦ₀)).mul hu

private def flat (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) : ℂ :=
  conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)

private theorem flat_eq (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) :
    flat σ g = fun y => conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ) := rfl

private theorem flat_flat (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) : flat σ (flat σ g) = g := by
  funext y
  have hpos := ideleNorm_pos (Matrix.GeneralLinearGroup.det y)
  simp only [flat, inv_inv, map_mul, Complex.conj_conj, Complex.conj_ofReal, map_inv, ideleNorm_inv',
    Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv]
  rw [mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.rpow_pos_of_pos hpos σ).ne', Complex.ofReal_one, mul_one]

private theorem rightConv_flat (σ : ℝ) (u g : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    rightConv K u (flat σ g) x =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ σ : ℝ) : ℂ) *
        rightConv K (twist σ u) (fun y => conj (g y⁻¹)) x := by
  have hx := ideleNorm_pos (Matrix.GeneralLinearGroup.det x)
  rw [conv_apply, conv_apply, ← integral_const_mul]
  congr 1
  funext y
  simp only [flat, twist, wt_mul]
  simp only [wt_def]
  have h1 : ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ σ : ℝ) : ℂ) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, Real.rpow_neg hx.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hx σ).ne', Complex.ofReal_one]
  linear_combination
    (-(u (x * y) * conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))) * h1

private theorem normSq_mul_wt_transport (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : IsLsXiFunction (𝓞 K) K ⊤ ξ F) (γ : Matrix.GeneralLinearGroup (Fin 2) K)
    (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    ‖F (globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z)‖ ^ 2 *
        ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z)) ^ (-σ) =
      ‖F g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-σ) := by
  have hz := ideleNorm_pos z
  have hnorm : ‖F (globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z)‖ = ideleNorm K z ^ σ * ‖F g‖ := by
    rw [mul_assoc, central_comm, hF.left_invariant, hF.central_transform ⟨z, Subgroup.mem_top z⟩, norm_mul]
    exact congrArg (· * ‖F g‖) (hσ ⟨z, Subgroup.mem_top z⟩)
  have hdet : ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z)) =
      ideleNorm K z ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) := by
    rw [mul_assoc, central_comm, normDet_global, normDet_central]
  rw [hnorm, hdet, Real.mul_rpow (pow_nonneg hz.le _) (ideleNorm_pos _).le, sq_rpow_neg hz, mul_pow]
  have h2 : (ideleNorm K z ^ σ) ^ 2 * ideleNorm K z ^ (-(2 * σ)) = 1 := by
    rw [← Real.rpow_natCast (ideleNorm K z ^ σ) 2, ← Real.rpow_mul hz.le, Nat.cast_ofNat, ← Real.rpow_add hz,
      show σ * 2 + -(2 * σ) = 0 by ring, Real.rpow_zero]
  linear_combination (‖F g‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (-σ)) * h2

private theorem normDet_siegel (c' u' d₁' d₂' : ℝ) (hd₁' : 0 < d₁') {x : AdelicGL2 (𝓞 K) K}
    (hx : x ∈ centreCutSiegelSet K c' u' d₁' d₂') :
    ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈
      Set.Icc (d₁' ^ (∑ w : InfinitePlace K, w.mult)) (d₂' ^ (∑ w : InfinitePlace K, w.mult)) := by
  rw [mem_centreCutSiegelSet_iff] at hx
  obtain ⟨hfin, -, -, hdet⟩ := hx
  rw [ideleNorm_det_eq_prod_archDetNorm_pow_mult K x hfin, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_pow_eq_pow_sum]
  constructor
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg hd₁'.le _)
      fun w _ => pow_le_pow_left₀ hd₁'.le (hdet w).1 _
  · exact Finset.prod_le_prod (fun w _ => pow_nonneg (archDetNorm_pos w x).le _)
      fun w _ => pow_le_pow_left₀ (archDetNorm_pos w x).le (hdet w).2 _

private theorem integral_normSq_le_inv_min_mul (σ α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ᵐ x ∂((μ K).restrict S), x ∈ slab (K := K) α β) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : Integrable (fun x => ‖u x‖ ^ 2) ((μ K).restrict S))
    (huw : Integrable (fun x => ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)) ((μ K).restrict S)) :
    ∫ x in S, ‖u x‖ ^ 2 ∂(μ K) ≤ (min (α ^ (-σ)) (β ^ (-σ)))⁻¹ *
      ∫ x in S, ‖u x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  have hm : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
    lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans_le hαβ) _)
  rw [← integral_const_mul]
  refine integral_mono_ae hu (huw.const_mul _) (hS.mono fun x hx => ?_)
  have h1 := (wt_bounds α β σ hα x hx).1
  rw [le_inv_mul_iff₀ hm, mul_comm]
  exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)

private theorem exists_forall_mem_window_wt_le (σ c' u' d₁' d₂' : ℝ) (hd₁' : 0 < d₁')
    (T : Finset (AdelicGL2 (𝓞 K) K)) :
    ∃ W : ℝ, ∀ y ∈ ⋃ t ∈ T, (· * t) '' centreCutSiegelSet K c' u' d₁' d₂',
      ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) ≤ W := by
  refine ⟨∑ t ∈ T,
    max ((d₁' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t)) ^ (-σ))
      ((d₂' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t)) ^ (-σ)), fun y hy => ?_⟩
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
  obtain ⟨t, ht, x, hx, rfl⟩ := hy
  have hxdet := normDet_siegel (K := K) c' u' d₁' d₂' hd₁' hx
  have htpos := ideleNorm_pos (Matrix.GeneralLinearGroup.det t)
  have hapos : 0 < d₁' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t) :=
    mul_pos (pow_pos hd₁' _) htpos
  have hmem : ideleNorm K (Matrix.GeneralLinearGroup.det (x * t)) ∈
      Set.Icc (d₁' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t))
        (d₂' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t)) := by
    rw [normDet_mul]
    exact ⟨mul_le_mul_of_nonneg_right hxdet.1 htpos.le, mul_le_mul_of_nonneg_right hxdet.2 htpos.le⟩
  refine (wt_bounds _ _ σ hapos _ hmem).2.trans ?_
  have hle : ∀ t ∈ T, (0 : ℝ) ≤
      max ((d₁' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t)) ^ (-σ))
        ((d₂' ^ (∑ w : InfinitePlace K, w.mult) * ideleNorm K (Matrix.GeneralLinearGroup.det t)) ^ (-σ)) :=
    fun t _ => le_max_of_le_left (Real.rpow_nonneg (mul_pos (pow_pos hd₁' _) (ideleNorm_pos _)).le _)
  exact Finset.single_le_sum hle ht

end WeightTwist
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace

namespace FamilyBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]

private theorem norm_sq_sum_smul {e : ι → E} (he : Orthonormal ℂ e) (l : ι → ℂ) :
    ‖∑ i, l i • e i‖ ^ 2 = ∑ i, ‖l i‖ ^ 2 := by
  have h : ⟪∑ i, l i • e i, ∑ i, l i • e i⟫_ℂ = ∑ i, ((‖l i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, he.inner_right_fintype l i]
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  rw [inner_self_eq_norm_sq_to_K] at h
  refine Complex.ofReal_injective ?_
  rw [Complex.ofReal_pow, Complex.ofReal_sum]
  exact h

private theorem sum_norm_sq_apply_le {e : ι → E} (he : Orthonormal ℂ e) (L : E →ₗ[ℂ] ℂ) (C : ℝ)
    (hL : ∀ l : ι → ℂ, ‖L (∑ i, l i • e i)‖ ≤ C * ‖∑ i, l i • e i‖) :
    ∑ i, ‖L (e i)‖ ^ 2 ≤ C ^ 2 := by
  set S : ℝ := ∑ i, ‖L (e i)‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  set l : ι → ℂ := fun i => conj (L (e i)) with hl
  have hLu : ‖L (∑ i, l i • e i)‖ = S := by
    have h : L (∑ i, l i • e i) = ((S : ℝ) : ℂ) := by
      rw [map_sum, hS, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, smul_eq_mul, hl, Complex.conj_mul', Complex.ofReal_pow]
    rw [h, Complex.norm_real, Real.norm_of_nonneg hS0]
  have hu : ‖∑ i, l i • e i‖ ^ 2 = S := by
    rw [norm_sq_sum_smul he l, hS]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hl, RCLike.norm_conj]
  have hmain : S * S ≤ C ^ 2 * S := by
    have h1 : S ≤ C * ‖∑ i, l i • e i‖ := by
      rw [← hLu]
      exact hL l
    have h2 : S ^ 2 ≤ (C * ‖∑ i, l i • e i‖) ^ 2 := pow_le_pow_left₀ hS0 h1 2
    rw [mul_pow, hu] at h2
    simpa only [sq] using h2
  rcases hS0.lt_or_eq with hpos | hzero
  · exact le_of_mul_le_mul_right hmain hpos
  · rw [← hzero]
    exact sq_nonneg C

variable {X : Type*} {M : Type*}

private theorem sum_norm_sq_mul_le_of_moves (F : ι → X → ℂ) (w : X → ℝ) (act : M → X → X) (D : Set X) {B W : ℝ}
    (hinv : ∀ i (m : M) (x : X), ‖F i (act m x)‖ ^ 2 * w (act m x) = ‖F i x‖ ^ 2 * w x)
    (hcov : ∀ x : X, ∃ m : M, act m x ∈ D) (hB : ∀ d ∈ D, ∑ i, ‖F i d‖ ^ 2 ≤ B) (hW : ∀ d ∈ D, w d ≤ W)
    (hw : ∀ x, 0 ≤ w x) (hB0 : 0 ≤ B) (x : X) : (∑ i, ‖F i x‖ ^ 2) * w x ≤ B * W := by
  obtain ⟨m, hm⟩ := hcov x
  calc (∑ i, ‖F i x‖ ^ 2) * w x = ∑ i, ‖F i x‖ ^ 2 * w x := Finset.sum_mul _ _ _
    _ = ∑ i, ‖F i (act m x)‖ ^ 2 * w (act m x) := Finset.sum_congr rfl fun i _ => (hinv i m x).symm
    _ = (∑ i, ‖F i (act m x)‖ ^ 2) * w (act m x) := (Finset.sum_mul _ _ _).symm
    _ ≤ B * W := mul_le_mul (hB _ hm) (hW _ hm) (hw _) hB0

variable [MeasurableSpace X]

private theorem sum_integral_le_of_forall_le (μ : Measure X) (Φ₀ : Set X) [IsFiniteMeasure (μ.restrict Φ₀)]
    (F : ι → X → ℂ) (w : X → ℝ) {K : ℝ}
    (hint : ∀ i, Integrable (fun x => ‖F i x‖ ^ 2 * w x) (μ.restrict Φ₀))
    (hK : ∀ x, (∑ i, ‖F i x‖ ^ 2) * w x ≤ K) :
    ∑ i, ∫ x in Φ₀, ‖F i x‖ ^ 2 * w x ∂μ ≤ K * μ.real Φ₀ := by
  rw [← integral_finsetSum _ fun i _ => hint i]
  calc ∫ x in Φ₀, ∑ i, ‖F i x‖ ^ 2 * w x ∂μ ≤ ∫ _ in Φ₀, K ∂μ := by
        refine integral_mono (integrable_finsetSum _ fun i _ => hint i) (integrable_const K) fun x => ?_
        simpa only [← Finset.sum_mul] using hK x
    _ = K * μ.real Φ₀ := by rw [setIntegral_const, smul_eq_mul, mul_comm]

end FamilyBounds
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

section

open NumberField NumberField.AdelicLevel
open MeasureTheory

namespace Dichotomy

open AutomorphicForm

variable {F L : Type} [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L) (σ : L ≃ₐ[F] L)

private theorem twistedConvOp_centralScalar_mul
    (act : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ)
    (hact : ∀ z, sigmaAdelicAct F L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (act z))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (f u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξ u) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp F L D σ f u (centralScalar (𝓞 L) L z * x) =
      ((ξ ⟨act z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * twistedConvOp F L D σ f u x := by
  simp only [twistedConvOp_apply, rightConv_apply]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  have h1 : sigmaSectionActOn F L D σ u (centralScalar (𝓞 L) L z * x * y) =
      ((ξ ⟨act z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) * sigmaSectionActOn F L D σ u (x * y) := by
    show u (sigmaAdelicAct F L D σ (centralScalar (𝓞 L) L z * x * y)) =
      _ * u (sigmaAdelicAct F L D σ (x * y))
    rw [mul_assoc, map_mul, hact]
    exact hu.central_transform ⟨act z, Subgroup.mem_top _⟩ _
  beta_reduce
  rw [h1, mul_assoc]

private theorem twistedConvOp_eq_zero_of_ne
    (act : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ)
    (hact : ∀ z, sigmaAdelicAct F L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (act z))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (f u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξ u)
    (hT : IsLsXiFunction (𝓞 L) L ⊤ ξ (twistedConvOp F L D σ f u))
    (hne : ¬ ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ), ξ ⟨act z, Subgroup.mem_top _⟩ = ξ z) :
    twistedConvOp F L D σ f u = 0 := by
  obtain ⟨z, hz⟩ := not_forall.mp hne
  funext x
  have h1 := twistedConvOp_centralScalar_mul D σ act hact ξ f u hu (z : (AdeleRing (𝓞 L) L)ˣ) x
  have h2 := hT.central_transform z x
  have hne' : ((ξ ⟨act z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ≠ ((ξ z : ℂˣ) : ℂ) :=
    fun h => hz (Units.val_injective h)
  have h3 : (((ξ ⟨act z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) - ((ξ z : ℂˣ) : ℂ)) *
      twistedConvOp F L D σ f u x = 0 := by
    rw [sub_mul, ← h1, ← h2, sub_self]
  rcases mul_eq_zero.mp h3 with h | h
  · exact absurd (sub_eq_zero.mp h) hne'
  · exact h

end Dichotomy
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm
open IsDedekindDomain
open scoped ProbabilityTheory ENNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace WindowForms

variable (K : Type) [Field K] [NumberField K]

private theorem integrable_constantTermIntegrand
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (g : AdelicGL2 (𝓞 K) K) :
    Integrable (constantTermIntegrand unipotentGL2 f g)
      ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  have hcont : Continuous (constantTermIntegrand unipotentGL2 f g) :=
    hf.comp (continuous_unipotentGL2.mul continuous_const)
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 K) K
  have hint : IntegrableOn (constantTermIntegrand unipotentGL2 f g) (adelicBox K)
      (adelicAddHaar (𝓞 K) K) :=
    (hcont.continuousOn.integrableOn_compact hC).mono_set hsub
  exact hint.smul_measure (ENNReal.inv_ne_top.2 (adelicAddHaar_adelicBox_pos K).ne')

private def windowForms (W : Set (AdelicGL2 (𝓞 K) K)) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W) ∧
    IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ}
  zero_mem' :=
    ⟨continuous_const, isLsXiFunction_zero (𝓞 K) K ⊤ ξ, MemLp.zero, fun g => constantTerm_zero _ _ g⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφl, hφ2, hφz⟩ ⟨hψc, hψl, hψ2, hψz⟩
    refine ⟨hφc.add hψc, ⟨fun γ g => ?_, fun z g => ?_⟩, hφ2.add hψ2, fun g => ?_⟩
    · simp only [Pi.add_apply, hφl.left_invariant, hψl.left_invariant]
    · simp only [Pi.add_apply, hφl.central_transform, hψl.central_transform, mul_add]
    · have h1 := hφz g
      have h2 := hψz g
      have hsplit : constantTermIntegrand unipotentGL2 (φ + ψ) g =
          fun q => constantTermIntegrand unipotentGL2 φ g q + constantTermIntegrand unipotentGL2 ψ g q := rfl
      unfold constantTerm at h1 h2 ⊢
      rw [hsplit, integral_add (integrable_constantTermIntegrand K hφc g) (integrable_constantTermIntegrand K hψc g),
        h1, h2, add_zero]
  smul_mem' := by
    rintro c φ ⟨hφc, hφl, hφ2, hφz⟩
    refine ⟨hφc.const_smul c, ⟨fun γ g => ?_, fun z g => ?_⟩, hφ2.const_smul c, fun g => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hφl.left_invariant]
    · simp only [Pi.smul_apply, smul_eq_mul, hφl.central_transform, mul_left_comm]
    · have h1 := hφz g
      have hsplit : constantTermIntegrand unipotentGL2 (c • φ) g =
          fun q => c * constantTermIntegrand unipotentGL2 φ g q := rfl
      unfold constantTerm at h1 ⊢
      rw [hsplit, integral_const_mul, h1, mul_zero]

variable {K}

private theorem mem_windowForms_iff {W : Set (AdelicGL2 (𝓞 K) K)} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} :
    φ ∈ windowForms K W ξ ↔
      Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W) ∧
        IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ :=
  Iff.rfl

private theorem IsIsotypicCuspFormAt.mem_windowForms {W : Set (AdelicGL2 (𝓞 K) K)}
    {U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)} {gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K}
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Φ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ φ) :
    φ ∈ windowForms K W ξ := by
  have hcusp : IsCuspAutomorphicFnAt K (productionPinsOf K W U gen (adelicBox K)) ξ φ := h.smoothCusp.1
  have hmem : LsXiMemberAt (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ W φ := hcusp.1
  obtain ⟨hl, h2⟩ := (lsXiMemberAt_iff (𝓞 K) K (adelicGLHaar (Fin 2) (𝓞 K) K) ⊤ ξ W φ).1 hmem
  exact ⟨h.continuous, hl, h2, hcusp.2⟩

private theorem isotypicCuspSubmodule_le_windowForms (W : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K)) (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Φ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ ≤ windowForms K W ξ :=
  Submodule.span_le.2 fun _ hφ => IsIsotypicCuspFormAt.mem_windowForms hφ

end WindowForms
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open scoped ENNReal NNReal
open NumberField.TateGlobal
open scoped Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace CoverBound

variable {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  {ν : Measure α} [SMulInvariantMeasure G α ν]

private theorem lintegral_fd_le_of_cover {s : Set α} (hFD : IsFundamentalDomain G s ν) {F : α → ℝ≥0∞}
    (hFm : Measurable F) (hF : ∀ (g : G) (x : α), F (g • x) = F x) {P : Set α} (hP : MeasurableSet P)
    (hcov : ∀ x ∈ s, ∃ g : G, g • x ∈ P) :
    ∫⁻ x in s, F x ∂ν ≤ ∫⁻ x in P, F x ∂ν := by
  have hpt : ∀ x ∈ s, F x ≤ ∑' g : G, P.indicator F (g • x) := by
    intro x hx
    obtain ⟨g₀, hg₀⟩ := hcov x hx
    calc F x = P.indicator F (g₀ • x) := by rw [Set.indicator_of_mem hg₀, hF]
      _ ≤ ∑' g : G, P.indicator F (g • x) := ENNReal.le_tsum g₀
  have hterm : ∀ g : G, Measurable fun x => P.indicator F (g • x) :=
    fun g => (hFm.indicator hP).comp (measurable_const_smul g)
  calc ∫⁻ x in s, F x ∂ν ≤ ∫⁻ x in s, ∑' g : G, P.indicator F (g • x) ∂ν :=
        lintegral_mono_ae ((ae_restrict_mem₀ hFD.nullMeasurableSet).mono fun x hx => hpt x hx)
    _ = ∑' g : G, ∫⁻ x in s, P.indicator F (g • x) ∂ν :=
        lintegral_tsum fun g => (hterm g).aemeasurable
    _ = ∫⁻ x, P.indicator F x ∂ν := (hFD.lintegral_eq_tsum'' (P.indicator F)).symm
    _ = ∫⁻ x in P, F x ∂ν := lintegral_indicator hP F

end CoverBound
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist"

namespace SlabSquareIntegrable

open CoverBound

variable (K : Type) [Field K] [NumberField K]

private abbrev _root_.WeightedVenueTrace.SlabSquareIntegrable.μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

p2m_export "WeightedVenueTrace.SlabSquareIntegrable" "μ"
variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private scoped instance instRightInvμ : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

variable (K)

private def _root_.WeightedVenueTrace.SlabSquareIntegrable.slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

p2m_export "WeightedVenueTrace.SlabSquareIntegrable" "slab"
private abbrev _root_.WeightedVenueTrace.SlabSquareIntegrable.Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

p2m_export "WeightedVenueTrace.SlabSquareIntegrable" "Γ"

private def sqE (φ : AdelicGL2 (𝓞 K) K → ℂ) (y : AdelicGL2 (𝓞 K) K) : ℝ≥0∞ := ‖φ y‖ₑ ^ (2 : ℝ)

private def piece (c u d₁ d₂ : ℝ) (n : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) : Set (AdelicGL2 (𝓞 K) K) :=
  (· * (centralScalar (𝓞 K) K n * x)) '' centreCutSiegelSet K c u d₁ d₂

variable {K}

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict (slab K α β)) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ slab K α β =
      (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ slab K α β) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, slab_Γ_stable]
  rw [hset, measure_preimage_mul]

private theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) := Units.val_injective.countable
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

private theorem central_comm (c : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * centralScalar (𝓞 K) K c = centralScalar (𝓞 K) K c * X :=
  AutomorphicForm.SiegelCovering.mul_centralScalar_comm c X

private theorem measurable_sqE {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) : Measurable (sqE K φ) :=
  hφ.measurable.enorm.pow_const _

private theorem sqE_smul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (γ : Γ K) (y : AdelicGL2 (𝓞 K) K) : sqE K φ (γ • y) = sqE K φ y := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  simp only [sqE, Γ_smul, hγ₀, hl.left_invariant]

private theorem sqE_centralScalar_mul {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (n : (AdeleRing (𝓞 K) K)ˣ) (y : AdelicGL2 (𝓞 K) K) :
    sqE K φ (centralScalar (𝓞 K) K n * y) = ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) * sqE K φ y := by
  have h := hl.central_transform ⟨n, Subgroup.mem_top n⟩ y
  dsimp only at h
  simp only [sqE, h, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]

private theorem piece_eq (c u d₁ d₂ : ℝ) (n : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    piece K c u d₁ d₂ n x = (centralScalar (𝓞 K) K n * ·) '' ((· * x) '' centreCutSiegelSet K c u d₁ d₂) := by
  unfold piece
  rw [Set.image_image]
  congr 1
  funext s
  simp only [← mul_assoc, central_comm]

private theorem measurableSet_piece (c u d₁ d₂ : ℝ) (n : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    MeasurableSet (piece K c u d₁ d₂ n x) := by
  unfold piece
  rw [Set.image_mul_right]
  exact measurable_mul_const _ (measurableSet_centreCutSiegelSet (F := K) c u d₁ d₂)

private theorem lintegral_piece (c u d₁ d₂ : ℝ) (n : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K)
    (F : AdelicGL2 (𝓞 K) K → ℝ≥0∞) :
    ∫⁻ y in piece K c u d₁ d₂ n x, F y ∂(μ K) =
      ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, F (centralScalar (𝓞 K) K n * y) ∂(μ K) := by
  rw [piece_eq]
  exact ((measurePreserving_mul_left (μ K) (centralScalar (𝓞 K) K n)).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft (centralScalar (𝓞 K) K n)).measurableEmbedding F _).symm

private theorem lintegral_piece_lt_top (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ φ)
    (hW : ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, sqE K φ y ∂(μ K) < ⊤)
    (n : (AdeleRing (𝓞 K) K)ˣ) {x : AdelicGL2 (𝓞 K) K} (hx : x ∈ T) :
    ∫⁻ y in piece K c u d₁ d₂ n x, sqE K φ y ∂(μ K) < ⊤ := by
  rw [lintegral_piece]
  calc ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, sqE K φ (centralScalar (𝓞 K) K n * y) ∂(μ K)
      = ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂,
          ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) * sqE K φ y ∂(μ K) :=
        lintegral_congr fun y => sqE_centralScalar_mul hl n y
    _ = ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) *
          ∫⁻ y in (· * x) '' centreCutSiegelSet K c u d₁ d₂, sqE K φ y ∂(μ K) :=
        lintegral_const_mul _ (measurable_sqE hφc)
    _ ≤ ‖((ξ ⟨n, Subgroup.mem_top n⟩ : ℂˣ) : ℂ)‖ₑ ^ (2 : ℝ) *
          ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, sqE K φ y ∂(μ K) :=
        mul_le_mul_right (lintegral_mono_set (Set.subset_iUnion₂ x hx)) _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) enorm_ne_top) hW

private theorem exists_finset_forall_exists_smul_mem_iUnion_piece (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂) (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) (α β : ℝ)
    (hα : 0 < α) {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∃ N : Finset (AdeleRing (𝓞 K) K)ˣ, ∀ y ∈ Φ₀, ∃ γ : Γ K,
      γ • y ∈ ⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2 := by
  obtain ⟨N, hN⟩ := exists_finset_central_slab_covering_of_coversModCentre K c u d₁ d₂ T hd hcov α β hα
  refine ⟨N, fun y hy => ?_⟩
  obtain ⟨γ, n, hn, x, hx, hmem⟩ := hN y (hΦ₀ hy)
  refine ⟨⟨globalPoints (𝓞 K) K γ, MonoidHom.mem_range.2 ⟨γ, rfl⟩⟩, ?_⟩
  show globalPoints (𝓞 K) K γ * y ∈ _
  exact Set.mem_iUnion.2 ⟨⟨(n, x), Finset.mk_mem_product hn hx⟩, hmem⟩

private theorem measure_piece (c u d₁ d₂ : ℝ) (n : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    μ K (piece K c u d₁ d₂ n x) = μ K (centreCutSiegelSet K c u d₁ d₂) := by
  have h := lintegral_piece c u d₁ d₂ n x fun _ => (1 : ℝ≥0∞)
  rw [setLIntegral_one, setLIntegral_one] at h
  rw [h, Set.image_mul_right, measure_preimage_mul_right]

private theorem measure_fd_lt_top
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) : μ K Φ₀ < ⊤ := by
  obtain ⟨N, hcover⟩ := exists_finset_forall_exists_smul_mem_iUnion_piece c u d₁ d₂ T hd hcov α β hα hΦ₀
  have hPm : MeasurableSet (⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2) :=
    MeasurableSet.iUnion fun p => measurableSet_piece c u d₁ d₂ p.1.1 p.1.2
  haveI := countable_Γ (K := K)
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hmain := lintegral_fd_le_of_cover hFD (measurable_const (a := (1 : ℝ≥0∞))) (fun _ _ => rfl) hPm hcover
  calc μ K Φ₀ = ∫⁻ _ in Φ₀, (1 : ℝ≥0∞) ∂(μ K) := (setLIntegral_one _).symm
    _ = ∫⁻ _ in Φ₀, (1 : ℝ≥0∞) ∂((μ K).restrict (slab K α β)) := by
        rw [Measure.restrict_restrict' (slab_measurable α β), Set.inter_eq_left.2 hΦ₀]
    _ ≤ ∫⁻ _ in ⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2, (1 : ℝ≥0∞) ∂((μ K).restrict (slab K α β)) := hmain
    _ ≤ ∫⁻ _ in ⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2, (1 : ℝ≥0∞) ∂(μ K) :=
        lintegral_mono' (Measure.restrict_mono (Set.Subset.refl _) Measure.restrict_le_self) le_rfl
    _ ≤ ∑' p : ↥(N ×ˢ T), ∫⁻ _ in piece K c u d₁ d₂ p.1.1 p.1.2, (1 : ℝ≥0∞) ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ p : ↥(N ×ˢ T), μ K (centreCutSiegelSet K c u d₁ d₂) := by
        rw [tsum_fintype]
        exact Finset.sum_congr rfl fun p _ => by rw [setLIntegral_one, measure_piece]
    _ < ⊤ := ENNReal.sum_lt_top.2 fun _ _ => SiegelVolume.measure_centreCutSiegelSet_lt_top (μ K) hc u hd₁ d₂

private theorem memLp_restrict_of_memLp_restrict_window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφc : Continuous φ)
    (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ φ)
    (h2 : MemLp φ 2 ((μ K).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))) :
    MemLp φ 2 ((μ K).restrict Φ₀) := by
  obtain ⟨N, hcover⟩ := exists_finset_forall_exists_smul_mem_iUnion_piece c u d₁ d₂ T hd hcov α β hα hΦ₀
  have hW : ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, sqE K φ y ∂(μ K) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top h2.eLpNorm_lt_top
    simpa [sqE] using h
  have hPm : MeasurableSet (⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2) :=
    MeasurableSet.iUnion fun p => measurableSet_piece c u d₁ d₂ p.1.1 p.1.2
  haveI := countable_Γ (K := K)
  haveI := smulInvariant_restrict_slab (K := K) α β
  have hmain := lintegral_fd_le_of_cover hFD (measurable_sqE hφc) (sqE_smul hl) hPm hcover
  refine ⟨hφc.aestronglyMeasurable,
    (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top).2 ?_⟩
  simp only [ENNReal.toReal_ofNat]
  show ∫⁻ y in Φ₀, sqE K φ y ∂(μ K) < ⊤
  calc ∫⁻ y in Φ₀, sqE K φ y ∂(μ K) = ∫⁻ y in Φ₀, sqE K φ y ∂((μ K).restrict (slab K α β)) := by
        rw [Measure.restrict_restrict' (slab_measurable α β), Set.inter_eq_left.2 hΦ₀]
    _ ≤ ∫⁻ y in ⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2, sqE K φ y ∂((μ K).restrict (slab K α β)) := hmain
    _ ≤ ∫⁻ y in ⋃ p : ↥(N ×ˢ T), piece K c u d₁ d₂ p.1.1 p.1.2, sqE K φ y ∂(μ K) :=
        lintegral_mono' (Measure.restrict_mono (Set.Subset.refl _) Measure.restrict_le_self) le_rfl
    _ ≤ ∑' p : ↥(N ×ˢ T), ∫⁻ y in piece K c u d₁ d₂ p.1.1 p.1.2, sqE K φ y ∂(μ K) := lintegral_iUnion_le _ _
    _ = ∑ p : ↥(N ×ˢ T), ∫⁻ y in piece K c u d₁ d₂ p.1.1 p.1.2, sqE K φ y ∂(μ K) := tsum_fintype _
    _ < ⊤ := ENNReal.sum_lt_top.2 fun p _ =>
        lintegral_piece_lt_top c u d₁ d₂ T hφc hl hW p.1.1 (Finset.mem_product.1 p.2).2

end SlabSquareIntegrable
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_adeleBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace TwistCuspidal

variable (K : Type) [Field K] [NumberField K]

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.coe_injective (K := K)).countable

private scoped instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine (Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_)
  intro I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  exact ⟨s, hs⟩

private scoped instance countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Function.Injective.countable (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h

open scoped RestrictedProduct in
private scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    exact UniformSpace.secondCountable_of_separable _
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_adeleRing : SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

private theorem globalPoints_unipotentGL2 (K : Type) [Field K] [NumberField K] (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

variable {K}

private scoped instance instAddHaar : (adelicAddHaar (𝓞 K) K).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 K) K

variable {F : Type} [Field F] [Algebra F K] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) F K) (τ : K ≃ₐ[F] K)

private theorem act_act_inv (x : AdeleRing (𝓞 K) K) : D.act τ (D.act τ⁻¹ x) = x := by
  rw [← RingAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, RingAut.one_apply]

private theorem act_inv_act (x : AdeleRing (𝓞 K) K) : D.act τ⁻¹ (D.act τ x) = x := by
  rw [← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]

private def actHomeomorph : AdeleRing (𝓞 K) K ≃ₜ AdeleRing (𝓞 K) K where
  toFun := D.act τ
  invFun := D.act τ⁻¹
  left_inv := act_inv_act D τ
  right_inv := act_act_inv D τ
  continuous_toFun := D.continuous_act τ
  continuous_invFun := D.continuous_act τ⁻¹

private def adeleActEquiv : AdeleRing (𝓞 K) K ≃ᵐ AdeleRing (𝓞 K) K := (actHomeomorph D τ).toMeasurableEquiv

private theorem continuous_act_symm : Continuous (D.act τ : AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 K) K).symm := by
  have h := D.continuous_act τ⁻¹
  rw [map_inv] at h
  exact h

private theorem exists_map_actEquiv_eq_smul :
    ∃ c : ENNReal, Measure.map (adeleActEquiv D τ) (adelicAddHaar (𝓞 K) K) = c • adelicAddHaar (𝓞 K) K := by
  haveI : (Measure.map (adeleActEquiv D τ) (adelicAddHaar (𝓞 K) K)).IsAddHaarMeasure :=
    (D.act τ : AdeleRing (𝓞 K) K ≃+* AdeleRing (𝓞 K) K).toAddEquiv.isAddHaarMeasure_map (adelicAddHaar (𝓞 K) K)
      (D.continuous_act τ) (continuous_act_symm D τ)
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩

private def principalAct (ρ : K ≃ₐ[F] K) (k : AdeleRing.principalSubgroup (𝓞 K) K) :
    AdeleRing.principalSubgroup (𝓞 K) K :=
  ⟨D.act ρ k, by
    obtain ⟨k₀, hk₀⟩ := RingHom.mem_range.1 k.2
    exact RingHom.mem_range.2 ⟨ρ k₀, by rw [← hk₀, D.compat]⟩⟩

private theorem coe_principalAct (ρ : K ≃ₐ[F] K) (k : AdeleRing.principalSubgroup (𝓞 K) K) :
    ((principalAct D ρ k : AdeleRing.principalSubgroup (𝓞 K) K) : AdeleRing (𝓞 K) K) = D.act ρ k := rfl

private def principalEquiv : AdeleRing.principalSubgroup (𝓞 K) K ≃ AdeleRing.principalSubgroup (𝓞 K) K where
  toFun := principalAct D τ⁻¹
  invFun := principalAct D τ
  left_inv k := Subtype.ext (by rw [coe_principalAct, coe_principalAct, act_act_inv])
  right_inv k := Subtype.ext (by rw [coe_principalAct, coe_principalAct, act_inv_act])

private scoped instance countable_principalSubgroup : Countable (AdeleRing.principalSubgroup (𝓞 K) K) := by
  refine Function.Surjective.countable (f := fun k : K =>
    (⟨algebraMap K (AdeleRing (𝓞 K) K) k, RingHom.mem_range.2 ⟨k, rfl⟩⟩ : AdeleRing.principalSubgroup (𝓞 K) K)) ?_
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := RingHom.mem_range.1 hx
  exact ⟨k, rfl⟩

private theorem isAddFundamentalDomain_image_adelicBox :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 K) K) (adeleActEquiv D τ '' adelicBox K)
      (adelicAddHaar (𝓞 K) K) := by
  have hbox := isAddFundamentalDomain_adelicBox K (Measure.map (adeleActEquiv D τ).symm (adelicAddHaar (𝓞 K) K))
  have hsymm : Measure.QuasiMeasurePreserving (adeleActEquiv D τ).toEquiv.symm (adelicAddHaar (𝓞 K) K)
      (Measure.map (adeleActEquiv D τ).symm (adelicAddHaar (𝓞 K) K)) :=
    (⟨(adeleActEquiv D τ).symm.measurable, rfl⟩ : MeasurePreserving (adeleActEquiv D τ).symm (adelicAddHaar (𝓞 K) K)
      (Measure.map (adeleActEquiv D τ).symm (adelicAddHaar (𝓞 K) K))).quasiMeasurePreserving
  refine hbox.image_of_equiv (adeleActEquiv D τ).toEquiv hsymm (principalEquiv D τ) fun k x => ?_
  show D.act τ (D.act τ⁻¹ k + x) = (k : AdeleRing (𝓞 K) K) + D.act τ x
  rw [map_add, act_act_inv]

private theorem sigmaAdelicAct_unipotentGL2 (q : AdeleRing (𝓞 K) K) :
    sigmaAdelicAct F K D τ (unipotentGL2 q) = unipotentGL2 (D.act τ q) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change D.act τ ((unipotentGL2 q : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)
    = (unipotentGL2 (D.act τ q) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem constantTermIntegrand_vadd {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {u : AdelicGL2 (𝓞 K) K → ℂ} (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (g : AdelicGL2 (𝓞 K) K)
    (k : AdeleRing.principalSubgroup (𝓞 K) K) (q : AdeleRing (𝓞 K) K) :
    constantTermIntegrand unipotentGL2 u g (k +ᵥ q) = constantTermIntegrand unipotentGL2 u g q := by
  obtain ⟨k₀, hk₀⟩ := RingHom.mem_range.1 k.2
  show u (unipotentGL2 ((k : AdeleRing (𝓞 K) K) + q) * g) = u (unipotentGL2 q * g)
  rw [unipotentGL2_add, mul_assoc, ← hk₀, ← globalPoints_unipotentGL2, hl.left_invariant]

private theorem constantTermIntegrand_sigmaSectionActOn (u : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) :
    constantTermIntegrand unipotentGL2 (sigmaSectionActOn F K D τ u) g =
      fun q => constantTermIntegrand unipotentGL2 u (sigmaAdelicAct F K D τ g) (adeleActEquiv D τ q) := by
  funext q
  show u (sigmaAdelicAct F K D τ (unipotentGL2 q * g)) = u (unipotentGL2 (D.act τ q) * sigmaAdelicAct F K D τ g)
  rw [map_mul, sigmaAdelicAct_unipotentGL2]

private theorem map_actEquiv_cond {c : ENNReal}
    (hc : Measure.map (adeleActEquiv D τ) (adelicAddHaar (𝓞 K) K) = c • adelicAddHaar (𝓞 K) K) :
    Measure.map (adeleActEquiv D τ) (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) =
      (adelicAddHaar (𝓞 K) K (adelicBox K))⁻¹ •
        (c • (adelicAddHaar (𝓞 K) K).restrict (adeleActEquiv D τ '' adelicBox K)) := by
  unfold ProbabilityTheory.cond
  rw [Measure.map_smul]
  congr 1
  have himage : adeleActEquiv D τ ⁻¹' (adeleActEquiv D τ '' adelicBox K) = adelicBox K :=
    (adeleActEquiv D τ).injective.preimage_image _
  conv_lhs => rw [← himage]
  rw [← (adeleActEquiv D τ).measurableEmbedding.restrict_map, hc, Measure.restrict_smul]

private theorem isCuspidalFn_sigmaSectionActOn
    {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {u : AdelicGL2 (𝓞 K) K → ℂ}
    (hl : IsLsXiFunction (𝓞 K) K ⊤ ξ u)
    (hu : IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2 u) :
    IsCuspidalFn (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) unipotentGL2
      (sigmaSectionActOn F K D τ u) := by
  intro g
  obtain ⟨c, hc⟩ := exists_map_actEquiv_eq_smul D τ
  have hfd : ∫ q in adeleActEquiv D τ '' adelicBox K, constantTermIntegrand unipotentGL2 u (sigmaAdelicAct F K D τ g) q
        ∂(adelicAddHaar (𝓞 K) K) =
      ∫ q in adelicBox K, constantTermIntegrand unipotentGL2 u (sigmaAdelicAct F K D τ g) q ∂(adelicAddHaar (𝓞 K) K) :=
    (isAddFundamentalDomain_image_adelicBox D τ).setIntegral_eq (isAddFundamentalDomain_adelicBox_adelicAddHaar K)
      (constantTermIntegrand_vadd hl _)
  have hu' := hu (sigmaAdelicAct F K D τ g)
  unfold constantTerm at hu' ⊢
  unfold ProbabilityTheory.cond at hu'
  rw [integral_smul_measure] at hu'
  rw [constantTermIntegrand_sigmaSectionActOn]
  beta_reduce
  rw [← integral_map_equiv (adeleActEquiv D τ)
    (constantTermIntegrand unipotentGL2 u (sigmaAdelicAct F K D τ g)), map_actEquiv_cond D τ hc, integral_smul_measure,
    integral_smul_measure, hfd, smul_smul, mul_comm, ← smul_smul, hu', smul_zero]

end TwistCuspidal
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal"

section

namespace Pieces

open AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

private def pieceIn (q Vc : Submodule ℂ M) : Submodule ℂ q :=
  Vc.comap q.subtype

private theorem mem_pieceIn {q Vc : Submodule ℂ M} (w : q) : w ∈ pieceIn q Vc ↔ (w : M) ∈ Vc :=
  Iff.rfl

private noncomputable def pieceEquiv {q Vc : Submodule ℂ M} (h : Vc ≤ q) : pieceIn q Vc ≃ₗ[ℂ] Vc :=
  Submodule.comapSubtypeEquivOfLe h

private theorem coe_pieceEquiv_apply {q Vc : Submodule ℂ M} (h : Vc ≤ q) (w : pieceIn q Vc) :
    ((pieceEquiv h w : Vc) : M) = ((w : q) : M) :=
  rfl

private theorem coe_coe_pieceEquiv_symm_apply {q Vc : Submodule ℂ M} (h : Vc ≤ q) (v : Vc) :
    ((((pieceEquiv h).symm v : pieceIn q Vc) : q) : M) = (v : M) :=
  rfl

private theorem finiteDimensional_pieceIn {q Vc : Submodule ℂ M} (h : Vc ≤ q)
    [FiniteDimensional ℂ Vc] : FiniteDimensional ℂ (pieceIn q Vc) :=
  LinearEquiv.finiteDimensional (pieceEquiv h).symm

private noncomputable def pieceEnd {q Vc : Submodule ℂ M} (h : Vc ≤ q) {T : M → M}
    (hT : IsStableLinearOn Vc T) : pieceIn q Vc →ₗ[ℂ] pieceIn q Vc :=
  (pieceEquiv h).symm.conj hT.toEnd

private theorem trace_pieceEnd {q Vc : Submodule ℂ M} (h : Vc ≤ q) {T : M → M}
    (hT : IsStableLinearOn Vc T) :
    LinearMap.trace ℂ (pieceIn q Vc) (pieceEnd h hT) = traceOn Vc T hT := by
  rw [traceOn_eq, pieceEnd]
  exact LinearMap.trace_conj' _ _

private theorem coe_coe_pieceEnd_apply {q Vc : Submodule ℂ M} (h : Vc ≤ q) {T : M → M}
    (hT : IsStableLinearOn Vc T) (w : pieceIn q Vc) :
    (((pieceEnd h hT w : pieceIn q Vc) : q) : M) = T ((w : q) : M) :=
  rfl

end Pieces
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.TateGlobal NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ProbabilityTheory ComplexConjugate Pointwise

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

namespace FamilyHS

open FamilyBounds

universe v

variable {K : Type} [Field K] [NumberField K]

private theorem eLpNorm_toReal_sq {ν : Measure (AdelicGL2 (𝓞 K) K)} {w : AdelicGL2 (𝓞 K) K → ℂ}
    (hw : MemLp w 2 ν) : (eLpNorm w 2 ν).toReal ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂ν := by
  have hI : 0 ≤ ∫ x, ‖w x‖ ^ 2 ∂ν := integral_nonneg fun x => by positivity
  rw [hw.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat]
  simp only [Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hI _), ← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

private theorem integrable_normSq_mul_wt (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ Venue.slab K α β) (w : AdelicGL2 (𝓞 K) K → ℂ) (hw : MemLp w 2 ((Venue.μ K).restrict Φ₀)) :
    Integrable (fun x => ‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((Venue.μ K).restrict Φ₀) := by
  have hsq : Integrable (fun x => ‖w x‖ ^ 2) ((Venue.μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm hw.1).1 hw
  have hmeas : AEStronglyMeasurable (fun x => ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((Venue.μ K).restrict Φ₀) :=
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').aestronglyMeasurable
  have hbd : ∀ᵐ x ∂((Venue.μ K).restrict Φ₀),
      ‖ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
    filter_upwards [Venue.ae_mem_slab α β Φ₀ hΦ₀] with x hx
    rw [Real.norm_of_nonneg (Venue.wt_pos σ x).le]
    exact (Venue.wt_bounds α β σ hα x hx).2
  exact (hsq.bdd_mul hmeas hbd).congr (Filter.Eventually.of_forall fun x => mul_comm _ _)

private theorem integral_normSq_twist_le (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ Venue.slab K α β) (w : AdelicGL2 (𝓞 K) K → ℂ) (hw : MemLp w 2 ((Venue.μ K).restrict Φ₀)) :
    ∫ x in Φ₀, ‖WeightTwist.twist σ w x‖ ^ 2 ∂(Venue.μ K) ≤
      max (α ^ (-σ)) (β ^ (-σ)) *
        ∫ x in Φ₀, ‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(Venue.μ K) := by
  calc ∫ x in Φ₀, ‖WeightTwist.twist σ w x‖ ^ 2 ∂(Venue.μ K)
      ≤ ∫ x in Φ₀, max (α ^ (-σ)) (β ^ (-σ)) *
          (‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)) ∂(Venue.μ K) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_)
          ((integrable_normSq_mul_wt α β σ hα Φ₀ hΦ₀ w hw).const_mul _) ?_
        · show (0 : ℝ) ≤ ‖WeightTwist.twist σ w x‖ ^ 2
          positivity
        filter_upwards [Venue.ae_mem_slab α β Φ₀ hΦ₀] with x hx
        have hr0 := (Venue.wt_pos σ x).le
        have hr := (Venue.wt_bounds α β σ hα x hx).2
        have hwt : ‖WeightTwist.wt K σ x‖ = ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) := by
          show ‖((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)‖ = _
          rw [Complex.norm_real, Real.norm_of_nonneg hr0]
        show ‖w x * WeightTwist.wt K σ x‖ ^ 2 ≤
          max (α ^ (-σ)) (β ^ (-σ)) * (‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
        rw [norm_mul, mul_pow, hwt]
        calc ‖w x‖ ^ 2 * (ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)) ^ 2
            = ‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) *
                ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) := by ring
          _ ≤ ‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) * max (α ^ (-σ)) (β ^ (-σ)) := by gcongr
          _ = max (α ^ (-σ)) (β ^ (-σ)) *
                (‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)) := mul_comm _ _
    _ = max (α ^ (-σ)) (β ^ (-σ)) *
        ∫ x in Φ₀, ‖w x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(Venue.μ K) :=
      integral_const_mul _ _

variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ Venue.slab K α β}
  {hFD : IsFundamentalDomain (Venue.Γ K) Φ₀ ((Venue.μ K).restrict (Venue.slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

private theorem pointwise_twist (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hhf : IsFactorizableTestFn K h) (hh : Continuous h) (hhc : HasCompactSupport h)
    (F : Type) [Field F] [Algebra F K] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) F K) (τ : K ≃ₐ[F] K)
    (hξ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ξ ⟨Venue.actUnits F D τ z, Subgroup.mem_top _⟩ = ξ z) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ w : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ, Venue.fn w ∈ Wf →
      ∀ d ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        ‖Venue.fn (Venue.convOp h hh hhc (Venue.tw F D τ hξ w)) d‖ ≤ Cp * ‖w‖ := by
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain K ξ h hhf
      c u d₁ d₂ T hc hd₁ α β (hα.trans hαβ) hαβ Φ₀ hFD
  have hmin : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
    lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)
  refine ⟨max C 0 * √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹, by positivity, fun w hw d hd => ?_⟩
  have hψ_L2 := Venue.memLp_fn (Venue.tw F D τ hξ w)
  have hcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 (Venue.fn (Venue.tw F D τ hξ w)) := by
    rw [Venue.tw_apply]
    exact TwistCuspidal.isCuspidalFn_sigmaSectionActOn D τ (hWf _ hw).1 (hWf _ hw).2
  have h1 := hC _ (Venue.isLsXiFunction_fn _) hcusp (Venue.continuous_fn _) hψ_L2 d hd
  have h2 : (eLpNorm (Venue.fn (Venue.tw F D τ hξ w)) 2 ((Venue.μ K).restrict Φ₀)).toReal ^ 2 ≤
      (min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖Venue.tw F D τ hξ w‖ ^ 2 := by
    rw [eLpNorm_toReal_sq hψ_L2, Venue.norm_sq_eq]
    exact WeightTwist.integral_normSq_le_inv_min_mul σ α β hα hαβ.le Φ₀ (Venue.ae_mem_slab α β Φ₀ hΦ₀) _
      ((memLp_two_iff_integrable_sq_norm hψ_L2.1).1 hψ_L2) (integrable_normSq_mul_wt α β σ hα Φ₀ hΦ₀ _ hψ_L2)
  have h3 : (eLpNorm (Venue.fn (Venue.tw F D τ hξ w)) 2 ((Venue.μ K).restrict Φ₀)).toReal ≤
      √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖ := by
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul (inv_nonneg.2 hmin.le), Real.sqrt_sq (norm_nonneg _),
      Venue.norm_tw] at h4
  rw [Venue.fn_convOp]
  calc ‖rightConv K (Venue.fn (Venue.tw F D τ hξ w)) h d‖
      ≤ C * (eLpNorm (Venue.fn (Venue.tw F D τ hξ w)) 2 ((Venue.μ K).restrict Φ₀)).toReal := h1
    _ ≤ max C 0 * (eLpNorm (Venue.fn (Venue.tw F D τ hξ w)) 2 ((Venue.μ K).restrict Φ₀)).toReal := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (√(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖) := by gcongr
    _ = max C 0 * √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖ := (mul_assoc _ _ _).symm

private theorem pointwise_flat (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (g : AdelicGL2 (𝓞 K) K → ℂ) (hgf : IsFactorizableTestFn K g) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ w : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ, Venue.fn w ∈ Wf →
      ∀ d ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        ‖Venue.fn (Venue.convOpFlat g hg hgc w) d‖ ≤ Cp * ‖w‖ := by
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain K
      (WeightTwist.twistChar ξ σ) (fun y => conj (g y⁻¹)) (FlatTestFn.isFactorizableTestFn_conj_comp_inv K hgf)
      c u d₁ d₂ T hc hd₁ α β (hα.trans hαβ) hαβ Φ₀ hFD
  obtain ⟨W, hW⟩ := WeightTwist.exists_forall_mem_window_wt_le (-σ) c u d₁ d₂ hd₁ T
  simp only [neg_neg] at hW
  have hmax : 0 < max (α ^ (-σ)) (β ^ (-σ)) := lt_max_of_lt_left (Real.rpow_pos_of_pos hα _)
  refine ⟨max W 0 * max C 0 * √(max (α ^ (-σ)) (β ^ (-σ))), by positivity, fun w hw d hd => ?_⟩
  have htw_L2 : MemLp (WeightTwist.twist σ (Venue.fn w)) 2 ((Venue.μ K).restrict Φ₀) :=
    WeightTwist.memLp_twist α β σ hα Φ₀ hΦ₀ (Venue.memLp_fn w)
  have h1 := hC _ (WeightTwist.isLsXiFunction_twist σ ξ (Venue.isLsXiFunction_fn w))
    (WeightTwist.isCuspidalFn_twist σ _ (hWf _ hw).2) (WeightTwist.continuous_twist σ (Venue.continuous_fn w))
    htw_L2 d hd
  have h2 : (eLpNorm (WeightTwist.twist σ (Venue.fn w)) 2 ((Venue.μ K).restrict Φ₀)).toReal ^ 2 ≤
      max (α ^ (-σ)) (β ^ (-σ)) * ‖w‖ ^ 2 := by
    rw [eLpNorm_toReal_sq htw_L2, Venue.norm_sq_eq]
    exact integral_normSq_twist_le α β σ hα Φ₀ hΦ₀ _ (Venue.memLp_fn w)
  have h3 : (eLpNorm (WeightTwist.twist σ (Venue.fn w)) 2 ((Venue.μ K).restrict Φ₀)).toReal ≤
      √(max (α ^ (-σ)) (β ^ (-σ))) * ‖w‖ := by
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul hmax.le, Real.sqrt_sq (norm_nonneg _)] at h4
  have hd0 : 0 ≤ ideleNorm K (Matrix.GeneralLinearGroup.det d) ^ σ := (Real.rpow_pos_of_pos (ideleNorm_pos _) _).le
  show ‖rightConv K (Venue.fn w) (WeightTwist.flat σ g) d‖ ≤ _
  rw [WeightTwist.rightConv_flat, norm_mul, Complex.norm_real, Real.norm_of_nonneg hd0]
  calc ideleNorm K (Matrix.GeneralLinearGroup.det d) ^ σ *
        ‖rightConv K (WeightTwist.twist σ (Venue.fn w)) (fun y => conj (g y⁻¹)) d‖
      ≤ max W 0 * (max C 0 * (√(max (α ^ (-σ)) (β ^ (-σ))) * ‖w‖)) := by
        refine mul_le_mul ((hW d hd).trans (le_max_left _ _)) (h1.trans ?_) (norm_nonneg _) (by positivity)
        exact mul_le_mul (le_max_left _ _) h3 ENNReal.toReal_nonneg (by positivity)
    _ = max W 0 * max C 0 * √(max (α ^ (-σ)) (β ^ (-σ))) * ‖w‖ := by ring

private theorem family_sum_le (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (c u d₁ d₂ : ℝ)
    (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Op : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (Cp : ℝ)
    (hpt : ∀ w : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ, Venue.fn w ∈ Wf →
      ∀ d ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, ‖Venue.fn (Op w) d‖ ≤ Cp * ‖w‖) :
    ∃ A : ℝ, ∀ (J : Type v) [Fintype J] (e : J → Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ), Orthonormal ℂ e →
      (∀ j, Venue.fn (e j) ∈ Wf) → ∑ j, ‖Op (e j)‖ ^ 2 ≤ A := by
  obtain ⟨W', hW'⟩ := WeightTwist.exists_forall_mem_window_wt_le σ c u d₁ d₂ hd₁ T
  have hvol : Venue.μ K Φ₀ < ⊤ :=
    SlabSquareIntegrable.measure_fd_lt_top c u d₁ d₂ T hc hd₁ hd hcov α β hα Φ₀ hΦ₀ hFD
  haveI : IsFiniteMeasure ((Venue.μ K).restrict Φ₀) := ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
  refine ⟨Cp ^ 2 * W' * (Venue.μ K).real Φ₀, fun J _ e he hmem => ?_⟩
  have hnorm : ∀ j, ‖Op (e j)‖ ^ 2 =
      ∫ x in Φ₀, ‖Venue.fn (Op (e j)) x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(Venue.μ K) :=
    fun j => Venue.norm_sq_eq _
  simp only [hnorm]
  refine sum_integral_le_of_forall_le (Venue.μ K) Φ₀ (fun j => Venue.fn (Op (e j)))
    (fun x => ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
    (fun j => integrable_normSq_mul_wt α β σ hα Φ₀ hΦ₀ _ (Venue.memLp_fn _)) fun x => ?_
  refine sum_norm_sq_mul_le_of_moves (fun j => Venue.fn (Op (e j)))
    (fun x => ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
    (fun m : Matrix.GeneralLinearGroup (Fin 2) K × (AdeleRing (𝓞 K) K)ˣ =>
      fun y => globalPoints (𝓞 K) K m.1 * y * centralScalar (𝓞 K) K m.2)
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) ?_ ?_ ?_ hW'
    (fun y => (Venue.wt_pos σ y).le) (by positivity) x
  · intro j m y
    exact WeightTwist.normSq_mul_wt_transport σ ξ hσ (Venue.isLsXiFunction_fn (Op (e j))) m.1 m.2 y
  · intro y
    obtain ⟨γ, z, hm⟩ := hcov y
    exact ⟨(γ, z), hm⟩
  · intro d hd
    have hL := sum_norm_sq_apply_le he ((LinearMap.proj d ∘ₗ (Venue.ven ξ Φ₀).subtype) ∘ₗ Op) Cp fun l => ?_
    · exact hL
    · refine hpt _ ?_ d hd
      show (Venue.ven ξ Φ₀).subtype (∑ i, l i • e i) ∈ Wf
      rw [map_sum]
      exact Submodule.sum_mem _ fun i _ => by
        show l i • Venue.fn (e i) ∈ Wf
        exact Wf.smul_mem _ (hmem i)

private theorem hB_of_family (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    {ι : Type*} (V : ι → Submodule ℂ (Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)) (hV : ∀ i, ∀ w ∈ V i, Venue.fn w ∈ Wf)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hhf : IsFactorizableTestFn K h) (hh : Continuous h) (hhc : HasCompactSupport h)
    (F : Type) [Field F] [Algebra F K] (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) F K) (τ : K ≃ₐ[F] K)
    (hξ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ξ ⟨Venue.actUnits F D τ z, Subgroup.mem_top _⟩ = ξ z) :
    ∃ B : ℝ, ∀ (J : Type v) [Fintype J] (e : J → Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ),
      Orthonormal ℂ e → (∀ j, ∃ i, e j ∈ V i) →
      ∑ j, ‖(Venue.convOp h hh hhc ∘ₗ Venue.tw F D τ hξ) (e j)‖ ^ 2 ≤ B := by
  obtain ⟨Cp, -, hpt⟩ := pointwise_twist Wf hWf c u d₁ d₂ T hc hd₁ h hhf hh hhc F D τ hξ
  obtain ⟨B, hB⟩ := family_sum_le.{v} Wf c u d₁ d₂ T hc hd₁ hd hcov
    (Venue.convOp h hh hhc ∘ₗ Venue.tw F D τ hξ :
      Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) Cp hpt
  exact ⟨B, fun J _ e he hmem => hB J e he fun j => by
    obtain ⟨i, hi⟩ := hmem j
    exact hV i _ hi⟩

private theorem hA_of_family (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    {ι : Type*} (V : ι → Submodule ℂ (Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)) (hV : ∀ i, ∀ w ∈ V i, Venue.fn w ∈ Wf)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (g : AdelicGL2 (𝓞 K) K → ℂ) (hgf : IsFactorizableTestFn K g) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ A : ℝ, ∀ (J : Type v) [Fintype J] (e : J → Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ),
      Orthonormal ℂ e → (∀ j, ∃ i, e j ∈ V i) →
      ∑ j, ‖Venue.convOpFlat g hg hgc (e j)‖ ^ 2 ≤ A := by
  obtain ⟨Cp, -, hpt⟩ := pointwise_flat Wf hWf c u d₁ d₂ T hc hd₁ g hgf hg hgc
  obtain ⟨A, hA⟩ := family_sum_le.{v} Wf c u d₁ d₂ T hc hd₁ hd hcov
    (Venue.convOpFlat g hg hgc :
      Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) Cp hpt
  exact ⟨A, fun J _ e he hmem => hA J e he fun j => by
    obtain ⟨i, hi⟩ := hmem j
    exact hV i _ hi⟩

private theorem pointwise_plain (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hhf : IsFactorizableTestFn K h) (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ w : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ, Venue.fn w ∈ Wf →
      ∀ d ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        ‖Venue.fn (Venue.convOp h hh hhc w) d‖ ≤ Cp * ‖w‖ := by
  obtain ⟨C, hC⟩ :=
    exists_forall_norm_rightConv_le_mul_eLpNorm_of_isLsXiFunction_of_isCuspidalFn_of_isFundamentalDomain K ξ h hhf
      c u d₁ d₂ T hc hd₁ α β (hα.trans hαβ) hαβ Φ₀ hFD
  have hmin : 0 < min (α ^ (-σ)) (β ^ (-σ)) :=
    lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)
  refine ⟨max C 0 * √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹, by positivity, fun w hw d hd => ?_⟩
  have hψ_L2 := Venue.memLp_fn w
  have hcusp : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 (Venue.fn w) := (hWf _ hw).2
  have h1 := hC _ (Venue.isLsXiFunction_fn _) hcusp (Venue.continuous_fn _) hψ_L2 d hd
  have h2 : (eLpNorm (Venue.fn w) 2 ((Venue.μ K).restrict Φ₀)).toReal ^ 2 ≤
      (min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖ ^ 2 := by
    rw [eLpNorm_toReal_sq hψ_L2, Venue.norm_sq_eq]
    exact WeightTwist.integral_normSq_le_inv_min_mul σ α β hα hαβ.le Φ₀ (Venue.ae_mem_slab α β Φ₀ hΦ₀) _
      ((memLp_two_iff_integrable_sq_norm hψ_L2.1).1 hψ_L2) (integrable_normSq_mul_wt α β σ hα Φ₀ hΦ₀ _ hψ_L2)
  have h3 : (eLpNorm (Venue.fn w) 2 ((Venue.μ K).restrict Φ₀)).toReal ≤
      √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖ := by
    have h4 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_mul (inv_nonneg.2 hmin.le), Real.sqrt_sq (norm_nonneg _)] at h4
  rw [Venue.fn_convOp]
  calc ‖rightConv K (Venue.fn w) h d‖
      ≤ C * (eLpNorm (Venue.fn w) 2 ((Venue.μ K).restrict Φ₀)).toReal := h1
    _ ≤ max C 0 * (eLpNorm (Venue.fn w) 2 ((Venue.μ K).restrict Φ₀)).toReal := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C 0 * (√(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖) := by gcongr
    _ = max C 0 * √(min (α ^ (-σ)) (β ^ (-σ)))⁻¹ * ‖w‖ := (mul_assoc _ _ _).symm

private theorem hB_plain_of_family (Wf : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hWf : ∀ φ ∈ Wf,
      IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ)
    {ι : Type*} (V : ι → Submodule ℂ (Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)) (hV : ∀ i, ∀ w ∈ V i, Venue.fn w ∈ Wf)
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (h : AdelicGL2 (𝓞 K) K → ℂ) (hhf : IsFactorizableTestFn K h) (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∃ B : ℝ, ∀ (J : Type v) [Fintype J] (e : J → Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ),
      Orthonormal ℂ e → (∀ j, ∃ i, e j ∈ V i) →
      ∑ j, ‖(Venue.convOp h hh hhc) (e j)‖ ^ 2 ≤ B := by
  obtain ⟨Cp, -, hpt⟩ := pointwise_plain Wf hWf c u d₁ d₂ T hc hd₁ h hhf hh hhc
  obtain ⟨B, hB⟩ := family_sum_le.{v} Wf c u d₁ d₂ T hc hd₁ hd hcov
    (Venue.convOp h hh hhc :
      Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) Cp hpt
  exact ⟨B, fun J _ e he hmem => hB J e he fun j => by
    obtain ⟨i, hi⟩ := hmem j
    exact hV i _ hi⟩

end FamilyHS
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

namespace ClassOrthogonality

open IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]
variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ Venue.slab K α β}
  {hFD : IsFundamentalDomain (Venue.Γ K) Φ₀ ((Venue.μ K).restrict (Venue.slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}
variable (W : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
  (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K)))

private theorem rawb_eq {Φ : HeckeEigensystem K ℂ}
    (hΦ : Φ ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    Φ.toRawCentral.b v = ((ξ ⟨Matrix.GeneralLinearGroup.det (gen v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by
  obtain ⟨φ, hφ, hφ0⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hΦ
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hφ0
  have hg' : φ g ≠ 0 := hg
  have hl := (WindowForms.mem_windowForms_iff.1 (WindowForms.IsIsotypicCuspFormAt.mem_windowForms hφ)).2.1
  have e1 := hφ.central_eigen v hv g
  have e2 := hl.central_transform ⟨Matrix.GeneralLinearGroup.det (gen v), Subgroup.mem_top _⟩ g
  exact mul_right_cancel₀ hg' (e1.symm.trans e2)

private theorem b_eq {Φ Φ' : HeckeEigensystem K ℂ}
    (hΦ : Φ ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (hΦ' : Φ' ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) : Φ.b v = Φ'.b v := by
  have h1 := rawb_eq W U gen N S hΦ v hv
  have h2 := rawb_eq W U gen N S hΦ' v hv
  rw [HeckeEigensystem.toRawCentral_b] at h1 h2
  exact mul_left_cancel₀ (inv_ne_zero (HeckeEigensystem.cNorm_ne_zero v)) (h1.trans h2.symm)

private theorem exists_a_ne {Φ Φ' : HeckeEigensystem K ℂ}
    (hΦ : Φ ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (hΦ' : Φ' ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (hne : Φ ≠ Φ') : ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ Φ.a v ≠ Φ'.a v := by
  by_contra hcon
  exact hne (eq_of_mem_cuspClasses hΦ hΦ' fun v hv =>
    ⟨Classical.byContradiction fun h => hcon ⟨v, hv, h⟩, b_eq W U gen N S hΦ hΦ' v hv⟩)

private theorem invariant_and_eigen_of_mem {Φ : HeckeEigensystem K ℂ} (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S)
    {reps₀ : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 K) K}
    (hsys₀ : HeckeIntegralSeam.IsHeckeCosetSystem (U N) (gen v) reps₀) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ) :
    (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, φ (g * u) = φ g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K, ∑ i, φ (g * reps₀ i) = Φ.a v * φ g := by
  have hφ' : φ ∈
      Submodule.span ℂ {ψ | IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ ψ} := hφ
  clear hφ
  induction hφ' using Submodule.span_induction with
  | mem x hx =>
    have hx' : IsIsotypicCuspFormAt K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ x := hx
    have hxU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U N, x (g * u) = x g := fun g u hu => hx'.level_invariant g u hu
    refine ⟨hxU, fun g => ?_⟩
    obtain ⟨reps, hsys, heig⟩ := hx'.hecke_eigen v hv
    rw [Venue.cosetSum_eq_of_isHeckeCosetSystem hsys₀ hsys x hxU g]
    exact heig g
  | zero => exact ⟨fun _ _ _ => rfl, fun g => by simp⟩
  | add x y _ _ hx hy =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.add_apply, hx.1 g u hu, hy.1 g u hu]
    · simp only [Pi.add_apply, Finset.sum_add_distrib, hx.2 g, hy.2 g, mul_add]
  | smul c x _ hx =>
    refine ⟨fun g u hu => ?_, fun g => ?_⟩
    · simp only [Pi.smul_apply, hx.1 g u hu]
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hx.2 g]
      ring

private theorem inner_eq_zero_of_ne_cuspClass
    (hstd : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ S →
      ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K), u₁ ∈ U N ∧ u₂ ∈ U N ∧
        (gen w)⁻¹ = centralScalar (𝓞 K) K z * u₁ * gen w * u₂)
    {Φ Φ' : HeckeEigensystem K ℂ}
    (hΦ : Φ ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S)
    (hΦ' : Φ' ∈ cuspClasses K (productionPinsOf K W U gen (adelicBox K)) ξ N S) (hne : Φ ≠ Φ')
    (φ ψ : Venue.Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ)
    (hφ : Venue.fn φ ∈ isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ)
    (hψ : Venue.fn ψ ∈ isotypicCuspSubmodule K (productionPinsOf K W U gen (adelicBox K)) ξ N S Φ') :
    @inner ℂ _ _ φ ψ = 0 := by
  by_cases hφ0 : φ = 0
  · rw [hφ0, inner_zero_left]
  obtain ⟨v, hv, hav⟩ := exists_a_ne W U gen N S hΦ hΦ' hne
  obtain ⟨φ₀, hφ₀, -⟩ := exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses hΦ
  obtain ⟨reps₀, hsys, -⟩ := hφ₀.hecke_eigen v hv
  have hsys₀ : HeckeIntegralSeam.IsHeckeCosetSystem (U N) (gen v) reps₀ := hsys
  obtain ⟨hφU, hφeig⟩ := invariant_and_eigen_of_mem W U gen N S v hv hsys₀ hφ
  obtain ⟨hψU, hψeig⟩ := invariant_and_eigen_of_mem W U gen N S v hv hsys₀ hψ
  obtain ⟨z, u₁, u₂, hu₁, hu₂, e⟩ := hstd v hv
  refine Venue.inner_eq_zero_of_isHeckeCosetEigenfunctionAt (U N)
    (fun u hu => Venue.normDet_pow_eq_one_of_invariant (U N) φ hφ0 hφU u hu) (gen v) ⟨z, Subgroup.mem_top z⟩
    ⟨u₁, hu₁, u₂, hu₂, ?_⟩ v ψ φ hψU hφU (Φ'.a v) (Φ.a v) ⟨reps₀, hsys₀, hψeig⟩ ⟨reps₀, hsys₀, hφeig⟩ hav.symm
  show (gen v)⁻¹ = centralScalar (𝓞 K) K z * (u₁ * gen v * u₂)
  rw [e]
  simp only [mul_assoc]

end ClassOrthogonality
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

section

open scoped InnerProductSpace ComplexConjugate

namespace Abstract

universe u

private theorem summable_norm_trace_of_orthogonal_of_adjoint_bounds
    {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    {ι : Type u} (V : ι → Submodule ℂ E) [∀ i, FiniteDimensional ℂ (V i)]
    (hV : ∀ i j, i ≠ j → ∀ u ∈ V i, ∀ v ∈ V j, ⟪u, v⟫_ℂ = 0)
    (Ti : ∀ i, V i →ₗ[ℂ] V i)
    {κ : Type*} (s : Finset κ) (A : κ → E' →ₗ[ℂ] E) (Adag : κ → E →ₗ[ℂ] E')
    (B : κ → E →ₗ[ℂ] E')
    (hTi : ∀ i (w : V i), ((Ti i w : V i) : E) = ∑ k ∈ s, A k (B k (w : E)))
    (hadj : ∀ k (w : E') i, ∀ v ∈ V i, ⟪A k w, v⟫_ℂ = ⟪w, Adag k v⟫_ℂ)
    (α β : κ → ℝ)
    (hA : ∀ k (J : Type u) [Fintype J] (e : J → E), Orthonormal ℂ e →
      (∀ j, ∃ i, e j ∈ V i) → ∑ j, ‖Adag k (e j)‖ ^ 2 ≤ α k)
    (hB : ∀ k (J : Type u) [Fintype J] (e : J → E), Orthonormal ℂ e →
      (∀ j, ∃ i, e j ∈ V i) → ∑ j, ‖B k (e j)‖ ^ 2 ≤ β k) :
    Summable (fun i => ‖LinearMap.trace ℂ (V i) (Ti i)‖) ∧
      ∑' i, ‖LinearMap.trace ℂ (V i) (Ti i)‖ ≤ ∑ k ∈ s, √(α k) * √(β k) := by
  classical
  let b : ∀ i : ι, OrthonormalBasis (Fin (Module.finrank ℂ (V i))) ℂ (V i) :=
    fun i => stdOrthonormalBasis ℂ (V i)
  have key : ∀ t : Finset ι,
      ∑ i ∈ t, ‖LinearMap.trace ℂ (V i) (Ti i)‖ ≤ ∑ k ∈ s, √(α k) * √(β k) := by
    intro t
    let J := Σ i : t, Fin (Module.finrank ℂ (V (i : ι)))
    obtain ⟨e, he⟩ : ∃ e : J → E, ∀ p, e p = ((b (p.1 : ι) p.2 : V (p.1 : ι)) : E) :=
      ⟨_, fun _ => rfl⟩
    have horth : Orthonormal ℂ e := by
      rw [orthonormal_iff_ite]
      rintro ⟨i, m⟩ ⟨i', m'⟩
      rw [he, he]
      by_cases hii : i = i'
      · subst hii
        rw [← Submodule.coe_inner, orthonormal_iff_ite.mp (b (i : ι)).orthonormal m m']
        by_cases hmm : m = m'
        · subst hmm
          simp
        · rw [if_neg hmm, if_neg (show ¬((⟨i, m⟩ : J) = ⟨i, m'⟩) from
            fun h => hmm (eq_of_heq (Sigma.mk.inj h).2))]
      · have hne : (i : ι) ≠ (i' : ι) := fun h => hii (Subtype.ext h)
        rw [hV _ _ hne _ (b (i : ι) m).2 _ (b (i' : ι) m').2,
          if_neg (show ¬((⟨i, m⟩ : J) = ⟨i', m'⟩) from fun h => hii (Sigma.mk.inj h).1)]
    have hmem : ∀ p : J, ∃ i, e p ∈ V i := fun p => ⟨p.1, by rw [he]; exact (b (p.1 : ι) p.2).2⟩
    have per : ∀ i : t, ‖LinearMap.trace ℂ (V (i : ι)) (Ti i)‖ ≤
        ∑ k ∈ s, ∑ m, ‖Adag k (e ⟨i, m⟩)‖ * ‖B k (e ⟨i, m⟩)‖ := by
      intro i
      rw [(Ti (i : ι)).trace_eq_sum_inner (b (i : ι))]
      refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)).trans_eq Finset.sum_comm
      rw [Submodule.coe_inner, hTi (i : ι) (b (i : ι) m), inner_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [he, ← inner_conj_symm, hadj k _ (i : ι) _ (b (i : ι) m).2, inner_conj_symm]
      exact norm_inner_le_norm _ _
    calc ∑ i ∈ t, ‖LinearMap.trace ℂ (V i) (Ti i)‖
        = ∑ i : t, ‖LinearMap.trace ℂ (V (i : ι)) (Ti i)‖ := (Finset.sum_coe_sort t _).symm
      _ ≤ ∑ i : t, ∑ k ∈ s, ∑ m, ‖Adag k (e ⟨i, m⟩)‖ * ‖B k (e ⟨i, m⟩)‖ :=
          Finset.sum_le_sum fun i _ => per i
      _ = ∑ k ∈ s, ∑ p : J, ‖Adag k (e p)‖ * ‖B k (e p)‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ =>
            (Fintype.sum_sigma fun p : J => ‖Adag k (e p)‖ * ‖B k (e p)‖).symm
      _ ≤ ∑ k ∈ s, √(α k) * √(β k) := Finset.sum_le_sum fun k _ =>
          (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans
            (mul_le_mul (Real.sqrt_le_sqrt (hA k J e horth hmem))
              (Real.sqrt_le_sqrt (hB k J e horth hmem)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hnn : 0 ≤ fun i => ‖LinearMap.trace ℂ (V i) (Ti i)‖ := fun i => norm_nonneg _
  exact ⟨summable_of_sum_le hnn key, Real.tsum_le_of_sum_le hnn key⟩

end Abstract
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

section

namespace TraceZero

private theorem trace_eq_zero_of_not_finite {V : Type*} [AddCommGroup V] [Module ℂ V]
    (h : ¬ Module.Finite ℂ V) (T : V →ₗ[ℂ] V) : LinearMap.trace ℂ V T = 0 := by
  have hne : ¬ ∃ s : Finset V, Nonempty (Module.Basis s ℂ V) := by
    rintro ⟨s, ⟨b⟩⟩
    exact h (Module.Finite.of_basis b)
  unfold LinearMap.trace
  rw [dif_neg hne, LinearMap.zero_apply]

end TraceZero
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces"

end WeightedVenueTrace
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

open WeightedVenueTrace.TraceZero in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (hstd : ∀ w : HeightOneSpectrum (𝓞 K), w ∉ SK →
      ∃ (z : (AdeleRing (𝓞 K) K)ˣ) (u₁ u₂ : AdelicGL2 (𝓞 K) K),
        u₁ ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K ∧
        u₂ ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K ∧
        (heckeGen (𝓞 K) K w)⁻¹ = centralScalar (𝓞 K) K z * u₁ * heckeGen (𝓞 K) K w * u₂)
    (tysK : ArchTypeFamily K) (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f)
    (S' : Finset (HeightOneSpectrum (𝓞 K))) (hS' : SK ⊆ S')
    (hft : IsUnitFactorizableOfTypeAt K tysK (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) S' f) :
    Summable (fun π : ↥(cuspClasses K
        (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) =>
      ‖cutTrace K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f hf hfc‖) := by
  classical
  have hft' : IsFactorizableTestFn K f := hft.isFactorizableTestFn

  let V : ↥(cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) →
      Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    fun π => isotypicCuspSubmodule K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π ⊓
      archCutSubmodule K tysK
  let P : ↥(cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) → Prop :=
    fun π => Module.Finite ℂ ↥(V π) ∧ ∀ v ∈ V π, convOp K f v ∈ V π
  refine (summable_subtype_and_compl (s := {π | P π})).1 ⟨?_, ?_⟩
  ·
    have hVW : ∀ π : ↥{π | P π}, V π ≤ WeightedVenueTrace.WindowForms.windowForms K ΦK ξK :=
      fun π => inf_le_left.trans
        ((AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab K cK uK d₁K d₂K TK
            hdK hcovK α β hα ΦK hΦKs hΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K) ξK N' SK _).trans
          (WeightedVenueTrace.WindowForms.isotypicCuspSubmodule_le_windowForms _ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) ξK N' SK _))
    by_cases hex : ∃ π : ↥{π | P π}, ∃ v ∈ V π, v ≠ 0
    swap
    ·
      push Not at hex
      have hz : (fun π : ↥{π | P π} =>
          ‖cutTrace K
            (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π
            tysK f hf hfc‖) = 0 := by
        funext π
        obtain ⟨-, hmaps⟩ := (π.2 : P π)
        rw [Pi.zero_apply, norm_eq_zero, cutTrace_eq, convTraceOn_eq_traceOn K _ hf hfc hmaps]
        exact traceOn_eq_zero_of_eq_bot _ ((Submodule.eq_bot_iff _).2 (hex π))
      rw [hz]
      exact summable_zero
    ·
      obtain ⟨π₀, v₀, hv₀, hne₀⟩ := hex
      have hv₀W := WeightedVenueTrace.WindowForms.mem_windowForms_iff.1 (hVW π₀ hv₀)
      have hne₀' : ∃ g, v₀ g ≠ 0 := by
        by_contra h
        push Not at h
        exact hne₀ (funext h)
      obtain ⟨hprin, hcontχ⟩ :=
        AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K ξK v₀
          hv₀W.2.1 hv₀W.1 hne₀'
      let μξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := ξK.comp Subgroup.topEquiv.symm.toMonoidHom
      obtain ⟨σ₀, hσ₀'⟩ :=
        NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow K μξ (fun u => hprin u) hcontχ
      have hσ₀ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
          ‖((ξK z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ₀ := fun z => hσ₀' z

      have hΦ' : ΦK ⊆ WeightedVenueTrace.Venue.slab K α β := hΦKs
      have hFD' : MeasureTheory.IsFundamentalDomain (WeightedVenueTrace.Venue.Γ K) ΦK
          ((WeightedVenueTrace.Venue.μ K).restrict (WeightedVenueTrace.Venue.slab K α β)) := hΦK
      have hVv : ∀ π : ↥{π | P π}, V π ≤ WeightedVenueTrace.Venue.ven ξK ΦK := fun π φ hφ => by
        have hw := WeightedVenueTrace.WindowForms.mem_windowForms_iff.1 (hVW π hφ)
        exact ⟨hw.1, hw.2.1, hw.2.2.1⟩
      let E : Type := WeightedVenueTrace.Venue.Ven α β ΦK ξK hα hαβ hΦ' hFD' σ₀ hσ₀
      let Vv : ↥{π | P π} → Submodule ℂ E := fun i =>
        WeightedVenueTrace.Pieces.pieceIn (WeightedVenueTrace.Venue.ven ξK ΦK) (V i)
      haveI hfdim : ∀ i, FiniteDimensional ℂ (Vv i) := fun i =>
        haveI : Module.Finite ℂ ↥(V i) := (i.2 : P i).1
        WeightedVenueTrace.Pieces.finiteDimensional_pieceIn (hVv i)
      have hst : ∀ i : ↥{π | P π}, IsStableLinearOn (V i) (convOp K f) := fun i =>
        isStableLinearOn_convOp K
          (fun v hv => (WeightedVenueTrace.WindowForms.mem_windowForms_iff.1 (hVW i hv)).1) hf hfc
          (i.2 : P i).2
      let Ti : ∀ i, Vv i →ₗ[ℂ] Vv i := fun i => WeightedVenueTrace.Pieces.pieceEnd (hVv i) (hst i)
      have hDM : ∃ n : ℕ, ∃ g h : Fin n → AdelicGL2 (𝓞 K) K → ℂ,
          (∀ k, IsFactorizableTestFn K (g k)) ∧ (∀ k, IsFactorizableTestFn K (h k)) ∧
            ∀ x, f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x :=
        exists_eq_sum_rightConv_of_isFactorizableTestFn K f hft'
      obtain ⟨n, g, h, hg, hh, hfsum⟩ := hDM
      have hgc : ∀ k, Continuous (g k) ∧ HasCompactSupport (g k) := fun k =>
        continuous_and_hasCompactSupport_of_isFactorizableTestFn K (g k) (hg k)
      have hhc : ∀ k, Continuous (h k) ∧ HasCompactSupport (h k) := fun k =>
        continuous_and_hasCompactSupport_of_isFactorizableTestFn K (h k) (hh k)
      let A : Fin n → E →ₗ[ℂ] E := fun k => WeightedVenueTrace.Venue.convOp (g k) (hgc k).1 (hgc k).2
      let Adag : Fin n → E →ₗ[ℂ] E := fun k =>
        WeightedVenueTrace.Venue.convOpFlat (g k) (hgc k).1 (hgc k).2
      let B : Fin n → E →ₗ[ℂ] E := fun k =>
        WeightedVenueTrace.Venue.convOp (h k) (hhc k).1 (hhc k).2
      have hTi : ∀ i (w : Vv i), ((Ti i w : Vv i) : E) = ∑ k ∈ Finset.univ, A k (B k (w : E)) := by
        intro i w
        apply WeightedVenueTrace.Venue.fn_injective
        have hL : WeightedVenueTrace.Venue.fn ((Ti i w : Vv i) : E) =
            rightConv K (WeightedVenueTrace.Venue.fn (w : E)) f :=
          WeightedVenueTrace.Pieces.coe_coe_pieceEnd_apply (hVv i) (hst i) w
        have hR : WeightedVenueTrace.Venue.fn (∑ k ∈ Finset.univ, A k (B k (w : E))) =
            ∑ k, rightConv K (rightConv K
              (WeightedVenueTrace.Venue.fn (w : E)) (h k)) (g k) := by
          show ((∑ k ∈ Finset.univ, A k (B k (w : E)) : ↥(WeightedVenueTrace.Venue.ven ξK ΦK)) :
            AdelicGL2 (𝓞 K) K → ℂ) = _
          rw [Submodule.coe_sum]
          exact Finset.sum_congr rfl fun k _ => rfl
        rw [hL, hR]
        exact WeightedVenueTrace.ConvolutionAssociativity.rightConv_eq_sum_of_forall_eq_sum _ f
          (WeightedVenueTrace.Venue.continuous_fn _) g h (fun k => (hgc k).1) (fun k => (hgc k).2)
          (fun k => (hhc k).1) (fun k => (hhc k).2) hfsum
      have hadj : ∀ k (w : E) i, ∀ v ∈ Vv i, @inner ℂ _ _ (A k w) v = @inner ℂ _ _ w (Adag k v) :=
        fun k w i v _ => WeightedVenueTrace.Venue.inner_convOp (g k) (hgc k).1 (hgc k).2 w v
      have hVorth : ∀ i j, i ≠ j → ∀ w ∈ Vv i, ∀ v ∈ Vv j, @inner ℂ _ _ w v = 0 :=
        fun i j hij w hw v hv =>
          WeightedVenueTrace.ClassOrthogonality.inner_eq_zero_of_ne_cuspClass _ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) N' SK hstd i.1.2 j.1.2
            (fun e => hij (Subtype.ext (Subtype.ext e))) w v
            (inf_le_left (b := archCutSubmodule K tysK) ((WeightedVenueTrace.Pieces.mem_pieceIn w).1 hw))
            (inf_le_left (b := archCutSubmodule K tysK) ((WeightedVenueTrace.Pieces.mem_pieceIn v).1 hv))

      obtain ⟨T', c', hc', u', hTcu⟩ := SiegelCovering.exists_finset_coversModCentre_iUnion_mul_centreCutSiegelSet K
      have hcov' := hTcu 1 2 two_pos one_le_two
      let Wf := WeightedVenueTrace.WindowForms.windowForms K ΦK ξK
      have hWf := fun φ (hφ : φ ∈ Wf) =>
        And.intro (WeightedVenueTrace.WindowForms.mem_windowForms_iff.1 hφ).2.1
          (WeightedVenueTrace.WindowForms.mem_windowForms_iff.1 hφ).2.2.2
      have hVf : ∀ i, ∀ w ∈ Vv i, WeightedVenueTrace.Venue.fn w ∈ Wf :=
        fun i w hw => hVW i ((WeightedVenueTrace.Pieces.mem_pieceIn w).1 hw)
      have hAk : ∀ k, ∃ a : ℝ, ∀ (J : Type) [Fintype J] (e : J → E), Orthonormal ℂ e →
          (∀ j, ∃ i, e j ∈ Vv i) → ∑ j, ‖Adag k (e j)‖ ^ 2 ≤ a := fun k =>
        WeightedVenueTrace.FamilyHS.hA_of_family Wf hWf Vv hVf c' u' 1 2 T' hc' one_pos one_lt_two hcov'
          (g k) (hg k) (hgc k).1 (hgc k).2
      have hBk : ∀ k, ∃ b : ℝ, ∀ (J : Type) [Fintype J] (e : J → E), Orthonormal ℂ e →
          (∀ j, ∃ i, e j ∈ Vv i) → ∑ j, ‖B k (e j)‖ ^ 2 ≤ b := fun k =>
        WeightedVenueTrace.FamilyHS.hB_plain_of_family Wf hWf Vv hVf c' u' 1 2 T' hc' one_pos one_lt_two hcov'
          (h k) (hh k) (hhc k).1 (hhc k).2
      choose αk hA using hAk
      choose βk hB using hBk
      have hSA := WeightedVenueTrace.Abstract.summable_norm_trace_of_orthogonal_of_adjoint_bounds Vv hVorth Ti
        Finset.univ A Adag B hTi hadj αk βk hA hB
      refine hSA.1.congr fun i => ?_
      show ‖LinearMap.trace ℂ _ (WeightedVenueTrace.Pieces.pieceEnd (hVv i) (hst i))‖ = _
      rw [WeightedVenueTrace.Pieces.trace_pieceEnd, cutTrace_eq,
        convTraceOn_eq_traceOn K _ hf hfc (i.2 : P i).2]
  ·
    have hz : (fun π : ↥({π | P π}ᶜ) =>
        ‖cutTrace K
          (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK π tysK f
          hf hfc‖) = 0 := by
      funext π
      have hπ : ¬ P π := π.2
      rw [Pi.zero_apply, norm_eq_zero, cutTrace_eq]
      by_cases hmaps : ∀ v ∈ V π, convOp K f v ∈ V π
      · have hfin : ¬ Module.Finite ℂ ↥(V π) := fun hfin => hπ ⟨hfin, hmaps⟩
        rw [convTraceOn_eq_traceOn K _ hf hfc hmaps, traceOn_eq]
        exact WeightedVenueTrace.TraceZero.trace_eq_zero_of_not_finite hfin _
      · exact convTraceOn_eq_zero K _ hf hfc hmaps
    rw [hz]
    exact summable_zero

end
p2m_reactivate "P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Venue P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.ConvolutionAssociativity P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.WeightTwist P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.SlabSquareIntegrable P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.TwistCuspidal P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace.Pieces P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset.WeightedVenueTrace"

end S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset
end P2MW
export P2MW.S_AutomorphicForm_summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre_of_subset (solution)
