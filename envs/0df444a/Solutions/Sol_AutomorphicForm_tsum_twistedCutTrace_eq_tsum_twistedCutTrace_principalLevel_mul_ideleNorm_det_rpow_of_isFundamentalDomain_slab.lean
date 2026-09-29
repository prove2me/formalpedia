-- Prove2me | solution 1 for AutomorphicForm.tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b1b2ca6e-df52-5ba7-b32e-2e8c015e5ab1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_ideleNorm_det_sigmaAdelicAct
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
p2m_open "IsDedekindDomain AutomorphicForm~det_centralScalar NumberField.TateGlobal"
open scoped ComplexConjugate NNReal Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace R4TraceSwapSigma

variable {L : Type} [Field L] [NumberField L]

section Members

variable {ΦL : Set (AdelicGL2 (𝓞 L) L)} {U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L)}
  {gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L} {B : Set (AdeleRing (𝓞 L) L)}
  {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} {N : Ideal (𝓞 L)}
  {SL : Finset (HeightOneSpectrum (𝓞 L))} {π : HeckeEigensystem L ℂ}

theorem isLsXiFunction_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π) :
    IsLsXiFunction (𝓞 L) L ⊤ ξL u := by
  refine Submodule.span_induction (p := fun u _ => IsLsXiFunction (𝓞 L) L ⊤ ξL u) ?_ ?_ ?_ ?_ hu
  · intro u h
    have h1 : LsXiMemberAt (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξL ΦL u := h.smoothCusp.1.1
    exact ((lsXiMemberAt_iff (𝓞 L) L _ ⊤ ξL ΦL u).1 h1).1
  · exact ⟨fun _ _ => rfl, fun _ _ => by simp⟩
  · rintro u w - - ⟨hul, huc⟩ ⟨hwl, hwc⟩
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.add_apply, hul, hwl]
    · simp only [Pi.add_apply, huc, hwc, mul_add]
  · rintro c u - ⟨hul, huc⟩
    refine ⟨fun γ g => ?_, fun z g => ?_⟩
    · simp only [Pi.smul_apply, hul]
    · simp only [Pi.smul_apply, huc, smul_eq_mul]
      ring

theorem apply_centralScalar_mul_of_mem {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ isotypicCuspSubmodule L (productionPinsOf L ΦL U gen B) ξL N SL π)
    (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L) :
    u (centralScalar (𝓞 L) L z * g) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * u g :=
  (isLsXiFunction_of_mem hu).central_transform ⟨z, Subgroup.mem_top z⟩ g

end Members

section Twist

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem map_scalar {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : Rˣ) :
    Matrix.GeneralLinearGroup.map (n := Fin 2) f (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (f : R →* S) a) := by
  refine Units.ext ?_
  change ((Matrix.scalar (Fin 2) (a : R)).map f : Matrix (Fin 2) (Fin 2) S) =
    Matrix.scalar (Fin 2) (f (a : R))
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero f)]

theorem sigmaAdelicAct_centralScalar (τ : L ≃ₐ[K] L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D τ (centralScalar (𝓞 L) L w) =
      centralScalar (𝓞 L) L
        (Units.map ((D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) w) :=
  map_scalar (D.act τ : RingAut (AdeleRing (𝓞 L) L)).toRingHom w

theorem unitsAct_eq_map (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct σ z =
      Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom : AdeleRing (𝓞 L) L →* _) z :=
  Units.ext rfl

theorem det_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z) = z * z := by
  refine Units.ext ?_
  change Matrix.det (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L)) = (z : AdeleRing (𝓞 L) L) * z
  rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]

theorem ideleNorm_unitsAct [NumberField K] (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L (D.unitsAct σ z) = ideleNorm L z := by
  have h := AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z)
  rw [sigmaAdelicAct_centralScalar K D σ z, ← unitsAct_eq_map K D σ z, det_centralScalar,
    det_centralScalar, ideleNorm_mul, ideleNorm_mul] at h
  have h1 := ideleNorm_pos (D.unitsAct σ z)
  have h2 := ideleNorm_pos z
  nlinarith [h, h1, h2, sq_nonneg (ideleNorm L (D.unitsAct σ z) - ideleNorm L z),
    sq_nonneg (ideleNorm L (D.unitsAct σ z) + ideleNorm L z)]

variable {K D}

theorem twistedConvOp_centralScalar_mul (σ : L ≃ₐ[K] L)
    {ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ} (φ u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : IsLsXiFunction (𝓞 L) L ⊤ ξL u) (z : (AdeleRing (𝓞 L) L)ˣ) (x : AdelicGL2 (𝓞 L) L) :
    twistedConvOp K L D σ φ u (centralScalar (𝓞 L) L z * x) =
      ((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) *
        twistedConvOp K L D σ φ u x := by
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  simp only [sigmaSectionActOn, Function.comp_apply, map_mul, sigmaAdelicAct_centralScalar K D σ z,
    mul_assoc]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [hu.central_transform ⟨_, Subgroup.mem_top _⟩, mul_assoc]

theorem twistedCutTrace_eq_zero_of_exists_apply_ne (σ : L ≃ₐ[K] L)
    (Φ : Set (AdelicGL2 (𝓞 L) L)) (U : Ideal (𝓞 L) → Subgroup (AdelicGL2 (𝓞 L) L))
    (gen : HeightOneSpectrum (𝓞 L) → AdelicGL2 (𝓞 L) L) (B : Set (AdeleRing (𝓞 L) L))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ ≠
        ξL ⟨z, Subgroup.mem_top z⟩)
    (N : Ideal (𝓞 L)) (SL : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (tys : ArchTypeFamily L) (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    twistedCutTrace K L D σ (productionPinsOf L Φ U gen B) ξL N SL Ψ tys φ hφ hφc = 0 := by
  set W : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) :=
    isotypicCuspSubmodule L (productionPinsOf L Φ U gen B) ξL N SL Ψ ⊓ archCutSubmodule L tys with hW
  have hV : ∀ u ∈ W, u ∈ isotypicCuspSubmodule L (productionPinsOf L Φ U gen B) ξL N SL Ψ :=
    fun u hu => (Submodule.mem_inf.mp hu).1
  rw [twistedCutTrace_eq]
  by_cases hmaps : ∀ u ∈ W, twistedConvOp K L D σ φ u ∈ W
  · rw [twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc hmaps, traceOn_eq]
    obtain ⟨z₀, hz₀⟩ := hne
    have hzero : ∀ u ∈ W, twistedConvOp K L D σ φ u = 0 := by
      intro u hu
      funext x
      have h1 := twistedConvOp_centralScalar_mul (D := D) σ φ u (isLsXiFunction_of_mem (hV u hu)) z₀ x
      have h2 := apply_centralScalar_mul_of_mem (hV _ (hmaps u hu)) z₀ x
      have h3 : (((ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
            AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z₀, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) -
          ((ξL ⟨z₀, Subgroup.mem_top z₀⟩ : ℂˣ) : ℂ)) * twistedConvOp K L D σ φ u x = 0 := by
        rw [sub_mul, ← h1, ← h2, sub_self]
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd (Units.val_injective (sub_eq_zero.mp h)) hz₀
      · exact h
    have hEnd : (isStableLinearOn_twistedConvOp K L D σ
        (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc hmaps).toEnd = 0 :=
      LinearMap.ext fun u => Subtype.ext (hzero u u.2)
    rw [hEnd, map_zero]
  · rw [twistedConvTraceOn_eq_zero K L D σ _ hφ hφc hmaps]

theorem exists_apply_ne_of_twist [NumberField K] (σ : L ≃ₐ[K] L)
    (ξL ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((ideleNorm L z) ^ (w) : ℝ) : ℂ) =
        ((ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hne : ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ ≠
        ξL ⟨z, Subgroup.mem_top z⟩) :
    ∃ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ₀ ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ ≠
        ξ₀ ⟨z, Subgroup.mem_top z⟩ := by
  by_contra hall
  push Not at hall
  obtain ⟨z₀, hz₀⟩ := hne
  apply hz₀
  set z : (AdeleRing (𝓞 L) L)ˣ := D.unitsAct σ⁻¹ z₀ with hz
  have hσz : D.unitsAct σ z = z₀ := by
    rw [hz, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have e1 := hξ₀ z
  have e2 := hξ₀ (D.unitsAct σ z)
  rw [ideleNorm_unitsAct K D σ z] at e2
  have hinv : ξ₀ ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξ₀ ⟨z, Subgroup.mem_top z⟩ := by
    have := hall z
    rwa [← unitsAct_eq_map K D σ z] at this
  rw [hinv] at e2
  have e3 : ((ξL ⟨D.unitsAct σ (D.unitsAct σ z), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
      ((ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) := by rw [← e2, ← e1]
  rw [hσz] at e3
  rw [← unitsAct_eq_map K D σ z₀]
  exact Units.val_injective e3

theorem xi0_of_invariant [NumberField K] (σ : L ≃ₐ[K] L)
    (ξL ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : ℝ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((ideleNorm L z) ^ (w) : ℝ) : ℂ) =
        ((ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩) :
    (∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((ideleNorm L z) ^ w : ℝ) : ℂ) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
    (∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξ₀ ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξ₀ ⟨z, Subgroup.mem_top z⟩) := by
  have h1 : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((ideleNorm L z) ^ w : ℝ) : ℂ) = ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
    intro z
    rw [hξ₀ z, unitsAct_eq_map K D σ z, hξσ z]
  refine ⟨h1, fun z => ?_⟩
  have hn : (((ideleNorm L z) ^ w : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (ideleNorm_pos z) w).ne'
  have e1 := h1 z
  have e2 := h1 (D.unitsAct σ z)
  rw [ideleNorm_unitsAct K D σ z, unitsAct_eq_map K D σ z, hξσ, ← e1] at e2
  exact Units.val_injective (mul_right_cancel₀ hn e2)

end Twist

section NormOne

variable (F : Type) [Field F] [NumberField F]

theorem fst_mul (a b : AdeleRing (𝓞 F) F) : (a * b).1 = a.1 * b.1 := rfl
theorem snd_mul (a b : AdeleRing (𝓞 F) F) : (a * b).2 = a.2 * b.2 := rfl
theorem fst_one : (1 : AdeleRing (𝓞 F) F).1 = 1 := rfl
theorem snd_one : (1 : AdeleRing (𝓞 F) F).2 = 1 := rfl

theorem smul_adelicBox_eq (x : (AdeleRing (𝓞 F) F)ˣ) (h1 : (x : AdeleRing (𝓞 F) F).1 = 1)
    (hint : (x : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
    (hint' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    x • NumberField.AdelicBox.adelicBox F = NumberField.AdelicBox.adelicBox F := by
  have h1' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    have h := congrArg (fun a : AdeleRing (𝓞 F) F => a.1) x.inv_mul
    beta_reduce at h
    rw [fst_mul, fst_one, h1, mul_one] at h
    exact h
  ext a
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  show ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * a ∈ NumberField.AdelicBox.adelicBox F ↔
    a ∈ NumberField.AdelicBox.adelicBox F
  simp only [NumberField.AdelicBox.adelicBox, Set.mem_setOf_eq, fst_mul, snd_mul, h1', one_mul]
  change (_ ∧ _ * a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) ↔
    (_ ∧ a.2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => mul_mem_integralFiniteAdeles hint' h⟩
  have : (x : AdeleRing (𝓞 F) F).2 * (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * a.2) = a.2 := by
    rw [← mul_assoc, ← snd_mul, x.mul_inv, snd_one, one_mul]
  rw [← this]
  exact mul_mem_integralFiniteAdeles hint h

theorem ideleNorm_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) (h1 : (x : AdeleRing (𝓞 F) F).1 = 1)
    (hint : (x : AdeleRing (𝓞 F) F).2 ∈ NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F)
    (hint' : ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F) :
    ideleNorm F x = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  haveI := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  haveI : (adelicAddHaar (𝓞 F) F).Regular := by
    unfold adelicAddHaar Measure.addHaar; infer_instance
  unfold ideleNorm
  rw [distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicAddHaar (𝓞 F) F)
    (s := NumberField.AdelicBox.adelicBox F)
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos F).ne'
    (NumberField.AdelicBox.adelicAddHaar_adelicBox_lt_top F).ne (r := 1)
    (by rw [smul_adelicBox_eq F x h1 hint hint', ENNReal.coe_one, one_mul])]
  rfl

variable {F}

theorem det_snd_mem_integralFiniteAdeles {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ levelOne (𝓞 F) F N) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 ∈
      NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
  have hint := (mem_finiteLevelOne_iff.mp (mem_levelOne_iff.mp hu)).1.integral
  have h : ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 =
      ((glFin (𝓞 F) F u : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  rw [h, Matrix.det_fin_two]
  exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (hint 0 0) (hint 1 1))
    (mul_mem_integralFiniteAdeles (hint 0 1) (hint 1 0))

theorem det_fst_eq_one {u : AdelicGL2 (𝓞 F) F} (hu : u ∈ finiteAdelicGL2Subgroup F) :
    ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  have h1 : glArch (𝓞 F) F u = 1 := (mem_finiteAdelicGL2Subgroup_iff F u).mp hu
  have h : ((Matrix.GeneralLinearGroup.det u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 =
      ((glArch (𝓞 F) F u : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)).det := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two]
    rfl
  rw [h, h1]
  simp

theorem ideleNorm_det_eq_one_of_mem_levelOne_inf {N : Ideal (𝓞 F)} {u : AdelicGL2 (𝓞 F) F}
    (hu : u ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.mp hu
  refine ideleNorm_eq_one F _ (det_fst_eq_one hu2) (det_snd_mem_integralFiniteAdeles hu1) ?_
  rw [← map_inv]
  exact det_snd_mem_integralFiniteAdeles (inv_mem hu1)

end NormOne

section ArchDet

variable {F : Type} [Field F] [NumberField F]

abbrev finMatOf (g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
  ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))

def archIncl (F : Type) [Field F] [NumberField F] : InfiniteAdeleRing F →* AdeleRing (𝓞 F) F where
  toFun x := (x, (1 : FiniteAdeleRing (𝓞 F) F))
  map_one' := rfl
  map_mul' _ _ := Prod.ext rfl (one_mul _).symm

theorem archIncl_apply_fst (x : InfiniteAdeleRing F) : (archIncl F x).1 = x := rfl
theorem archIncl_apply_snd (x : InfiniteAdeleRing F) : (archIncl F x).2 = 1 := rfl

theorem det_eq_archIncl_mul_finIncl (g : AdelicGL2 (𝓞 F) F) :
    Matrix.GeneralLinearGroup.det g =
      Units.map (archIncl F) (Matrix.GeneralLinearGroup.det (glArch (𝓞 F) F g)) *
        Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (Matrix.GeneralLinearGroup.det (glFin (𝓞 F) F g)) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).1 =
      ((archIncl F (Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))) *
        (finIncl (𝓞 F) F (Matrix.det (finMatOf g)))).1
    have h : adeleArch (𝓞 F) F (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) =
        Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
      rw [RingHom.map_det]; rfl
    rw [← adeleArch_apply, h, ← adeleArch_apply, map_mul, adeleArch_apply, adeleArch_apply, archIncl_apply_fst,
      finIncl_apply_fst, mul_one]
  · change (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))).2 =
      ((archIncl F (Matrix.det ((glArch (𝓞 F) F g : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))) *
        (finIncl (𝓞 F) F (Matrix.det (finMatOf g)))).2
    have h : adeleFin (𝓞 F) F (Matrix.det (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) = Matrix.det (finMatOf g) := by
      rw [RingHom.map_det]; rfl
    rw [← adeleFin_apply, h, ← adeleFin_apply, map_mul, adeleFin_apply, adeleFin_apply, archIncl_apply_snd,
      finIncl_apply_snd, one_mul]

theorem det_adelicArchGLIncl (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix.GeneralLinearGroup.det (adelicArchGLIncl F g) = Units.map (archIncl F) (Matrix.GeneralLinearGroup.det g) := by
  rw [det_eq_archIncl_mul_finIncl, glArch_adelicArchGLIncl, glFin_adelicArchGLIncl, map_one, map_one, mul_one]

theorem det_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k) = 1 := by
  have hk1 : ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff w.Completion).mp k.2).1
  rw [rowIsometryInclAt₀_apply, show adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) =
    adelicArchGLIncl F (archGLIncl F w (k : GL (Fin 2) w.Completion)) from rfl, det_adelicArchGLIncl,
    ← map_one (Units.map (archIncl F))]
  congr 1
  refine Units.ext (funext fun u => ?_)
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  change archEval F u (Matrix.det ((archGLIncl F w (k : GL (Fin 2) w.Completion) : GL (Fin 2) (InfiniteAdeleRing F)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) = 1
  rw [RingHom.map_det]
  change Matrix.det ((archComponent F u (archGLIncl F w (k : GL (Fin 2) w.Completion)) : GL (Fin 2) u.Completion) :
    Matrix (Fin 2) (Fin 2) u.Completion) = 1
  by_cases hu : u = w
  · subst hu
    rw [archComponent_archGLIncl_self, hk1]
  · rw [archComponent_archGLIncl_of_ne F hu, Units.val_one, Matrix.det_one]

theorem ideleNorm_det_mul_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 F) F) :
    ideleNorm F (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ F w k)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det x) ∧
    ideleNorm F (Matrix.GeneralLinearGroup.det (rowIsometryInclAt₀ F w k * x)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det x) := by
  rw [map_mul, map_mul, det_rowIsometryInclAt₀, mul_one, one_mul]
  exact ⟨rfl, rfl⟩

end ArchDet

section Modulus

theorem nrm_pos (g : AdelicGL2 (𝓞 L) L) : 0 < ideleNorm L (Matrix.GeneralLinearGroup.det g) :=
  ideleNorm_pos _

theorem nrm_mul (g h : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (g * h)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) * ideleNorm L (Matrix.GeneralLinearGroup.det h) := by
  rw [map_mul, ideleNorm_mul]

def Mw (c : ℝ) (u : AdelicGL2 (𝓞 L) L → ℂ) : AdelicGL2 (𝓞 L) L → ℂ :=
  fun g => u g * (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ c : ℝ) : ℂ)

theorem Mw_apply (c : ℝ) (u : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L) :
    Mw c u g = u g * (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ c : ℝ) : ℂ) := rfl

theorem Mw_Mw (c c' : ℝ) (u : AdelicGL2 (𝓞 L) L → ℂ) : Mw c (Mw c' u) = Mw (c' + c) u := by
  funext g
  simp only [Mw]
  rw [Real.rpow_add (nrm_pos g)]
  push_cast
  ring

theorem Mw_zero (u : AdelicGL2 (𝓞 L) L → ℂ) : Mw 0 u = u := by
  funext g
  simp [Mw]

theorem Mw_half_neg (w : ℝ) (u : AdelicGL2 (𝓞 L) L → ℂ) : Mw (w / 2) (Mw (-(w / 2)) u) = u := by
  rw [Mw_Mw, neg_add_cancel, Mw_zero]

theorem Mw_neg_half (w : ℝ) (u : AdelicGL2 (𝓞 L) L → ℂ) : Mw (-(w / 2)) (Mw (w / 2) u) = u := by
  rw [Mw_Mw, add_neg_cancel, Mw_zero]

theorem Mw_add (c : ℝ) (u v : AdelicGL2 (𝓞 L) L → ℂ) : Mw c (u + v) = Mw c u + Mw c v := by
  funext g
  simp [Mw, add_mul]

theorem Mw_smul (c : ℝ) (a : ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ) : Mw c (a • u) = a • Mw c u := by
  funext g
  simp [Mw, mul_assoc]

theorem Mw_zero_fun (c : ℝ) : Mw c (0 : AdelicGL2 (𝓞 L) L → ℂ) = 0 := by
  funext g
  simp [Mw]

theorem Mw_ne_zero_of_ne_zero {c : ℝ} {u : AdelicGL2 (𝓞 L) L → ℂ} (hu : u ≠ 0) : Mw c u ≠ 0 := by
  intro h
  apply hu
  have := congrArg (Mw (-c)) h
  rwa [Mw_Mw, add_neg_cancel, Mw_zero, Mw_zero_fun] at this

theorem mul_mem_archCutSubmodule (tys : ArchTypeFamily L) (m : AdelicGL2 (𝓞 L) L → ℂ)
    (hm : ∀ (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      m (x * rowIsometryInclAt₀ L w k) = m x)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : f ∈ archCutSubmodule L tys) :
    (fun x => f x * m x) ∈ archCutSubmodule L tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine comp_mul_mem_iSup_of_forall id m (fun i => archTypeSubmoduleAt L w (tys.rep w i))
    (fun i => archTypeSubmoduleAt L w (tys.rep w i)) (fun i fa hfa => ?_) (hf w)
  change fa ∈ typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ at hfa
  change (fun x => fa (id x) * m x) ∈ typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ
  exact comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ L w) (ι' := rowIsometryInclAt₀ L w)
    (MonoidHom.id (AdelicGL2 (𝓞 L) L)) (fun k => rfl) (m := m) (hm w) (ρ := (tys.rep w i).ρ) hfa

theorem mul_mem_archDualCutSubmodule (tys : ArchTypeFamily L) (m : AdelicGL2 (𝓞 L) L → ℂ)
    (hm : ∀ (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion) (x : AdelicGL2 (𝓞 L) L),
      m (x * rowIsometryInclAt₀ L w k) = m x)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : f ∈ archDualCutSubmodule L tys) :
    (fun x => f x * m x) ∈ archDualCutSubmodule L tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine comp_mul_mem_iSup_of_forall id m (fun i => archDualTypeSubmoduleAt L w (tys.rep w i))
    (fun i => archDualTypeSubmoduleAt L w (tys.rep w i)) (fun i fa hfa => ?_) (hf w)
  change fa ∈ typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ.dual at hfa
  change (fun x => fa (id x) * m x) ∈ typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ.dual
  exact comp_mul_mem_typeSubmodule_of_hom (ι := rowIsometryInclAt₀ L w) (ι' := rowIsometryInclAt₀ L w)
    (MonoidHom.id (AdelicGL2 (𝓞 L) L)) (fun k => rfl) (m := m) (hm w) (ρ := (tys.rep w i).ρ.dual) hfa

theorem norm_pow_right_invariant (c : ℝ) (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 L) L) :
    ((((ideleNorm L (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ L w k))) ^ c : ℝ) : ℂ)) =
      (((ideleNorm L (Matrix.GeneralLinearGroup.det x)) ^ c : ℝ) : ℂ) := by
  rw [(ideleNorm_det_mul_rowIsometryInclAt₀ w k x).1]

theorem norm_inv_pow_right_invariant (c : ℝ) (w : InfinitePlace L) (k : rowIsometrySubgroup₀ w.Completion)
    (x : AdelicGL2 (𝓞 L) L) :
    ((((ideleNorm L (Matrix.GeneralLinearGroup.det (x * rowIsometryInclAt₀ L w k)⁻¹)) ^ c : ℝ) : ℂ)) =
      (((ideleNorm L (Matrix.GeneralLinearGroup.det x⁻¹)) ^ c : ℝ) : ℂ) := by
  rw [mul_inv_rev, ← map_inv, (ideleNorm_det_mul_rowIsometryInclAt₀ w k⁻¹ x⁻¹).2]

theorem Mw_mem_archCutSubmodule (tys : ArchTypeFamily L) (c : ℝ) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : u ∈ archCutSubmodule L tys) : Mw c u ∈ archCutSubmodule L tys :=
  mul_mem_archCutSubmodule tys _ (fun w k x => norm_pow_right_invariant c w k x) hu

theorem isArchBiFinite_Mw (tys : ArchTypeFamily L) (c : ℝ) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : IsArchBiFinite L tys f) : IsArchBiFinite L tys (Mw c f) := by
  refine ⟨?_, mul_mem_archDualCutSubmodule tys _ (fun w k x => norm_pow_right_invariant c w k x) hf.2⟩
  exact mul_mem_archCutSubmodule tys (fun x => (((ideleNorm L (Matrix.GeneralLinearGroup.det x⁻¹)) ^ c : ℝ) : ℂ))
    (fun w k x => norm_inv_pow_right_invariant c w k x) hf.1

theorem isBiInvariantUnder_Mw (N : Ideal (𝓞 L)) (c : ℝ) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hf : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f) :
    IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) (Mw c f) := by
  intro k hk g
  have hk' : k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L :=
    Subgroup.mem_inf.mpr ⟨principalLevel_le_levelOne (𝓞 L) L N (Subgroup.mem_inf.mp hk).1, (Subgroup.mem_inf.mp hk).2⟩
  have hn := ideleNorm_det_eq_one_of_mem_levelOne_inf hk'
  refine ⟨?_, ?_⟩
  · simp only [Mw, nrm_mul, hn, one_mul, (hf k hk' g).1]
  · simp only [Mw, nrm_mul, hn, mul_one, (hf k hk' g).2]

end Modulus

section Blocks

def chi (c : ℝ) : HeightOneSpectrum (𝓞 L) → ℂ :=
  fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ c : ℝ) : ℂ)

theorem chi_mul_chi_neg (c : ℝ) (v : HeightOneSpectrum (𝓞 L)) : chi (-c) v * chi c v = 1 := by
  have hq : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero hN
  simp only [chi]
  rw [← Complex.ofReal_mul, ← Real.rpow_add hq, neg_add_cancel, Real.rpow_zero, Complex.ofReal_one]

theorem hes_ext {Ψ Ψ' : HeckeEigensystem L ℂ} (h1 : Ψ.level = Ψ'.level) (h2 : Ψ.a = Ψ'.a)
    (h3 : Ψ.b = Ψ'.b) : Ψ = Ψ' := by
  rcases Ψ with ⟨N₁, hN₁, a₁, b₁⟩
  rcases Ψ' with ⟨N₂, hN₂, a₂, b₂⟩
  simp only at h1 h2 h3
  subst h1; subst h2; subst h3
  rfl

theorem twist_twist_neg (Ψ : HeckeEigensystem L ℂ) (c : ℝ) : (Ψ.twist (chi c)).twist (chi (-c)) = Ψ := by
  refine hes_ext rfl (funext fun v => ?_) (funext fun v => ?_)
  · simp only [AutomorphicForm.HeckeEigensystem.twist_a]
    rw [← mul_assoc, chi_mul_chi_neg, one_mul]
  · simp only [AutomorphicForm.HeckeEigensystem.twist_b]
    rw [← mul_assoc, ← mul_pow, chi_mul_chi_neg, one_pow, one_mul]

theorem twist_neg_twist (Ψ : HeckeEigensystem L ℂ) (c : ℝ) : (Ψ.twist (chi (-c))).twist (chi c) = Ψ := by
  have h := twist_twist_neg Ψ (-c)
  rwa [neg_neg] at h

variable (Φ₂ : Set (AdelicGL2 (𝓞 L) L)) (ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
  (N : Ideal (𝓞 L)) (SL : Finset (HeightOneSpectrum (𝓞 L)))

theorem eq_of_mem_of_mem_of_ne_zero (Ψa Ψb : HeckeEigensystem L ℂ)
    (haN : Ψa.level = N) (haS : ∀ v ∈ SL, Ψa.a v = 0 ∧ Ψa.b v = 0)
    (hbN : Ψb.level = N) (hbS : ∀ v ∈ SL, Ψb.a v = 0 ∧ Ψb.b v = 0)
    (x : AdelicGL2 (𝓞 L) L → ℂ)
    (hxa : x ∈ isotypicCuspSubmodule L
      (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψa)
    (hxb : x ∈ isotypicCuspSubmodule L
      (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψb)
    (hx : x ≠ 0) : Ψa = Ψb := by
  set P := productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun v => heckeGen (𝓞 L) L v) (adelicBox L) with hP
  have hisoa : IsIsotypicCuspFormAt L P ξ₀ N SL Ψa x :=
    AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L Φ₂ _ _ ξ₀ N SL Ψa x hxa hx
  have hisob : IsIsotypicCuspFormAt L P ξ₀ N SL Ψb x :=
    AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L Φ₂ _ _ ξ₀ N SL Ψb x hxb hx
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hx
  have hcla : Ψa ∈ cuspClasses L P ξ₀ N SL :=
    ⟨haN, haS, (Submodule.ne_bot_iff _).mpr ⟨x, hxa, hx⟩⟩
  have hclb : Ψb ∈ cuspClasses L P ξ₀ N SL :=
    ⟨hbN, hbS, (Submodule.ne_bot_iff _).mpr ⟨x, hxb, hx⟩⟩
  refine eq_of_mem_cuspClasses hcla hclb fun v hv => ⟨?_, ?_⟩
  · obtain ⟨ra, hra, hsa⟩ := hisoa.hecke_eigen v hv
    obtain ⟨rb, hrb, hsb⟩ := hisob.hecke_eigen v hv
    have hind := HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hra hrb
      (φ := x) hisoa.level_invariant g₀
    have h1 : SmoothCusp.heckeCosetSum L rb x g₀ = SmoothCusp.heckeCosetSum L ra x g₀ := hind
    rw [hsa g₀, hsb g₀] at h1
    exact (mul_right_cancel₀ hg₀ h1).symm
  · have h1 := hisoa.central_eigen v hv g₀
    have h2 := hisob.central_eigen v hv g₀
    rw [h1] at h2
    have h3 := mul_right_cancel₀ hg₀ h2
    simp only [AutomorphicForm.HeckeEigensystem.toRawCentral_b] at h3
    exact mul_left_cancel₀ (inv_ne_zero (AutomorphicForm.HeckeEigensystem.cNorm_ne_zero v)) h3

end Blocks

section Operators

variable (K : Type) [Field K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem twistedConvOp_Mw (w : ℝ) (φ φ' : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (u : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp K L D σ φ' (Mw (-(w / 2)) u) = Mw (-(w / 2)) (twistedConvOp K L D σ φ u) := by
  funext x
  rw [Mw_apply, twistedConvOp_apply, twistedConvOp_apply, rightConv_apply, rightConv_apply,
    ← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sigmaSectionActOn, Function.comp_apply, Mw_apply]
  have hxy : ideleNorm L (Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ (x * y))) =
      ideleNorm L (Matrix.GeneralLinearGroup.det x) * ideleNorm L (Matrix.GeneralLinearGroup.det y) := by
    rw [AutomorphicForm.ideleNorm_det_sigmaAdelicAct K L D σ (x * y), nrm_mul]
  have hr : (ideleNorm L (Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ (x * y)))) ^ (-(w / 2)) *
      (ideleNorm L (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) =
        (ideleNorm L (Matrix.GeneralLinearGroup.det x)) ^ (-(w / 2)) := by
    rw [hxy, Real.mul_rpow (nrm_pos x).le (nrm_pos y).le, mul_assoc, ← Real.rpow_add (nrm_pos y),
      neg_add_cancel, Real.rpow_zero, mul_one]
  have hc : ((((ideleNorm L (Matrix.GeneralLinearGroup.det (sigmaAdelicAct K L D σ (x * y)))) ^ (-(w / 2)) : ℝ) : ℂ)) *
      (((ideleNorm L (Matrix.GeneralLinearGroup.det y)) ^ (w / 2) : ℝ) : ℂ) =
        (((ideleNorm L (Matrix.GeneralLinearGroup.det x)) ^ (-(w / 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hr]
  rw [hφ' y, ← hc]
  ring

theorem twistedConvOp_apply_mul_of_mem_levelOne (N : Ideal (𝓞 L)) (w : ℝ) (φ φ' : AdelicGL2 (𝓞 L) L → ℂ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (v : AdelicGL2 (𝓞 L) L → ℂ) (g : AdelicGL2 (𝓞 L) L)
    {k : AdelicGL2 (𝓞 L) L} (hk : k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) :
    twistedConvOp K L D σ φ' v (g * k) = twistedConvOp K L D σ φ' v g := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  have hφ'k : ∀ y, φ' (k⁻¹ * y) = φ' y := by
    intro y
    rw [hφ' (k⁻¹ * y), hφ' y, (hbi k⁻¹ (inv_mem hk) y).1, nrm_mul,
      ideleNorm_det_eq_one_of_mem_levelOne_inf (inv_mem hk), one_mul]
  rw [twistedConvOp_apply, rightConv_apply, rightConv_apply]
  have key : (fun y => sigmaSectionActOn K L D σ v (g * k * y) * φ' y) =
      fun y => (fun z => sigmaSectionActOn K L D σ v (g * z) * φ' (k⁻¹ * z)) (k * y) := by
    funext y
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key, integral_mul_left_eq_self (fun z => sigmaSectionActOn K L D σ v (g * z) * φ' (k⁻¹ * z)) k]
  simp only [hφ'k]

end Operators

section Invariant

variable (K : Type) [Field K] [NumberField K] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
variable (α β : ℝ) (ΦL Φ₂ : Set (AdelicGL2 (𝓞 L) L))
variable (ξL ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (w : ℝ)
variable (N : Ideal (𝓞 L)) (SL : Finset (HeightOneSpectrum (𝓞 L))) (tysL : ArchTypeFamily L)

def invSubmodule (N : Ideal (𝓞 L)) : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) where
  carrier := {u | ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u (g * k) = u g}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun hu hv g k hk => by simp only [Pi.add_apply, hu g k hk, hv g k hk]
  smul_mem' := fun c u hu g k hk => by simp only [Pi.smul_apply, hu g k hk]

theorem mem_invSubmodule_iff (u : AdelicGL2 (𝓞 L) L → ℂ) :
    u ∈ invSubmodule N ↔
      ∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, u (g * k) = u g :=
  Iff.rfl

theorem Mw_mem_of_mem
    (hMT : ∀ (Ψ : HeckeEigensystem L ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ),
      IsIsotypicCuspFormAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL Ψ u →
      IsIsotypicCuspFormAt L
        (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL
        (Ψ.twist fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (w / 2) : ℝ) : ℂ))
        (fun g => u g *
          (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (-(w / 2)) : ℝ) : ℂ)))
    (Ψ : HeckeEigensystem L ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : u ∈ isotypicCuspSubmodule L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL Ψ) :
    Mw (-(w / 2)) u ∈ isotypicCuspSubmodule L
      (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL (Ψ.twist (chi (w / 2))) ∧
    Mw (-(w / 2)) u ∈ invSubmodule N := by
  by_cases h0 : u = 0
  · subst h0
    rw [Mw_zero_fun]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  have hiso := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L ΦL _ _ ξL N SL Ψ u hu h0
  have h2 : IsIsotypicCuspFormAt L
      (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL (Ψ.twist (chi (w / 2))) (Mw (-(w / 2)) u) :=
    hMT Ψ u hiso
  refine ⟨h2.mem_isotypicCuspSubmodule, fun g k hk => ?_⟩
  simp only [Mw, nrm_mul, ideleNorm_det_eq_one_of_mem_levelOne_inf hk, mul_one, hiso.level_invariant g k hk]

theorem Mw'_mem_of_mem
    (hMT' : ∀ (Ψ : HeckeEigensystem L ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ),
      IsIsotypicCuspFormAt L
        (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψ u →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈ levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
        u (g * k) = u g) →
      IsIsotypicCuspFormAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL
        (Ψ.twist fun v => ((((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(w / 2)) : ℝ) : ℂ))
        (fun g => u g *
          (((ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)))
    (Ψ' : HeckeEigensystem L ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ)
    (hu : u ∈ isotypicCuspSubmodule L
      (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψ')
    (hinv : u ∈ invSubmodule N) :
    Mw (w / 2) u ∈ isotypicCuspSubmodule L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL (Ψ'.twist (chi (-(w / 2)))) := by
  by_cases h0 : u = 0
  · subst h0
    rw [Mw_zero_fun]
    exact Submodule.zero_mem _
  have hiso := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L Φ₂ _ _ ξ₀ N SL Ψ' u hu h0
  have h1 : IsIsotypicCuspFormAt L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξL N SL (Ψ'.twist (chi (-(w / 2)))) (Mw (w / 2) u) :=
    hMT' Ψ' u hiso hinv
  exact h1.mem_isotypicCuspSubmodule

end Invariant

end R4TraceSwapSigma

end

open R4TraceSwapSigma in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (Φ₂ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₂s : Φ₂ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₂ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₂
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (w : ℝ) (ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) =
        ((ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (harch : IsArchBiFinite L tysL φ)
    (φ' : AdelicGL2 (𝓞 L) L → ℂ) (hφ'c : Continuous φ') (hφ'k : HasCompactSupport φ')
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (hfin : ∀ Ψ ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      FiniteDimensional ℂ ↥(isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ ⊓ archCutSubmodule L tysL))
    (hfin₂ : ∀ Ψ ∈ cuspClasses L
        (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL,
      FiniteDimensional ℂ ↥(isotypicCuspSubmodule L
        (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψ ⊓ archCutSubmodule L tysL)) :
    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
      twistedCutTrace K L D σ
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc =
    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL},
      twistedCutTrace K L D σ
        (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψ.1 tysL φ' hφ'c hφ'k := by
  classical
  by_cases hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξL ⟨Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom :
          AdeleRing (𝓞 L) L →* AdeleRing (𝓞 L) L) z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩
  swap
  ·
    push Not at hξσ
    have hne₀ := exists_apply_ne_of_twist (K := K) (D := D) σ ξL ξ₀ w hξ₀ hξσ
    have h1 : ∀ Ψ : {Ψ : HeckeEigensystem L ℂ //
          Ψ ∈ cuspClasses L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
        twistedCutTrace K L D σ
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL Ψ.1 tysL φ hφ hφc = 0 := fun Ψ =>
      twistedCutTrace_eq_zero_of_exists_apply_ne σ ΦL _ _ _ ξL hξσ N SL Ψ.1 tysL φ hφ hφc
    have h2 : ∀ Ψ : {Ψ : HeckeEigensystem L ℂ //
          Ψ ∈ cuspClasses L
            (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL},
        twistedCutTrace K L D σ
          (productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ₀ N SL Ψ.1 tysL φ' hφ'c hφ'k = 0 := fun Ψ =>
      twistedCutTrace_eq_zero_of_exists_apply_ne σ Φ₂ _ _ _ ξ₀ hne₀ N SL Ψ.1 tysL φ' hφ'c hφ'k
    rw [tsum_congr h1, tsum_congr h2, tsum_zero, tsum_zero]

  obtain ⟨hξ₀', hξ₀σ⟩ := xi0_of_invariant (K := K) (D := D) σ ξL ξ₀ w hξ₀ hξσ

  set P₁ := productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun w => heckeGen (𝓞 L) L w) (adelicBox L) with hP₁
  set P₂ := productionPinsOf L Φ₂ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
      (fun v => heckeGen (𝓞 L) L v) (adelicBox L) with hP₂
  let V₁ : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    isotypicCuspSubmodule L P₁ ξL N SL Ψ
  let V₂ : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    isotypicCuspSubmodule L P₂ ξ₀ N SL Ψ
  let W₁ : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    V₁ Ψ ⊓ archCutSubmodule L tysL
  let W₂ : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    V₂ Ψ ⊓ archCutSubmodule L tysL
  let tw : HeckeEigensystem L ℂ → HeckeEigensystem L ℂ := fun Ψ => Ψ.twist (chi (w / 2))
  let tw' : HeckeEigensystem L ℂ → HeckeEigensystem L ℂ := fun Ψ => Ψ.twist (chi (-(w / 2)))
  let A₁ : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) := twistedConvOp K L D σ φ
  let A₂ : (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) := twistedConvOp K L D σ φ'
  let term₁ : HeckeEigensystem L ℂ → ℂ := fun Ψ => twistedCutTrace K L D σ P₁ ξL N SL Ψ tysL φ hφ hφc
  let term₂ : HeckeEigensystem L ℂ → ℂ := fun Ψ => twistedCutTrace K L D σ P₂ ξ₀ N SL Ψ tysL φ' hφ'c hφ'k

  obtain ⟨hMTa, hMTb⟩ :=
    AutomorphicForm.isIsotypicCuspFormAt_mul_ideleNorm_det_rpow_principalLevel_and_levelOne_of_isFundamentalDomain_slab
      L α β hα ΦL Φ₂ hΦs hΦ hΦ₂s hΦ₂ ξL ξ₀ w hξ₀' N SL hN

  have hφ'M : φ' = Mw (w / 2) φ := funext fun g => hφ' g
  have hφ'bi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ' := by
    rw [hφ'M]; exact isBiInvariantUnder_Mw N (w / 2) hbi
  have hφ'arch : IsArchBiFinite L tysL φ' := by
    rw [hφ'M]; exact isArchBiFinite_Mw tysL (w / 2) harch

  have htw'tw : ∀ Ψ, tw' (tw Ψ) = Ψ := fun Ψ => twist_twist_neg Ψ (w / 2)
  have htwtw' : ∀ Ψ, tw (tw' Ψ) = Ψ := fun Ψ => twist_neg_twist Ψ (w / 2)
  have htw_zero : ∀ Ψ : HeckeEigensystem L ℂ, (∀ v ∈ SL, Ψ.a v = 0 ∧ Ψ.b v = 0) →
      ∀ v ∈ SL, (tw Ψ).a v = 0 ∧ (tw Ψ).b v = 0 := by
    intro Ψ h v hv
    simp only [tw, AutomorphicForm.HeckeEigensystem.twist_a, AutomorphicForm.HeckeEigensystem.twist_b,
      (h v hv).1, (h v hv).2, mul_zero, and_self]
  have htw'_zero : ∀ Ψ : HeckeEigensystem L ℂ, (∀ v ∈ SL, Ψ.a v = 0 ∧ Ψ.b v = 0) →
      ∀ v ∈ SL, (tw' Ψ).a v = 0 ∧ (tw' Ψ).b v = 0 := by
    intro Ψ h v hv
    simp only [tw', AutomorphicForm.HeckeEigensystem.twist_a, AutomorphicForm.HeckeEigensystem.twist_b,
      (h v hv).1, (h v hv).2, mul_zero, and_self]

  have hM : ∀ Ψ, ∀ u ∈ W₁ Ψ, Mw (-(w / 2)) u ∈ W₂ (tw Ψ) ∧ Mw (-(w / 2)) u ∈ invSubmodule N := by
    intro Ψ u hu
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu
    obtain ⟨h1, h2⟩ := Mw_mem_of_mem ΦL Φ₂ ξL ξ₀ w N SL hMTa Ψ u hu1
    exact ⟨Submodule.mem_inf.mpr ⟨h1, Mw_mem_archCutSubmodule tysL _ hu2⟩, h2⟩
  have hM' : ∀ Ψ', ∀ u' ∈ W₂ Ψ', u' ∈ invSubmodule N → Mw (w / 2) u' ∈ W₁ (tw' Ψ') := by
    intro Ψ' u' hu' hinv
    obtain ⟨hu1, hu2⟩ := Submodule.mem_inf.mp hu'
    exact Submodule.mem_inf.mpr ⟨Mw'_mem_of_mem ΦL Φ₂ ξL ξ₀ w N SL hMTb Ψ' u' hu1 hinv,
      Mw_mem_archCutSubmodule tysL _ hu2⟩

  have hAM : ∀ u, A₂ (Mw (-(w / 2)) u) = Mw (-(w / 2)) (A₁ u) := fun u =>
    twistedConvOp_Mw K D σ w φ φ' hφ' u
  have hA₂inv : ∀ v, A₂ v ∈ invSubmodule N := fun v g k hk =>
    twistedConvOp_apply_mul_of_mem_levelOne K D σ N w φ φ' hbi hφ' v g hk

  have htw_mem : ∀ Ψ ∈ cuspClasses L P₁ ξL N SL, tw Ψ ∈ cuspClasses L P₂ ξ₀ N SL := by
    rintro Ψ ⟨hΨN, hΨS, hΨV⟩
    refine ⟨hΨN, htw_zero Ψ hΨS, ?_⟩
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hΨV
    obtain ⟨h1, -⟩ := Mw_mem_of_mem ΦL Φ₂ ξL ξ₀ w N SL hMTa Ψ u hu
    exact (Submodule.ne_bot_iff _).mpr ⟨_, h1, Mw_ne_zero_of_ne_zero hu0⟩

  have hclass : ∀ Ψ ∈ cuspClasses L P₁ ξL N SL, term₁ Ψ = term₂ (tw Ψ) := by
    intro Ψ hΨ
    have hΨ₂ := htw_mem Ψ hΨ
    haveI hfd₂ : FiniteDimensional ℂ (W₂ (tw Ψ)) := hfin₂ (tw Ψ) hΨ₂

    let W₃ : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := W₂ (tw Ψ) ⊓ invSubmodule N
    haveI hfd₃ : FiniteDimensional ℂ W₃ := Submodule.finiteDimensional_of_le (inf_le_left : W₃ ≤ W₂ (tw Ψ))
    have hMW : ∀ u ∈ W₁ Ψ, Mw (-(w / 2)) u ∈ W₃ := fun u hu =>
      Submodule.mem_inf.mpr ⟨(hM Ψ u hu).1, (hM Ψ u hu).2⟩
    have hM'W : ∀ u' ∈ W₃, Mw (w / 2) u' ∈ W₁ Ψ := by
      intro u' hu'
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hu'
      have h := hM' (tw Ψ) u' h1 h2
      rwa [htw'tw] at h
    show twistedCutTrace K L D σ P₁ ξL N SL Ψ tysL φ hφ hφc =
      twistedCutTrace K L D σ P₂ ξ₀ N SL (tw Ψ) tysL φ' hφ'c hφ'k
    rw [twistedCutTrace_eq, twistedCutTrace_eq]
    change twistedConvTraceOn K L D σ (W₁ Ψ) (continuous_of_mem_isotypicCuspSubmodule_inf L) φ hφ hφc =
      twistedConvTraceOn K L D σ (W₂ (tw Ψ)) (continuous_of_mem_isotypicCuspSubmodule_inf L) φ' hφ'c hφ'k
    by_cases h2 : ∀ u' ∈ W₂ (tw Ψ), A₂ u' ∈ W₂ (tw Ψ)
    ·
      have h1 : ∀ u ∈ W₁ Ψ, A₁ u ∈ W₁ Ψ := by
        intro u hu
        have hMu := hMW u hu
        have hA3 : A₂ (Mw (-(w / 2)) u) ∈ W₃ :=
          Submodule.mem_inf.mpr ⟨h2 _ (Submodule.mem_inf.mp hMu).1, hA₂inv _⟩
        have h := hM'W _ hA3
        rwa [hAM u, Mw_half_neg] at h
      rw [twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc h1, twistedConvTraceOn_eq_traceOn K L D σ _ hφ'c hφ'k h2,
        traceOn_eq, traceOn_eq]
      set s₁ := isStableLinearOn_twistedConvOp K L D σ (V := W₁ Ψ)
        (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc h1 with hs₁
      set s₂ := isStableLinearOn_twistedConvOp K L D σ (V := W₂ (tw Ψ))
        (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ'c hφ'k h2 with hs₂

      let T₂' : W₂ (tw Ψ) →ₗ[ℂ] W₃ :=
        { toFun := fun u' => ⟨A₂ u', Submodule.mem_inf.mpr ⟨h2 u' u'.2, hA₂inv _⟩⟩
          map_add' := fun u v => Subtype.ext (s₂.map_add u u.2 v v.2)
          map_smul' := fun c u => Subtype.ext (s₂.map_smul c u u.2) }
      let incl : W₃ →ₗ[ℂ] W₂ (tw Ψ) := Submodule.inclusion inf_le_left
      have hT₂ : s₂.toEnd = incl ∘ₗ T₂' := LinearMap.ext fun u => Subtype.ext rfl

      let e : W₁ Ψ ≃ₗ[ℂ] W₃ :=
        { toFun := fun u => ⟨Mw (-(w / 2)) u, hMW u u.2⟩
          map_add' := fun u v => Subtype.ext (Mw_add _ _ _)
          map_smul' := fun c u => Subtype.ext (Mw_smul _ _ _)
          invFun := fun u' => ⟨Mw (w / 2) u', hM'W u' u'.2⟩
          left_inv := fun u => Subtype.ext (by dsimp only; exact Mw_half_neg w (u : AdelicGL2 (𝓞 L) L → ℂ))
          right_inv := fun u' => Subtype.ext (by dsimp only; exact Mw_neg_half w (u' : AdelicGL2 (𝓞 L) L → ℂ)) }
      have hconj : T₂' ∘ₗ incl = e.conj s₁.toEnd := by
        rw [LinearEquiv.conj_apply]
        refine LinearMap.ext fun u' => Subtype.ext ?_
        show A₂ (u' : AdelicGL2 (𝓞 L) L → ℂ) = Mw (-(w / 2)) (A₁ (Mw (w / 2) (u' : AdelicGL2 (𝓞 L) L → ℂ)))
        rw [← hAM, Mw_neg_half]
      rw [hT₂, LinearMap.trace_comp_comm', hconj, LinearMap.trace_conj']
    ·
      rw [twistedConvTraceOn_eq_zero K L D σ _ hφ'c hφ'k h2]
      by_cases h1 : ∀ u ∈ W₁ Ψ, A₁ u ∈ W₁ Ψ
      swap
      · rw [twistedConvTraceOn_eq_zero K L D σ _ hφ hφc h1]
      rw [twistedConvTraceOn_eq_traceOn K L D σ _ hφ hφc h1, traceOn_eq]

      obtain ⟨Ψ'', hΨ''N, hΨ''S, hblock⟩ :=
        AutomorphicForm.exists_forall_twistedConvOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
          K L D σ α β hα hαβ Φ₂ hΦ₂s hΦ₂ ξ₀ hξ₀σ SL hSL N hN tysL (tw Ψ) hΨ.1
      have hb : ∀ u' ∈ W₂ (tw Ψ), A₂ u' ∈ W₂ Ψ'' := hblock φ' hφ'c hφ'k hφ'bi hφ'arch
      have hne : Ψ'' ≠ tw Ψ := by
        intro heq
        apply h2
        intro u' hu'
        have h := hb u' hu'
        rwa [heq] at h
      have hzero : ∀ u ∈ W₁ Ψ, A₁ u = 0 := by
        intro u hu
        have hx₁ : Mw (-(w / 2)) (A₁ u) ∈ V₂ (tw Ψ) :=
          (Submodule.mem_inf.mp (Submodule.mem_inf.mp (hMW _ (h1 u hu))).1).1
        have hx₂ : Mw (-(w / 2)) (A₁ u) ∈ V₂ Ψ'' := by
          rw [← hAM u]
          exact (Submodule.mem_inf.mp (hb _ (Submodule.mem_inf.mp (hMW u hu)).1)).1
        by_contra hA
        have hx0 : Mw (-(w / 2)) (A₁ u) ≠ 0 := Mw_ne_zero_of_ne_zero hA
        exact hne (eq_of_mem_of_mem_of_ne_zero Φ₂ ξ₀ N SL Ψ'' (tw Ψ) hΨ''N hΨ''S hΨ₂.1 hΨ₂.2.1 _ hx₂ hx₁ hx0)
      have hEnd : (isStableLinearOn_twistedConvOp K L D σ (V := W₁ Ψ)
          (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ hφc h1).toEnd = 0 :=
        LinearMap.ext fun u => Subtype.ext (hzero u u.2)
      rw [hEnd, map_zero]

  have hsupp : ∀ Ψ' ∈ cuspClasses L P₂ ξ₀ N SL, term₂ Ψ' ≠ 0 → tw' Ψ' ∈ cuspClasses L P₁ ξL N SL := by
    rintro Ψ' ⟨hΨ'N, hΨ'S, -⟩ ht
    refine ⟨hΨ'N, htw'_zero Ψ' hΨ'S, ?_⟩
    obtain ⟨hmaps, -⟩ := mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero K L D ht
    have ht' : LinearMap.trace ℂ _ (isStableLinearOn_twistedConvOp K L D σ (V := W₂ Ψ')
        (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ'c hφ'k hmaps).toEnd ≠ 0 := by
      have h := ht
      change twistedCutTrace K L D σ P₂ ξ₀ N SL Ψ' tysL φ' hφ'c hφ'k ≠ 0 at h
      rwa [twistedCutTrace_eq, twistedConvTraceOn_eq_traceOn K L D σ _ hφ'c hφ'k hmaps, traceOn_eq] at h
    have hex : ∃ u' ∈ W₂ Ψ', A₂ u' ≠ 0 := by
      by_contra hall
      push Not at hall
      apply ht'
      have hEnd : (isStableLinearOn_twistedConvOp K L D σ (V := W₂ Ψ')
          (continuous_of_mem_isotypicCuspSubmodule_inf L) hφ'c hφ'k hmaps).toEnd = 0 :=
        LinearMap.ext fun u => Subtype.ext (hall u u.2)
      rw [hEnd, map_zero]
    obtain ⟨u', hu', hA0⟩ := hex
    have hy : A₂ u' ∈ W₂ Ψ' := hmaps u' hu'
    have hy1 := hM' Ψ' _ hy (hA₂inv u')
    exact (Submodule.ne_bot_iff _).mpr ⟨_, (Submodule.mem_inf.mp hy1).1, Mw_ne_zero_of_ne_zero hA0⟩

  symm
  refine tsum_eq_tsum_of_ne_zero_bij
    (fun x => (⟨tw x.1.1, htw_mem x.1.1 x.1.2⟩ : {Ψ : HeckeEigensystem L ℂ // Ψ ∈ cuspClasses L P₂ ξ₀ N SL}))
    ?_ ?_ ?_
  · rintro ⟨⟨Ψa, hΨa⟩, ha⟩ ⟨⟨Ψb, hΨb⟩, hb⟩ h
    have h' : tw Ψa = tw Ψb := congrArg Subtype.val h
    have h'' : Ψa = Ψb := by rw [← htw'tw Ψa, ← htw'tw Ψb, h']
    subst h''
    rfl
  · rintro ⟨Ψ', hΨ'⟩ ht
    have ht' : term₂ Ψ' ≠ 0 := ht
    have hΨ := hsupp Ψ' hΨ' ht'
    have hne1 : term₁ (tw' Ψ') ≠ 0 := by
      rw [hclass (tw' Ψ') hΨ, htwtw']
      exact ht'
    refine ⟨⟨⟨tw' Ψ', hΨ⟩, hne1⟩, ?_⟩
    exact Subtype.ext (htwtw' Ψ')
  · rintro ⟨⟨Ψ, hΨ⟩, -⟩
    exact (hclass Ψ hΨ).symm

end S_AutomorphicForm_tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_tsum_twistedCutTrace_eq_tsum_twistedCutTrace_principalLevel_mul_ideleNorm_det_rpow_of_isFundamentalDomain_slab (solution)
