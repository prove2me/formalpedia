-- Prove2me | solution 1 for AutomorphicForm.two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/93d9fbe9-5580-586b-86ba-45991b7824e5

import Theorems.Thm_AutomorphicForm_exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
import Theorems.Thm_MeasureTheory_exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
import Theorems.Thm_AutomorphicForm_map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
p2m_attr_erase "instance" "ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace"
p2m_attr_erase "instance" "NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add AutomorphicForm.rightTranslationEmbed_smul_apply LT.LatticeTree.IntegralAut.refl_toField LT.LatticeTree.vecPair_one LT.LatticeTree.IntegralAut.mk.sizeOf_spec LT.LatticeTree.galVec_refl LT.LatticeTree.mulVecPair_zero LT.LatticeTree.galVec_apply LT.LatticeTree.vecPair_zero LT.LatticeTree.IntegralAut.refl_toBase LT.LatticeTree.scalarGL_coe LT.LatticeTree.IntegralAut.mk.injEq LT.LatticeTree.IntegralAut.comp_toBase_apply LT.LatticeTree.IntegralAut.unitMap_coe LT.LatticeTree.latticeGal_refl LT.LatticeTree.gammaZero_coe LT.LatticeTree.Vertex.act_mk LT.LatticeTree.Vertex.galAct_mk"
p2m_attr_erase "simp" "LT.LatticeTree.transvectionGate_coe LT.LatticeTree.mulVecPair_one LT.LatticeTree.diagSnd_coe LT.LatticeTree.unitOfNeZero_coe LT.LatticeTree.IntegralAut.comp_toField_apply LT.LatticeTree.mulVecLinR_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.preimage_mulLeft_smul LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two tensorArch tensorPlace baseChangeEquiv baseChangeGL_eq baseChangeEquiv_tmul_one baseChangeGLEquiv baseChangeGLEquiv_apply isTopologicalRing_tensor t2Space_tensor locallyCompactSpace_tensor isTopologicalGroup_tensorGL t2Space_tensorGL glBorelOf centralizerBorel toTensorGL semiLocalIntegralSet sigmaTensor sigmaGL normString IsSigmaConjugate IsNormConjugator twistedCentralizer twistedCentralizerBorel localGLBorel localHaar globalPoints centralScalar sigmaCentralizer mem_sigmaCentralizer_iff IsGlobalAddChar tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft coe_sigmaGL continuous_sigmaTensor"
namespace MassDReduce
p2m_open "AutomorphicForm"

section Discrete

variable (F : Type) [Field F] [NumberField F]

theorem exists_isOpen_forall_algebraMap_mem_eq_zero :
    ∃ U : Set (AdeleRing (𝓞 F) F), IsOpen U ∧ (0 : AdeleRing (𝓞 F) F) ∈ U ∧
      ∀ ξ : F, algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ U → ξ = 0 := by
  obtain ⟨C, hC, h0C⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 F) F)
  have hfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact F hC
  set S : Set F := {ξ : F | algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C} with hS
  set T : Set (AdeleRing (𝓞 F) F) := (algebraMap F (AdeleRing (𝓞 F) F)) '' (S \ {0}) with hT
  have hTfin : T.Finite := (hfin.subset Set.diff_subset).image _
  have hTclosed : IsClosed T := hTfin.isClosed
  refine ⟨interior C \ T, isOpen_interior.sdiff hTclosed, ⟨mem_interior_iff_mem_nhds.2 h0C, ?_⟩, ?_⟩
  · rintro ⟨ξ, ⟨hξS, hξ0⟩, hξ⟩
    have hinj := NumberField.AdeleRing.algebraMap_injective (R := 𝓞 F) (K := F)
    have : ξ = 0 := hinj (by rw [hξ, map_zero])
    exact hξ0 this
  · intro ξ hξ
    by_contra hne
    have hξC : algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ C := interior_subset hξ.1
    exact hξ.2 ⟨ξ, ⟨hξC, hne⟩, rfl⟩

theorem exists_isOpen_forall_globalPoints_mem_eq_one :
    ∃ V : Set (GL (Fin 2) (AdeleRing (𝓞 F) F)), IsOpen V ∧ (1 : GL (Fin 2) (AdeleRing (𝓞 F) F)) ∈ V ∧
      ∀ γ₀ : GL (Fin 2) F, AutomorphicForm.globalPoints (𝓞 F) F γ₀ ∈ V → γ₀ = 1 := by
  obtain ⟨U, hUo, h0U, hU⟩ := exists_isOpen_forall_algebraMap_mem_eq_zero F
  let V : Set (GL (Fin 2) (AdeleRing (𝓞 F) F)) :=
    {g | ∀ i j : Fin 2, (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j -
      (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ∈ U}
  have hVo : IsOpen V := by
    have : V = ⋂ i : Fin 2, ⋂ j : Fin 2, (fun g : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) ⁻¹' U := by
      ext g; simp [V]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hUo.preimage ?_
    have hc : Continuous fun g : GL (Fin 2) (AdeleRing (𝓞 F) F) =>
        (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j :=
      (Continuous.matrix_elem Units.continuous_val i j)
    exact hc.sub continuous_const
  refine ⟨V, hVo, ?_, ?_⟩
  · intro i j
    simp only [Units.val_one, sub_self]
    exact h0U
  · intro γ₀ hV
    ext i j
    have h1 := hV i j
    have hval : ((AutomorphicForm.globalPoints (𝓞 F) F γ₀ : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
        algebraMap F (AdeleRing (𝓞 F) F) ((γ₀ : Matrix (Fin 2) (Fin 2) F) i j) := rfl
    rw [hval] at h1
    have h1' : algebraMap F (AdeleRing (𝓞 F) F)
        ((γ₀ : Matrix (Fin 2) (Fin 2) F) i j - (1 : Matrix (Fin 2) (Fin 2) F) i j) ∈ U := by
      rw [map_sub]
      convert h1 using 2
      rcases eq_or_ne i j with rfl | hij
      · simp
      · simp [Matrix.one_apply_ne hij]
    have := hU _ h1'
    rw [sub_eq_zero] at this
    simpa using this

end Discrete

section Setting

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

local notation "AK" => AdeleRing (𝓞 K) K

abbrev inclA : L →+* L ⊗[K] AK := Algebra.TensorProduct.includeLeftRingHom

abbrev MK : Type := Matrix (Fin 2) (Fin 2) (L ⊗[K] AK)

abbrev δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : GL (Fin 2) (L ⊗[K] AK) :=
  Matrix.GeneralLinearGroup.map (inclA K L) δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) c

abbrev Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : Subgroup (GL (Fin 2) (L ⊗[K] AK)) :=
  AutomorphicForm.twistedCentralizer K L AK σ (δA K L δ₀ c)

abbrev Γrat (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) : Subgroup (GL (Fin 2) L) :=
  AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀

abbrev ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : Subgroup (Tw K L σ δ₀ c) :=
  ((Γrat K L σ δ₀).map (Matrix.GeneralLinearGroup.map (inclA K L))).subgroupOf (Tw K L σ δ₀ c)

theorem t2Space_GL (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] :
    T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem locallyCompactSpace_GL (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] : LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L AK σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L AK
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (AutomorphicForm.continuous_sigmaTensor (K := K) (L := L) (A := AK) (σ := σ))

theorem isClosed_Tw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : IsClosed ((Tw K L σ δ₀ c : Subgroup (GL (Fin 2) (L ⊗[K] AK))) : Set (GL (Fin 2) (L ⊗[K] AK))) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L AK
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L AK
  haveI := AutomorphicForm.t2Space_tensorGL K L AK
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] AK) =>
      t * δA K L δ₀ c * (AutomorphicForm.sigmaGL K L AK σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L σ).inv
  have : ((Tw K L σ δ₀ c : Subgroup (GL (Fin 2) (L ⊗[K] AK))) : Set (GL (Fin 2) (L ⊗[K] AK))) =
      (fun t : GL (Fin 2) (L ⊗[K] AK) => t * δA K L δ₀ c * (AutomorphicForm.sigmaGL K L AK σ t)⁻¹) ⁻¹'
        {δA K L δ₀ c} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem secondCountableTopology_tensorGL : SecondCountableTopology (GL (Fin 2) (L ⊗[K] AK)) := by
  haveI := NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo L
  exact (baseChangeGLEquiv K L).toHomeomorph.isEmbedding.secondCountableTopology

theorem baseChangeGL_map_inclA (g : GL (Fin 2) L) :
    baseChangeGLEquiv K L (Matrix.GeneralLinearGroup.map (inclA K L) g) = globalPoints (𝓞 L) L g := by
  rw [baseChangeGLEquiv_apply, baseChangeGL_eq]
  exact (AutomorphicForm.map_genuineRingEquiv_sigmaGL_and_toTensorGL_and_includeLeft K L
    (M4aHerbrand.GenuineDescent.genuineDescentDatum K L)).2.2 g

theorem globalPoints_injective : Function.Injective (AutomorphicForm.globalPoints (𝓞 L) L) := by
  intro a b hab
  ext i j
  have := congrArg (fun g : GL (Fin 2) (AdeleRing (𝓞 L) L) =>
    (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) i j) hab
  exact NumberField.AdeleRing.algebraMap_injective (R := 𝓞 L) (K := L) this

theorem discreteTopology_ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : DiscreteTopology (ΓTw K L σ δ₀ c) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L AK
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L AK
  haveI : IsTopologicalGroup (Tw K L σ δ₀ c) := inferInstance
  haveI : IsTopologicalGroup (ΓTw K L σ δ₀ c) := inferInstance
  obtain ⟨V, hVo, h1V, hV⟩ := exists_isOpen_forall_globalPoints_mem_eq_one L
  apply discreteTopology_of_isOpen_singleton_one

  let f : ΓTw K L σ δ₀ c → GL (Fin 2) (AdeleRing (𝓞 L) L) := fun γ =>
    baseChangeGLEquiv K L (((γ : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AK)))
  have hf : Continuous f :=
    (baseChangeGLEquiv K L).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hpre : f ⁻¹' V = {1} := by
    ext γ
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hγV
      have hγ := γ.2
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hγ
      obtain ⟨g, -, hg⟩ := hγ
      have hfg : f γ = globalPoints (𝓞 L) L g := by
        show baseChangeGLEquiv K L _ = _
        rw [← hg]
        exact baseChangeGL_map_inclA K L g
      rw [hfg] at hγV
      have hg1 : g = 1 := hV g hγV
      subst hg1
      apply Subtype.ext; apply Subtype.ext
      rw [← hg, map_one]
      rfl
    · intro h1
      subst h1
      show baseChangeGLEquiv K L (((1 : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AK))) ∈ V
      rw [OneMemClass.coe_one, map_one]
      exact h1V
  rw [← hpre]
  exact hVo.preimage hf

scoped instance countable_ΓTw (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : Countable (ΓTw K L σ δ₀ c) := by
  haveI : Countable L := (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  haveI : Countable (GL (Fin 2) L) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) L => (g : Matrix (Fin 2) (Fin 2) L))
      fun g h hgh => Units.ext hgh
  haveI : Countable ((Γrat K L σ δ₀).map (Matrix.GeneralLinearGroup.map (inclA K L))) := by
    refine Set.Countable.to_subtype ?_
    exact (Set.countable_range _).mono (by
      rintro x ⟨g, hg, rfl⟩
      exact ⟨g, rfl⟩)
  refine Function.Injective.countable
    (f := fun γ : ΓTw K L σ δ₀ c => (⟨((γ : Tw K L σ δ₀ c) : GL (Fin 2) (L ⊗[K] AK)), γ.2⟩ :
      (Γrat K L σ δ₀).map (Matrix.GeneralLinearGroup.map (inclA K L)))) ?_
  intro a b hab
  have h := congrArg Subtype.val hab
  dsimp only at h
  exact Subtype.ext (Subtype.ext h)

theorem inclA_injective : Function.Injective (inclA K L) := by
  intro l l' h
  have := congrArg (baseChangeEquiv K L) h
  rw [show baseChangeEquiv K L (inclA K L l) = algebraMap L _ l from baseChangeEquiv_tmul_one K L l,
    show baseChangeEquiv K L (inclA K L l') = algebraMap L _ l' from baseChangeEquiv_tmul_one K L l'] at this
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 L) L this

abbrev jM : Matrix (Fin 2) (Fin 2) L →+* MK K L := (inclA K L).mapMatrix

theorem jM_apply (x : Matrix (Fin 2) (Fin 2) L) : jM K L x = x.map (inclA K L) := rfl

theorem coe_map_δ₀ (δ₀ : GL (Fin 2) L) :
    ((Matrix.GeneralLinearGroup.map (inclA K L) δ₀ : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      jM K L (δ₀ : Matrix (Fin 2) (Fin 2) L) := rfl

theorem sigmaTensor_inclA (σ : L ≃ₐ[K] L) (l : L) : sigmaTensor K L AK σ (inclA K L l) = inclA K L (σ l) := by
  simp [sigmaTensor, Algebra.TensorProduct.map_tmul]

theorem map_sigmaTensor_jM (σ : L ≃ₐ[K] L) (x : Matrix (Fin 2) (Fin 2) L) :
    (jM K L x).map (sigmaTensor K L AK σ) = jM K L (x.map σ) := by
  ext i j
  simp only [jM_apply, Matrix.map_apply, sigmaTensor_inclA]

theorem coe_scalarGL (c : (L ⊗[K] AK)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      Matrix.scalar (Fin 2) (c : L ⊗[K] AK) := rfl

theorem map_sigmaTensor_scalar (σ : L ≃ₐ[K] L) (r : L ⊗[K] AK) :
    (Matrix.scalar (Fin 2) r : MK K L).map (sigmaTensor K L AK σ) =
      Matrix.scalar (Fin 2) (sigmaTensor K L AK σ r) := by
  rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]; rfl

theorem scalar_comm (r : L ⊗[K] AK) (X : MK K L) :
    Matrix.scalar (Fin 2) r * X = X * Matrix.scalar (Fin 2) r :=
  (Matrix.scalar_commute r (fun r' => mul_comm r r') X).eq

theorem coe_δA (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) : ((δA K L δ₀ c : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
    jM K L (δ₀ : Matrix (Fin 2) (Fin 2) L) * Matrix.scalar (Fin 2) (c : L ⊗[K] AK) := by
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_map_δ₀, coe_scalarGL]

theorem exists_norm_eq_scalar (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AK)ˣ) (h2 : Module.finrank K L = 2) (u : AKˣ)
    (hN : normString K L AK σ (δA K L δ₀ c) = toTensorGL K L AK (centralScalar (𝓞 K) K u)) :
    ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
  classical
  have hNS : normString K L AK σ (δA K L δ₀ c) = δA K L δ₀ c * sigmaGL K L AK σ (δA K L δ₀ c) := by
    rw [normString, h2]; simp [List.range_succ]
  rw [hNS] at hN
  set M : Matrix (Fin 2) (Fin 2) L :=
    (δ₀ : Matrix (Fin 2) (Fin 2) L) * ((δ₀ : Matrix (Fin 2) (Fin 2) L).map σ) with hM
  set w : L ⊗[K] AK := (c : L ⊗[K] AK) * sigmaTensor K L AK σ c with hw
  have hw_unit : IsUnit w := (c.isUnit).mul ((c.isUnit).map _)
  have hcoe : ((δA K L δ₀ c * sigmaGL K L AK σ (δA K L δ₀ c) : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      jM K L M * Matrix.scalar (Fin 2) w := by
    rw [Matrix.GeneralLinearGroup.coe_mul, coe_sigmaGL, coe_δA, Matrix.map_mul, map_sigmaTensor_jM,
      map_sigmaTensor_scalar, hM, map_mul, hw, map_mul]
    rw [mul_assoc, ← mul_assoc (Matrix.scalar (Fin 2) (c : L ⊗[K] AK)), scalar_comm, mul_assoc,
      mul_assoc]
  have hrhs : ((toTensorGL K L AK (centralScalar (𝓞 K) K u) : GL (Fin 2) (L ⊗[K] AK)) : MK K L) =
      Matrix.scalar (Fin 2) ((1 : L) ⊗ₜ[K] (u : AK)) := by
    change ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) AK) : Matrix (Fin 2) (Fin 2) AK).map
      (Algebra.TensorProduct.includeRight : AK →ₐ[K] L ⊗[K] AK) = _
    change (Matrix.scalar (Fin 2) (u : AK)).map _ = _
    rw [Matrix.scalar_apply, Matrix.diagonal_map (map_zero _)]
    rfl
  have hmat := congrArg (fun g : GL (Fin 2) (L ⊗[K] AK) => (g : MK K L)) hN
  rw [hcoe, hrhs] at hmat
  obtain ⟨wu, hwu⟩ := hw_unit
  have hjM : jM K L M =
      Matrix.scalar (Fin 2) (((1 : L) ⊗ₜ[K] (u : AK)) * ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK)) := by
    have := congrArg (fun X : MK K L => X * Matrix.scalar (Fin 2) ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK)) hmat
    rwa [mul_assoc, ← map_mul, ← map_mul, ← hwu, Units.mul_inv, map_one, mul_one] at this
  have hent : ∀ i k : Fin 2, inclA K L (M i k) = if i = k then
      ((1 : L) ⊗ₜ[K] (u : AK)) * ((wu⁻¹ : (L ⊗[K] AK)ˣ) : L ⊗[K] AK) else 0 := by
    intro i k
    have := congrFun (congrFun hjM i) k
    rw [jM_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply] at this
    exact this
  have h01 : M 0 1 = 0 := inclA_injective K L (by rw [hent, if_neg (by decide), map_zero])
  have h10 : M 1 0 = 0 := inclA_injective K L (by rw [hent, if_neg (by decide), map_zero])
  have h0011 : M 0 0 = M 1 1 := inclA_injective K L (by rw [hent, hent, if_pos rfl, if_pos rfl])
  have hMdet : IsUnit M.det := by
    have : M = ((δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) := by
      rw [Matrix.GeneralLinearGroup.coe_mul]; rfl
    rw [this]
    exact Matrix.isUnits_det_units _
  have hz : M 0 0 ≠ 0 := by
    intro h0
    rw [Matrix.det_fin_two, h0, h01, zero_mul, zero_mul, sub_zero] at hMdet
    exact not_isUnit_zero hMdet
  refine ⟨Units.mk0 (M 0 0) hz, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul]
  change M = ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (M 0 0) hz) : GL (Fin 2) L) :
    Matrix (Fin 2) (Fin 2) L)
  ext i k
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe, Matrix.scalar_apply, Matrix.diagonal_apply, Units.val_mk0]
  fin_cases i <;> fin_cases k <;> simp [h01, h10, h0011]

end Setting

theorem two_mul_two_inv_mul (M : ℝ≥0∞) : 2 * (2⁻¹ * M) = M := by
  rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

end AutomorphicForm.MassDReduce
p2m_reactivate "P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.MassDReduce"
p2m_reactivate "P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

end
p2m_reactivate "P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm.MassDReduce"

p2m_open "MeasureTheory Filter NumberField NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two.AutomorphicForm"

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

set_option maxHeartbeats 6400000 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] AdeleRing (𝓞 K) K)ˣ) (u : (AdeleRing (𝓞 K) K)ˣ)
    (hN : AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) =
      AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K u))
    (hns : ∀ (x : GL (Fin 2) L) (z : Lˣ),
      x⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) x ≠
        Matrix.GeneralLinearGroup.scalar (Fin 2) z)

    (τa' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
      (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτa' : τa'.IsHaarMeasure)
    (τf' : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
      (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))))
    (hτf' : ∀ v, (τf' v).IsHaarMeasure)

    (s : ENNReal)
    (harch :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      ∃ (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              ((AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
              (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τa' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))

    (t : HeightOneSpectrum (𝓞 K) → ENNReal) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (ht : ∀ v ∉ S₀, t v = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K),
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localGLBorel K v
       ∃ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K u)))
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) y ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
              (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))) =>
            y⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y) (τf' v) =
          t v • Measure.map (AutomorphicForm.toTensorGL K L (v.adicCompletion K)) (AutomorphicForm.localHaar K v)) ∨
      ((∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
        ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) ∧
       τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s} *
          (Ideal.absNorm v.asIdeal : ENNReal) =
        t v +
          τf' v {t | ∃ s : (v.adicCompletion K)ˣ, Valued.v (s : v.adicCompletion K) = 1 ∧
            Matrix.GeneralLinearGroup.det (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) =
              Units.map (Algebra.TensorProduct.includeRight :
                v.adicCompletion K →ₐ[K] L ⊗[K] v.adicCompletion K).toRingHom.toMonoidHom s}))

    (τ' : Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (hτ' : τ'.IsHaarMeasure) (cτ' : ℝ) (hcτ' : 0 < cτ')
    (hτ'prod : ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), S₀ ⊆ S →
        ∀ (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => Wa t) τa' →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) => WS v t) (τf' v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂τ' = cτ' * (∫ t, Wa t ∂τa') * ∏ v ∈ S, ∫ t, WS v t ∂(τf' v))

    (R' : ENNReal)
    (hD' : ∀ D' : Set (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      IsFundamentalDomain
        (((AutomorphicForm.sigmaCentralizer
            (Matrix.GeneralLinearGroup.map (σ : L →+* L)) δ₀).map
            (Matrix.GeneralLinearGroup.map
              (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K))).subgroupOf
          (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] AdeleRing (𝓞 K) K) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c))).op D' τ' →
      ∀ a b : ℝ, 0 < a → a ≤ b →
        τ' (D' ∩ {t | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det
            (Matrix.GeneralLinearGroup.map
              (((Algebra.TensorProduct.comm K L (AdeleRing (𝓞 K) K)).toRingEquiv.trans
                (M4aHerbrand.Bridge.genuineRingEquiv K L)).toRingHom)
              (t : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)))) ∈ Set.Icc a b}) =
          R' * ENNReal.ofReal (Real.log (b / a))) :
    2 * R' = ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
      ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
        NumberField.dedekindZeta_residue K) := by
  classical

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.t2Space_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.locallyCompactSpace_tensor K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L (AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.MassDReduce.t2Space_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.MassDReduce.locallyCompactSpace_GL (L ⊗[K] AdeleRing (𝓞 K) K)
  haveI := AutomorphicForm.MassDReduce.secondCountableTopology_tensorGL K L
  haveI : BorelSpace (AutomorphicForm.MassDReduce.Tw K L σ δ₀ c) := ⟨rfl⟩
  have hclosed := AutomorphicForm.MassDReduce.isClosed_Tw K L σ δ₀ c
  haveI : LocallyCompactSpace (AutomorphicForm.MassDReduce.Tw K L σ δ₀ c) :=
    hclosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.MassDReduce.Tw K L σ δ₀ c) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsTopologicalGroup (AutomorphicForm.MassDReduce.Tw K L σ δ₀ c) := inferInstance
  haveI : T2Space (AutomorphicForm.MassDReduce.Tw K L σ δ₀ c) := inferInstance
  haveI : τ'.IsHaarMeasure := hτ'

  haveI : Module.Finite K L := Module.finite_of_finrank_pos (by rw [h2]; norm_num)
  haveI : Algebra.IsQuadraticExtension K L := ⟨h2⟩
  haveI : Algebra.IsSeparable K L := Algebra.IsSeparable.of_integral K L
  haveI : IsGalois K L := inferInstance

  have hτ'r : τ'.IsMulRightInvariant :=
    AutomorphicForm.isMulRightInvariant_twistedCentralizer_adeleRing_of_normString_eq_toTensorGL_centralScalar_of_finrank_eq_two
      K L h2 σ hgen _ u hN τ' hτ'

  have hdisc := AutomorphicForm.MassDReduce.discreteTopology_ΓTw K L σ δ₀ c
  obtain ⟨D₀, hD₀m, -, hD₀all⟩ :=
    MeasureTheory.exists_measurableSet_isFundamentalDomain_op_of_discreteTopology
      (AutomorphicForm.MassDReduce.ΓTw K L σ δ₀ c) hdisc
  have hD₀ := hD₀all τ'

  obtain ⟨C, hC0, hCtop, hCrate⟩ :=
    AutomorphicForm.exists_measure_fundamentalDomain_op_twistedCentralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c u hN hns τ'
  have hlog : ENNReal.ofReal (Real.log (Real.exp 1 / 1)) = 1 := by
    rw [div_one, Real.log_exp, ENNReal.ofReal_one]
  have hR'C : R' = C := by
    have h1 := hD' D₀ hD₀ 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1 : ℝ); linarith)
    have h2' := hCrate D₀ hD₀ 1 (Real.exp 1) one_pos (by have := Real.add_one_le_exp (1 : ℝ); linarith)
    rw [hlog, mul_one] at h1 h2'
    exact h1.symm.trans h2'
  have hR'top : R' ≠ ⊤ := hR'C ▸ hCtop

  have hN₀ : ∃ z : Lˣ, δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) δ₀ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z :=
    AutomorphicForm.MassDReduce.exists_norm_eq_scalar K L σ δ₀ c h2 u hN

  letI : MeasurableSpace (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adeleBorel (𝓞 L) L
  haveI : BorelSpace (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 L) L
  let μ : Measure (AdeleRing (𝓞 L) L) := NumberField.AdelicHaar.adelicAddHaar (𝓞 L) L
  haveI hμ : μ.IsAddHaarMeasure := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 L) L
  have hμpos : μ (adelicBox L) ≠ 0 := (NumberField.AdelicBox.measure_adelicBox_pos L μ).ne'
  have hμtop : μ (adelicBox L) ≠ ⊤ := (NumberField.AdelicBox.measure_adelicBox_lt_top L μ).ne
  let μ₁ : Measure (AdeleRing (𝓞 L) L) := (μ (adelicBox L))⁻¹ • μ
  haveI : μ₁.IsAddHaarMeasure := by
    refine Measure.IsAddHaarMeasure.smul μ ?_ ?_
    · exact ENNReal.inv_ne_zero.2 hμtop
    · exact ENNReal.inv_ne_top.2 hμpos
  have hμ₁ : μ₁ (adelicBox L) = 1 := by
    show (μ (adelicBox L))⁻¹ • μ (adelicBox L) = 1
    rw [smul_eq_mul, ENNReal.inv_mul_cancel hμpos hμtop]
  have hψ : IsGlobalAddChar L (NumberField.StandardAddChar.stdAddChar L) :=
    (NumberField.StandardAddChar.adelicTraceData L).isGlobalAddChar_psiK

  set v₀ : Fin 2 → L := ![1, 0] with hv₀def
  have hv₀ : v₀ ≠ 0 := by
    intro h; have := congrFun h 0; simp [v₀] at this
  obtain ⟨Φ, hΦ, hΦnn, hI0, hItop, hZall, hZ', hlimE⟩ :=
    AutomorphicForm.exists_mem_schwartzBruhat2_tendsto_sub_one_mul_lintegral_twistedCentralizer_nhdsGT_one_of_forall_integral_eq_mul_prod_integral_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c u hN hns τa' hτa' τf' hτf' s harch t S₀ ht hfin τ' hτ' cτ' hcτ' hτ'prod v₀ hv₀ μ₁ hμ₁ hψ

  have hZ2 := hZall 2 one_lt_two
  have hlimT :=
    AutomorphicForm.tendsto_sub_one_mul_lintegral_mul_ideleNorm_det_rpow_twistedCentralizer_nhdsGT_one_of_isFundamentalDomain_of_forall_ne_scalar_of_finrank_eq_two
      K L h2 σ hgen δ₀ c hN₀ hns v₀ hv₀ μ₁ hμ₁ hψ hΦ (fun x => (hΦnn x).1) τ' hτ' hτ'r R' hR'top hD' D₀ hD₀m
      hD₀ 2 one_lt_two (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hZ2) hZ'

  haveI : (𝓝[>] (1 : ℝ)).NeBot := inferInstance
  have heq := tendsto_nhds_unique hlimT hlimE

  set I₀ : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Φ x).re ∂(pairHaar μ₁) with hI₀def
  have hR' : R' = 2⁻¹ * (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) * (∏ v ∈ S₀, t v) *
      ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) * (NumberField.dedekindZeta K 2).re *
        NumberField.dedekindZeta_residue K)) := by
    have h' : I₀ * R' = I₀ * (2⁻¹ * (ENNReal.ofReal cτ' * s * 2 ^ (2 * Module.finrank ℚ K) *
        (∏ v ∈ S₀, t v) * ENNReal.ofReal (((NumberField.discr K : ℝ) ^ 2) *
          (NumberField.dedekindZeta K 2).re * NumberField.dedekindZeta_residue K))) := by
      rw [heq]; ring
    exact (ENNReal.mul_right_inj hI0 hItop).1 h'
  rw [hR']
  exact AutomorphicForm.MassDReduce.two_mul_two_inv_mul _

end S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_two_mul_rate_eq_mul_discr_sq_mul_dedekindZeta_two_mul_residue_of_forall_isFundamentalDomain_twistedCentralizer_inter_ideleNorm_det_Icc_of_forall_ne_scalar_of_finrank_eq_two (solution)
