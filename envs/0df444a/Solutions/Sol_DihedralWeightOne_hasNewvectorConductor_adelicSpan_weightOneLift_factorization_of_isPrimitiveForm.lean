-- Prove2me | solution 1 for DihedralWeightOne.hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/89ccda89-c99a-51b2-8b92-6ecf3296f7f1

import Mathlib
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Definitions.Def_LocalNewvector_ConductorDatum
import Definitions.Def_LocalNewvector_AdelicSpanCarrier
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization
import Theorems.Thm_DihedralWeightOne_weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm
import Theorems.Thm_LocalNewvector_AdelicSpan_exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
import Theorems.Thm_DihedralWeightOne_factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
p2m_attr_erase "instance" "instCountableOfNumberField_definitions HeckeIntegralSeam.finite_padicInt_quotient_span_p Deep.NTSupply.instNormalRayClassSubgroup LocalNewvector.PSCarrier.instModuleComplex LocalNewvector.PSCarrier.instAddCommGroup LocalNewvector.PSCarrier.instSMulCommClassGeneralLinearGroupFinOfNatNatPadicComplex LocalNewvector.PSCarrier.instDistribMulActionGeneralLinearGroupFinOfNatNatPadic FLT.SpectralSide.instCompactSpaceMatrix instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.whittakerCoefficient_zero NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalNewvector.coe_borelElem LocalNewvector.halfModulus_one LocalNewvector.borelElem_one LocalNewvector.PSCarrier.toFn_csmul LocalNewvector.PSCarrier.toFn_smul LocalNewvector.coe_borelElem_inv FreyPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "FreyPackage.mk.injEq AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat"

set_option autoImplicit false

open NumberField AutomorphicForm DihedralWeightOne IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem solution
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] :
    LocalNewvector.HasNewvectorConductor q
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))
      (N.factorization q) := by
  obtain ⟨hne, hlev⟩ := DihedralWeightOne.weightOneLift_ne_zero_and_apply_mul_finEmbed_eq_of_isPrimitiveForm N ψ f hf
  obtain ⟨c, hce, hc⟩ :=
    LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization _ hne (NeZero.ne N) hlev q
  rcases Nat.lt_or_eq_of_le hce with hlt | heq
  · exfalso
    obtain ⟨y, hy, hy0, hfix⟩ :=
      LocalNewvector.AdelicSpan.exists_mem_span_fixed_padicK1_of_fixedSubmodule_padicK1_ne_bot_of_apply_mul_finEmbed_eq
        _ (NeZero.ne N) hlev q c hc.1
    have hle := DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1
      N ψ f hf q c y hy hfix hy0
    exact absurd hle (not_le.mpr hlt)
  · rw [← heq]
    exact hc

end S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
end P2MW
export P2MW.S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm (solution)
