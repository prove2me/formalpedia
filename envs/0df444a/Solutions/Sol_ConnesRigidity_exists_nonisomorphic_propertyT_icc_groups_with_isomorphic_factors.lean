-- Prove2me | solution 1 for ConnesRigidity.exists_nonisomorphic_propertyT_icc_groups_with_isomorphic_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:10.440282+00:00
-- url     : https://prove2.me/submissions/1a34eb88-a419-4082-8565-aeb9c51516b3

import Mathlib
import Definitions.Def_ConnesRigidity
import Theorems.Thm_ConnesRigidity_FiniteCarry_carry_comm
import Theorems.Thm_ConnesRigidity_FiniteCarry_carry_add_left
import Theorems.Thm_ConnesRigidity_FiniteCarry_carry_add_right
import Theorems.Thm_ConnesRigidity_two_pow_four_injective
import Theorems.Thm_ConnesRigidity_gamma_parameter_eq_of_mulEquiv
import Theorems.Thm_ConnesRigidity_gamma_pairwise_nonisomorphic
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_lambda_propertyT
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_gamma_propertyT
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_lambda_icc
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_gamma_icc
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_gamma_not_isomorphic_lambda
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_toPaperFamilyInput_lambda
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_toPaperFamilyInput_gamma
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_infinitePropertyTFiber_lambda
import Theorems.Thm_ConnesRigidity_PaperAnalyticInput_infinitePropertyTFiber_gamma
attribute [local simp] ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_lambda
attribute [local simp] ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_gamma
attribute [local simp] ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_lambda
attribute [local simp] ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_gamma

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
namespace ConnesRigidity
theorem _root_.solution :
    ∃ Γ Λ : ConnesRigidity.CountableDiscreteGroup.{0},
      Group.FG Γ ∧ Group.FG Λ ∧
      ConnesRigidity.IsICC Γ ∧
      ConnesRigidity.HasKazhdanPropertyT Γ ∧
      ConnesRigidity.IsICC Λ ∧
      ConnesRigidity.HasKazhdanPropertyT Λ ∧
      ConnesRigidity.TracialGroupFactorsIsomorphic Γ Λ ∧
      ¬ConnesRigidity.GroupsIsomorphic Γ Λ := by
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.two_eq_zero_zmod_two
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.StrictPair.{0}
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.BinaryQuadraticPolynomial.{0}
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.BinaryQuadraticPolynomial.mk.{0}
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.BinaryQuadraticPolynomial.constant.{0}
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.BinaryQuadraticPolynomial.linear.{0}
  let _ := @ConnesRigidity.FeedbackBooleanPolynomial.BinaryQuadraticPolynomial.quadratic.{0}
  let _ := @ConnesRigidity.CountableDiscreteGroup.instCoeSortType.{0}
  let _ := @ConnesRigidity.l2Reindex_symm.{0, 0}
  let _ := @ConnesRigidity.unitaryLinearIsometryEquiv_apply.{0}
  let _ := @ConnesRigidity.linearIsometryEquivUnitary_apply.{0}
  let _ := @ConnesRigidity.FiniteIndex.inducedLinearIsometryEquiv_apply.{0}
  let _ := @ConnesRigidity.FiniteIndex.inducedRepresentation_apply.{0}
  let _ := @ConnesRigidity.e_zero
  let _ := @ConnesRigidity.e_apply
  let _ := @ConnesRigidity.square_zero
  let _ := @ConnesRigidity.diagonal_val
  let _ := @ConnesRigidity.polarization_val
  let _ := @ConnesRigidity.truncatePolynomial_apply
  let _ := @ConnesRigidity.truncateVector_apply
  let _ := @ConnesRigidity.instCountableQ
  let _ := @ConnesRigidity.modThreeAtZero_apply
  let _ := @ConnesRigidity.modThreeAtZero_C
  let _ := @ConnesRigidity.modThreeAtZero_X
  let _ := @ConnesRigidity.modThreeGroupHom_apply_entry
  let _ := @ConnesRigidity.modTwoPolynomial_apply
  let _ := @ConnesRigidity.modTwoPolynomial_C
  let _ := @ConnesRigidity.modTwoPolynomial_X
  let _ := @ConnesRigidity.modTwoGroupHom_apply_entry
  let _ := @ConnesRigidity.pi₂_apply
  let _ := @ConnesRigidity.pi₂_apply_entry
  let _ := @ConnesRigidity.constantTermGroupHom_apply_entry
  let _ := @ConnesRigidity.constantTermToLevelThree_apply_coe
  let _ := @ConnesRigidity.finiteGeneratedCosetRepresentation_apply.{0}
  let _ := @ConnesRigidity.suslinEvaluation_entry
  let _ := @ConnesRigidity.suslinConstantSection_entry
  let _ := @ConnesRigidity.localGlobalElementarySubgroup_integralPolynomial
  let _ := @ConnesRigidity.localGlobalElementarySubgroup_integer
  let _ := @ConnesRigidity.LocalElementaryProof.coordinateRotation_smul_right.{0}
  let _ := @ConnesRigidity.LocalElementaryProof.coordinateRotation_smul_other.{0}
  let _ := @ConnesRigidity.MonicMatrixElimination.lowerBlockMatrix_zero_zero.{0}
  let _ := @ConnesRigidity.MonicMatrixElimination.lowerBlockMatrix_succ_zero.{0}
  let _ := @ConnesRigidity.MonicMatrixElimination.lowerBlockMatrix_zero_succ.{0}
  let _ := @ConnesRigidity.MonicMatrixElimination.lowerBlockMatrix_succ_succ.{0}
  let _ := @ConnesRigidity.StabilizedBlockReduction.finTwoPlusOne_symm_castSucc
  let _ := @ConnesRigidity.StabilizedBlockReduction.finTwoPlusOne_symm_last
  let _ := @ConnesRigidity.StabilizedBlockReduction.stabilizedTwoHom_castSucc_last.{0}
  let _ := @ConnesRigidity.StabilizedBlockReduction.stabilizedTwoHom_last_castSucc.{0}
  let _ := @ConnesRigidity.StabilizedBlockReduction.stabilizedTwoHom_last_last.{0}
  let _ := @ConnesRigidity.MennickeIdentity.mennickeBlock_val.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_inv_eq.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_inv_zero_zero.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_inv_zero_one.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_inv_one_zero.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_inv_one_one.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_conjugate_zero_one.{0}
  let _ := @ConnesRigidity.suslinSignedSwap_conjugate_one_zero.{0}
  let _ := @ConnesRigidity.suslinPolynomialDilate_entry
  let _ := @ConnesRigidity.cornulierRoot_val
  let _ := @ConnesRigidity.tensorFunctional_tmul
  let _ := @ConnesRigidity.carry_apply
  let _ := @ConnesRigidity.tensorFunctional_smul_left
  let _ := @ConnesRigidity.tensorFunctional_smul_right
  let _ := @ConnesRigidity.carry_smul_left
  let _ := @ConnesRigidity.carry_smul_right
  let _ := @ConnesRigidity.carryBilinear
  let _ := @ConnesRigidity.carryBilinear_apply
  let _ := @ConnesRigidity.shiftVector_apply
  let _ := @ConnesRigidity.shift_apply
  let _ := @ConnesRigidity.CarryGroup.ext_iff
  let _ := @ConnesRigidity.CarryGroup.zero_linear
  let _ := @ConnesRigidity.CarryGroup.zero_quadratic
  let _ := @ConnesRigidity.CarryGroup.neg_linear
  let _ := @ConnesRigidity.CarryGroup.neg_quadratic
  let _ := @ConnesRigidity.CarryGroup.coefficientFunctional_apply
  let _ := @ConnesRigidity.CarryGroup.shift_coefficientFunctional_e
  let _ := @ConnesRigidity.CarryGroup.orderFourElement_linear
  let _ := @ConnesRigidity.CarryGroup.orderFourElement_quadratic
  let _ := @ConnesRigidity.binaryRootsEquiv_apply
  let _ := @ConnesRigidity.binaryRootsEquiv_val
  let _ := @ConnesRigidity.continuousBinaryBidual.{0}
  let _ := @ConnesRigidity.continuousBinaryBidualEvaluation.{0}
  let _ := @ConnesRigidity.continuousBinaryBidualEvaluation_apply.{0}
  let _ := @ConnesRigidity.continuousBinaryBidualEquiv.{0}
  let _ := @ConnesRigidity.continuousBinaryBidualEquiv_apply.{0}
  let _ := @ConnesRigidity.pointwiseEvaluationCharacter_apply.{0}
  let _ := @ConnesRigidity.pointwiseEvaluationHom_apply.{0}
  let _ := @ConnesRigidity.pointwisePontryaginDualEquiv_symm_apply.{0}
  let _ := @ConnesRigidity.FiniteCarry.Point
  let _ := @ConnesRigidity.FiniteCarry.carry_zero_left
  let _ := @ConnesRigidity.FiniteCarry.carry_zero_right
  let _ := @ConnesRigidity.FiniteCarry.carry_comm
  let _ := @ConnesRigidity.FiniteCarry.carry_add_left
  let _ := @ConnesRigidity.FiniteCarry.carry_add_right
  let _ := @ConnesRigidity.FiniteCarry.Carry.ext_iff
  let _ := @ConnesRigidity.FiniteCarry.Carry.zero_low
  let _ := @ConnesRigidity.FiniteCarry.Carry.zero_high
  let _ := @ConnesRigidity.FiniteCarry.Carry.add_low
  let _ := @ConnesRigidity.FiniteCarry.Carry.add_high
  let _ := @ConnesRigidity.FiniteCarry.Carry.neg_low
  let _ := @ConnesRigidity.FiniteCarry.Carry.neg_high
  let _ := @ConnesRigidity.FiniteCarry.Carry.pointEquiv
  let _ := @ConnesRigidity.FiniteCarry.Carry.pointEquiv_apply
  let _ := @ConnesRigidity.FiniteCarry.Carry.codeEquiv_apply
  let _ := @ConnesRigidity.FiniteCarry.Carry.codeEquiv_symm_apply
  let _ := @ConnesRigidity.FiniteCarry.Carry.exponent_four
  let _ := @ConnesRigidity.FiniteCarry.Carry.card
  let _ := @ConnesRigidity.CarryGroup.pointEvaluation_low
  let _ := @ConnesRigidity.CarryGroup.pointEvaluation_high
  let _ := @ConnesRigidity.CarryGroup.evalFour_orderFourElement
  let _ := @ConnesRigidity.fourthRootCharacter_apply
  let _ := @ConnesRigidity.fourthRootCharacter_zero
  let _ := @ConnesRigidity.pontryaginDual_one_apply.{0}
  let _ := @ConnesRigidity.evalFourContinuous_apply
  let _ := @ConnesRigidity.fourthRootCharacter.comp_apply.{0}
  let _ := @ConnesRigidity.dualAction_apply.{0, 0}
  let _ := @ConnesRigidity.rho
  let _ := @ConnesRigidity.rho_apply
  let _ := @ConnesRigidity.carryKernelInclusion_linear
  let _ := @ConnesRigidity.carryKernelInclusion_quadratic
  let _ := @ConnesRigidity.carryPullback_linear
  let _ := @ConnesRigidity.carryPullback_quadratic
  let _ := @ConnesRigidity.shiftKernelInclusion_linear
  let _ := @ConnesRigidity.shiftKernelInclusion_quadratic
  let _ := @ConnesRigidity.shiftSection_apply
  let _ := @ConnesRigidity.carryPullbackSection_linear
  let _ := @ConnesRigidity.carryPullbackSection_quadratic
  let _ := @ConnesRigidity.carryPullbackContinuous_apply
  let _ := @ConnesRigidity.carryPullbackSectionContinuous_apply
  let _ := @ConnesRigidity.carryPullbackContinuous_section_apply
  let _ := @ConnesRigidity.kernelProjection_apply_coe
  let _ := @ConnesRigidity.kernelProjectionContinuous_apply
  let _ := @ConnesRigidity.shiftKernelInclusionContinuous_apply
  let _ := @ConnesRigidity.kernelProjectionContinuous_inclusion_apply
  let _ := @ConnesRigidity.d_polarization
  let _ := @ConnesRigidity.binaryRootCharacter_apply
  let _ := @ConnesRigidity.carryLinearEvaluation_apply
  let _ := @ConnesRigidity.carryLinearEvaluationContinuous_apply
  let _ := @ConnesRigidity.iotaCharacter_apply
  let _ := @ConnesRigidity.quadraticInclusionContinuous_apply
  let _ := @ConnesRigidity.quadraticRestriction_apply
  let _ := @ConnesRigidity.quadraticCharacter_apply
  let _ := @ConnesRigidity.quadraticPairing_apply
  let _ := @ConnesRigidity.linearSection_linear
  let _ := @ConnesRigidity.linearSection_quadratic
  let _ := @ConnesRigidity.linearSection_zero
  let _ := @ConnesRigidity.kernelCharacter_apply
  let _ := @ConnesRigidity.sigma_epsilon
  let _ := @ConnesRigidity.carryCoordinatesMeasurableEquiv_apply
  let _ := @ConnesRigidity.carryComplexCharacter_apply
  let _ := @ConnesRigidity.carryFourierBasis_coe
  let _ := @ConnesRigidity.carryBidualEvaluation_apply
  let _ := @ConnesRigidity.splitBinaryEvaluation_apply
  let _ := @ConnesRigidity.splitPontryaginCharacter_apply
  let _ := @ConnesRigidity.splitComplexCharacter_apply
  let _ := @ConnesRigidity.splitFourierBasis_coe
  let _ := @ConnesRigidity.HaarProbabilityAction.haar.{0, 0}
  let _ := @ConnesRigidity.HaarProbabilityAction.action_add.{0, 0}
  let _ := @ConnesRigidity.EquivariantHaarEquiv.refl.{0, 0}
  let _ := @ConnesRigidity.EquivariantHaarEquiv.trans.{0, 0, 0, 0}
  let _ := @ConnesRigidity.CrossedProductModel.trace.{0}
  let _ := @ConnesRigidity.kLinear_apply
  let _ := @ConnesRigidity.kTensorLinear_tmul
  let _ := @ConnesRigidity.kDividedSquareLinear_polarization
  let _ := @ConnesRigidity.kDLinear_apply
  let _ := @ConnesRigidity.kDAction_toAdd
  let _ := @ConnesRigidity.Lambda_mul_right
  let _ := @ConnesRigidity.lambdaProjection_inl
  let _ := @ConnesRigidity.lambdaProjection_inr
  let _ := @ConnesRigidity.InfinitePropertyTFiber.exact_index_embeddings.{0}
  let _ := @ConnesRigidity.InfinitePropertyTFiber.commensurable.{0}
  let _ := @ConnesRigidity.kCarryAddAut_linear
  let _ := @ConnesRigidity.kCarryAddAut_quadratic
  let _ := @ConnesRigidity.kCarryAction_linear
  let _ := @ConnesRigidity.kCarryAction_quadratic
  let _ := @ConnesRigidity.paperSplitAddAut_apply
  let _ := @ConnesRigidity.paperSplitAddAut_symm_apply
  let _ := @ConnesRigidity.kCarryAddAut_symm_apply
  let _ := @ConnesRigidity.crossedFiberwiseOperator_apply.{0, 0}
  let _ := @ConnesRigidity.crossedMultiplier_apply.{0, 0}
  let _ := @ConnesRigidity.crossedFiberwiseEquiv_apply.{0, 0, 0}
  let _ := @ConnesRigidity.crossedIndexEquiv_apply.{0, 0}
  let _ := @ConnesRigidity.crossedBaseHaarEquiv_apply.{0, 0, 0}
  let _ := @ConnesRigidity.crossedActionL2Equiv_apply.{0, 0}
  let _ := @ConnesRigidity.crossedGroupUnitary_apply.{0, 0}
  let _ := @ConnesRigidity.crossedHaarHilbertEquiv_apply.{0, 0, 0}
  let _ := @ConnesRigidity.carryEAddAction_apply
  let _ := @ConnesRigidity.crossedOperatorBlock_apply.{0, 0}
  let _ := @ConnesRigidity.dualCharacterAction_trivial.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.mk.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_empty.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_univ.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_inter.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_self_adjoint.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_iUnion.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.scalar.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.scalar_apply.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.projection_covariance.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.scalar_covariance.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.kernel_eigenprojection.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.energy_identity.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.scalar_univ_real.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.scalar_isProbabilityMeasure.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.probabilityMeasure.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.probabilityMeasure_invariant.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.probabilityMeasure_energy.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.trivialProjection_ne_zero_of_atom_pos.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.trivialProjection_kernel_fixed.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.trivialProjection_quotient_fixed.{0}
  let _ := @ConnesRigidity.ProjectionValuedSpectralMeasure.positive_atom_invariant.{0}
  let _ := @ConnesRigidity.quotientFixedOrthogonalIsometry_apply.{0}
  let _ := @ConnesRigidity.quotientFixedOrthogonalRepresentation_apply.{0}
  let _ := @ConnesRigidity.spectralUnitTest_apply.{0}
  let _ := @ConnesRigidity.spectralEnergyTest_apply.{0}
  let _ := @ConnesRigidity.PositiveSpectralFunctional.probabilityMeasure_toMeasure.{0}
  let _ := @ConnesRigidity.spectralFiniteAverageTest_apply.{0, 0}
  let _ := @ConnesRigidity.spectralKernelOperator_coe.{0}
  let _ := @ConnesRigidity.spectralCharacter_apply_coe.{0}
  let _ := @ConnesRigidity.spectralCharacterEvaluation_apply.{0}
  let _ := @ConnesRigidity.dualCharacterHomeomorph_apply.{0}
  let _ := @ConnesRigidity.quotientSpectralOperatorConjugation_coe.{0}
  let _ := @ConnesRigidity.dualCharacterActionContinuousMap_apply.{0}
  let _ := @ConnesRigidity.characterRealSqrt_apply.{0}
  let _ := @ConnesRigidity.characterVectorFunctionalLinear_apply.{0, 0}
  let _ := @ConnesRigidity.characterVectorFunctional_apply.{0, 0}
  let _ := @ConnesRigidity.jointCharacterFunctional_apply.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.mk.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.shears.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.translations.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.gap.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.gap_pos.{0}
  let _ := @ConnesRigidity.RelativeFourierAtomCertificate.positive_atom.{0}
  let _ := @ConnesRigidity.affineFixedSet.{0}
  let _ := @ConnesRigidity.mem_affineFixedSet.{0}
  let _ := @ConnesRigidity.affineLinearRepresentation_apply.{0}
  let _ := @ConnesRigidity.mem_affineLinearStabilizer.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.EquivariantHilbertKernelRealization.mk.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.EquivariantHilbertKernelRealization.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.EquivariantHilbertKernelRealization.realization.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.EquivariantHilbertKernelRealization.representation.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.EquivariantHilbertKernelRealization.equivariant.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.equivariantPairCocycle.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.equivariantPairCocycle_mul.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.unitaryCocycleAffineAction_apply.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.equivariantPairAffineAction.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.equivariantPairAffineAction_apply.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.equivariantPairAffineAction_apply_zero.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.markedOrbitAction_apply.{0}
  let _ := @ConnesRigidity.normalFixedLinearIsometryEquiv.{0}
  let _ := @ConnesRigidity.normalFixedRepresentation.{0}
  let _ := @ConnesRigidity.normalFixedRepresentation_apply.{0}
  let _ := @ConnesRigidity.normalFixedRepresentation_apply_eq_one.{0}
  let _ := @ConnesRigidity.normalFixedQuotientRepresentation.{0}
  let _ := @ConnesRigidity.normalFixedQuotientRepresentation_apply_mk.{0}
  let _ := @ConnesRigidity.normalFixedOrthogonalRepresentation_apply.{0}
  let _ := @ConnesRigidity.diagonalDisplacement_apply.{0}
  let _ := @ConnesRigidity.diagonalLinearIsometryHom_apply.{0}
  let _ := @ConnesRigidity.CornulierUltralimit.entrywisePow_apply.{0}
  let _ := @ConnesRigidity.gaussianKernel_apply.{0}
  let _ := @ConnesRigidity.gaussianAffineKernel.{0}
  let _ := @ConnesRigidity.gaussianAffineKernel_apply.{0}
  let _ := @ConnesRigidity.HasUniformRelativeKazhdanDisplacement.mono.{0}
  let _ := @ConnesRigidity.cornulierHilbertLength_one.{0}
  let _ := @ConnesRigidity.IsAffineFixed.affineInvariantOrthogonalProjection.{0}
  let _ := @ConnesRigidity.shalomCircleMeasurable
  let _ := @ConnesRigidity.shalomCircleBorel
  let _ := @ConnesRigidity.integerDualMeasurable
  let _ := @ConnesRigidity.integerDualBorel
  let _ := @ConnesRigidity.integerShalomTranslation_zero_one
  let _ := @ConnesRigidity.integerShalomTranslation_one_one
  let _ := @ConnesRigidity.integerShearDualMeasurable
  let _ := @ConnesRigidity.integerShearDualBorel
  let _ := @ConnesRigidity.shalomTorusCircleMeasurable
  let _ := @ConnesRigidity.shalomTorusCircleBorel
  let _ := @ConnesRigidity.ShalomTorus
  let _ := @ConnesRigidity.torusShearTpos
  let _ := @ConnesRigidity.torusShearSpos
  let _ := @ConnesRigidity.torusShearTneg
  let _ := @ConnesRigidity.torusShearSneg
  let _ := @ConnesRigidity.torusShearTpos_apply
  let _ := @ConnesRigidity.torusShearSpos_apply
  let _ := @ConnesRigidity.torusShearTneg_apply
  let _ := @ConnesRigidity.torusShearSneg_apply
  let _ := @ConnesRigidity.torusShearTpos_symm
  let _ := @ConnesRigidity.torusShearSpos_symm
  let _ := @ConnesRigidity.torusShearTneg_symm
  let _ := @ConnesRigidity.torusShearSneg_symm
  let _ := @ConnesRigidity.atomIntegerDualMeasurable
  let _ := @ConnesRigidity.atomIntegerDualBorel
  let _ := @ConnesRigidity.integerTranslationZero_eq_dualCoordinate
  let _ := @ConnesRigidity.integerTranslationOne_eq_dualCoordinate
  let _ := @ConnesRigidity.polynomialSequenceTail_apply
  let _ := @ConnesRigidity.polynomialCharacterCoefficients_apply
  let _ := @ConnesRigidity.mem_polynomialCharacterNoFree
  let _ := @ConnesRigidity.shalomPolynomial_negX_mul_X_pow
  let _ := @ConnesRigidity.shalomConstantVector_apply
  let _ := @ConnesRigidity.shalomConstantSpecialLinear_apply
  let _ := @ConnesRigidity.shalomConstantActing_apply
  let _ := @ConnesRigidity.isProjectionSupremum_image_starAlgEquiv.{0, 0}
  let _ := @ConnesRigidity.starAlgEquiv_isNormal.{0, 0}
  let _ := @ConnesRigidity.characterBitLinear_apply
  let _ := @ConnesRigidity.dualToPair_linear_apply
  let _ := @ConnesRigidity.dualToPair_quadratic_apply
  let _ := @ConnesRigidity.pairToDual_apply
  let _ := @ConnesRigidity.pairDualHomeomorph_apply
  let _ := @ConnesRigidity.pairDualHomeomorph_symm_apply
  let _ := @ConnesRigidity.dualCarryPullback_apply
  let _ := @ConnesRigidity.shiftKernelRestriction_apply
  let _ := @ConnesRigidity.gammaEmbedding_left
  let _ := @ConnesRigidity.gammaEmbedding_right
  let _ := @ConnesRigidity.kEAddAction_apply
  let _ := @ConnesRigidity.doubleIntoTwoTorsion_val.{0}
  let _ := @ConnesRigidity.twoTorsionEquiv.{0, 0}
  let _ := @ConnesRigidity.twoTorsionEquiv_val.{0, 0}
  let _ := @ConnesRigidity.twoTorsionEquiv_map_doubled.{0, 0}
  let _ := @ConnesRigidity.twoTorsionQuotientEquiv.{0, 0}
  let _ := @ConnesRigidity.ExponentFourExtension.iotaIntoTwoTorsion_val.{0, 0, 0}
  let _ := @ConnesRigidity.twoTorsion_smul_val.{0, 0}
  let _ := @ConnesRigidity.mem_finiteOrbitSubgroup.{0, 0}
  let _ := @ConnesRigidity.orbit_image_eq_of_equivariant.{0, 0, 0, 0}
  let _ := @ConnesRigidity.finiteOrbit_iff_of_equivariant.{0, 0, 0, 0}
  let _ := @ConnesRigidity.finiteOrbitSubgroupEquiv.{0, 0, 0, 0}
  let _ := @ConnesRigidity.finiteOrbitSubgroupEquiv_val.{0, 0, 0, 0}
  let _ := @ConnesRigidity.twoTorsionQuotientEquiv_mk.{0, 0}
  let _ := @ConnesRigidity.ExponentFourExtension.sigmaIntoRetractionKer_val.{0, 0, 0}
  let _ := @ConnesRigidity.ExponentFourExtension.quotientIotaBase_apply.{0, 0, 0}
  let _ := @ConnesRigidity.ExponentFourExtension.quotientSigmaToB_apply.{0, 0, 0}
  let _ := @ConnesRigidity.two_pow_four_injective
  let _ := @ConnesRigidity.intrinsicConjugationAut_mk.{0}
  let _ := @ConnesRigidity.intrinsicRestrictedEquiv_apply_val.{0, 0}
  let _ := @ConnesRigidity.intrinsicSubquotientEquiv_mk.{0, 0}
  let _ := @ConnesRigidity.semidirectTwoTorsionInl_apply.{0, 0}
  let _ := @ConnesRigidity.semidirectTwoTorsionInclusionEquiv_apply_val.{0, 0}
  let _ := @ConnesRigidity.primitiveCount_zero
  let _ := @ConnesRigidity.polynomialVectorVal_apply
  let _ := @ConnesRigidity.IsPrimitiveVector.ne_zero
  let _ := @ConnesRigidity.divX_X_mul_add_C
  let _ := @ConnesRigidity.coeff_zero_X_mul_add_C
  let _ := @ConnesRigidity.linearDetectorAt
  let _ := @ConnesRigidity.quadraticDetectorAt
  let _ := @ConnesRigidity.kDLinear_linearDetectorAt
  let _ := @ConnesRigidity.kDLinear_quadraticDetectorAt
  let _ := @ConnesRigidity.boundedVectorLinearDirect_apply
  let _ := @ConnesRigidity.dualPointAction_linear
  let _ := @ConnesRigidity.dualPointAction_quadratic
  let _ := @ConnesRigidity.homeomorphPushProbability_toMeasure.{0, 0}
  let _ := @ConnesRigidity.l2Curry_apply.{0, 0}
  let _ := @ConnesRigidity.l2Curry_symm_apply.{0, 0}
  let _ := @ConnesRigidity.semidirectFubiniCoordinates_apply.{0, 0}
  let _ := @ConnesRigidity.semidirectFubini_symm_apply.{0, 0}
  let _ := @ConnesRigidity.semidirectFubini_conj_leftRegular_apply.{0, 0}
  let _ := @ConnesRigidity.semidirectFubini_leftRegular_inl.{0, 0}
  let _ := @ConnesRigidity.semidirectFubini_leftRegular_inr.{0, 0}
  let _ := @ConnesRigidity.normalFourierCoordinates_apply.{0, 0, 0}
  let _ := @ConnesRigidity.normalFourierCoordinates_symm_apply.{0, 0, 0}
  let _ := @ConnesRigidity.PaperFactorUnitaryWitness.toStarAlgEquiv_coe.{0, 0}
  let _ := @ConnesRigidity.spectralPairProbability_toMeasure
  let _ := @ConnesRigidity.paperVectorDistribMulAction
  let _ := @ConnesRigidity.paperVector_smul
  let _ := @ConnesRigidity.paperDividedSquare_smul
  let _ := @ConnesRigidity.paperDual_smul
  let _ := @ConnesRigidity.paperDual_smul_toAdd
  let _ := @ConnesRigidity.paperDual_smul_ofAdd
  let _ := @ConnesRigidity.gamma_parameter_eq_of_mulEquiv
  let _ := @ConnesRigidity.gamma_pairwise_nonisomorphic
  let _ := @ConnesRigidity.PaperAnalyticInput.lambda_propertyT
  let _ := @ConnesRigidity.PaperAnalyticInput.gamma_propertyT
  let _ := @ConnesRigidity.PaperAnalyticInput.lambda_icc
  let _ := @ConnesRigidity.PaperAnalyticInput.gamma_icc
  let _ := @ConnesRigidity.PaperAnalyticInput.gamma_not_isomorphic_lambda
  let _ := @ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_lambda
  let _ := @ConnesRigidity.PaperAnalyticInput.toPaperFamilyInput_gamma
  let _ := @ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_lambda
  let _ := @ConnesRigidity.PaperAnalyticInput.infinitePropertyTFiber_gamma
  let F := manuscriptInfinitePropertyTFiber
  refine ⟨F.Gamma 0, F.Lambda, F.gamma_fg 0, F.lambda_fg,
    F.gamma_icc 0, F.gamma_propertyT 0, F.lambda_icc,
    F.lambda_propertyT, F.factors_isomorphic 0, ?_⟩
  rintro ⟨e⟩
  exact F.lambda_not_isomorphic 0 ⟨e.symm⟩
end ConnesRigidity
