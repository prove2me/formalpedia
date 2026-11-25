-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.padic_stationary_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:43.625809+00:00
-- url     : https://prove2.me/submissions/b3983a95-bc40-4030-a0ce-79b2470140c5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelProperties
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondVanishingOffRing
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialMeansOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PosSemidefEntryBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanPositiveSemidefinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteClassesPositiveSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanNormSquaredBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealPowerIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermExpansionOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermExpansionMatrixFunction
import Theorems.Thm_Formalism_FourierDecayAlt_P_gauss_hessian_index_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_added_block_kernel_block_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_added_block_kernel_support
import Theorems.Thm_Formalism_FourierDecayAlt_P_admissible_gauss_sum_small
import Theorems.Thm_Formalism_FourierDecayAlt_P_annihilatorCharacters
import Theorems.Thm_Formalism_FourierDecayAlt_P_averageBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_averaged_kernel_parseval
import Theorems.Thm_Formalism_FourierDecayAlt_P_averaged_kernel_periodic_psd
import Theorems.Thm_Formalism_FourierDecayAlt_P_averaged_vector_choices_exist
import Theorems.Thm_Formalism_FourierDecayAlt_P_averaged_vector_norm_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_boundedSubsequence
import Theorems.Thm_Formalism_FourierDecayAlt_P_characterMean
import Theorems.Thm_Formalism_FourierDecayAlt_P_characterOrthogonality
import Theorems.Thm_Formalism_FourierDecayAlt_P_characterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_cokernel_card_inverse_modulus
import Theorems.Thm_Formalism_FourierDecayAlt_P_compactOpenChoice
import Theorems.Thm_Formalism_FourierDecayAlt_P_crossTermsVanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_cut_posSemidef
import Theorems.Thm_Formalism_FourierDecayAlt_P_doubleMeanSplit
import Theorems.Thm_Formalism_FourierDecayAlt_P_finite_family_truncation_module
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_kernel_explicit_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_kernel_gram_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_kernel_parseval
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_kernel_periodic
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_theta_equals_first_kernel
import Theorems.Thm_Formalism_FourierDecayAlt_P_first_theta_kernel_equality
import Theorems.Thm_Formalism_FourierDecayAlt_P_gauss_index_independent_of_choice
import Theorems.Thm_Formalism_FourierDecayAlt_P_gauss_sum_modulus_of_lattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_gramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_gramRealisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_gram_equality_of_vectors
import Theorems.Thm_Formalism_FourierDecayAlt_P_head_reduction_lemma
import Theorems.Thm_Formalism_FourierDecayAlt_P_head_size_add_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_head_size_one_in_GL
import Theorems.Thm_Formalism_FourierDecayAlt_P_heads_distinct_determinant_orthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_field_refinement
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_lattice_refinement_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_integral_points_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_kernel_as_coset_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_kernel_block_diagonal_by_modulus
import Theorems.Thm_Formalism_FourierDecayAlt_P_kernel_gram_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_lattice_average_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_lattice_family_finite
import Theorems.Thm_Formalism_FourierDecayAlt_P_modulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_modulus_positive_multiplicative
import Theorems.Thm_Formalism_FourierDecayAlt_P_morseLemma
import Theorems.Thm_Formalism_FourierDecayAlt_P_nonStationary
import Theorems.Thm_Formalism_FourierDecayAlt_P_orbital_integral_change_of_variables
import Theorems.Thm_Formalism_FourierDecayAlt_P_orthogonalMeanNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_orthogonal_lattice_properties
import Theorems.Thm_Formalism_FourierDecayAlt_P_oscillatory_integral_invariant
import Theorems.Thm_Formalism_FourierDecayAlt_P_padic_change_of_variables
import Theorems.Thm_Formalism_FourierDecayAlt_P_parsevalGroup_statement
import Theorems.Thm_Formalism_FourierDecayAlt_P_partialMeansOrthogonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_phase_difference_estimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_phase_hessian_determinant
import Theorems.Thm_Formalism_FourierDecayAlt_P_phase_locally_constant
import Theorems.Thm_Formalism_FourierDecayAlt_P_posSemidefClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_posSemidefEntryBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootCorrection
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootCutStable
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootStableExhaustion
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootsFinite
import Theorems.Thm_Formalism_FourierDecayAlt_P_rootsSeparated
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_gram_and_vanishing
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_gram_property
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_vanishing_off_ring
import Theorems.Thm_Formalism_FourierDecayAlt_P_shiftSmall_statement
import Theorems.Thm_Formalism_FourierDecayAlt_P_shiftUnit_statement
import Theorems.Thm_Formalism_FourierDecayAlt_P_smallModules
import Theorems.Thm_Formalism_FourierDecayAlt_P_smallUnits
import Theorems.Thm_Formalism_FourierDecayAlt_P_square_near_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_stationaryPhaseOfSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_thetaAverageLower
import Theorems.Thm_Formalism_FourierDecayAlt_P_tripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_triple_form_end_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_truncated_average_norm_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_volume_scaling_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_zero_kernel_all_ones


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A6.StationaryPhase := by
  have h := stationaryPhaseOfSteps
  unfold Formalism.FourierDecayAlt.A6.StationaryAssemble at h
  apply h <;> clear h <;> try (first
      | exact a6x_kpGram_proof
      | exact kernel_gram_property
      | exact a6x_modMul_proof
      | exact modulus_positive_multiplicative
      | exact a6x_tripleForm_proof
      | exact tripleForm
      | exact a6x_avgClaim_proof
      | exact lattice_average_identity
      | exact a6x_tTEnd_proof
      | exact triple_form_end_identity
      | exact a6x_a2_proof
      | exact second_gram_and_vanishing
      | exact a6x_n1Formula_proof
      | exact first_kernel_explicit_formula
      | exact a6x_intFinite_proof
      | exact integral_points_finite
      | exact a6x_charOrthDual_proof
      | exact characterOrthogonalityDual
      | exact a6x_charOrth_proof
      | exact characterOrthogonality
      | exact a6x_cokerCard_proof
      | exact cokernel_card_inverse_modulus
      | exact a6x_a2Gram_proof
      | exact second_gram_property
      | exact a6x_n1Periodic_proof
      | exact first_kernel_periodic
      | exact a6x_n1Gram_proof
      | exact first_kernel_gram_property
      | exact a6x_n1Parseval_proof
      | exact first_kernel_parseval
      | exact a6x_nsSupport_proof
      | exact added_block_kernel_support
      | exact a6x_nsBlockDiag_proof
      | exact added_block_kernel_block_diagonal
      | exact a6x_n0Ones_proof
      | exact zero_kernel_all_ones
      | exact a6x_th1Eq_proof
      | exact first_theta_kernel_equality
      | exact a6x_a13OneEq_proof
      | exact first_theta_equals_first_kernel
      | exact a6x_a13Step_proof
      | exact lattice_average_induction
      | exact a6x_lemmaA_proof
      | exact lattice_average_lemma_full
      | exact doubleMeanSplit
      | exact a5x_meanSplit_proof
      | exact partialMeansOrthogonal
      | exact a5x_pOrth_proof
      | exact orthogonalMeanNorm
      | exact a5x_orthNorm_proof
      | exact averageBound
      | exact a5x_avgBound_proof
      | exact gauss_sum_modulus_of_lattice
      | exact a5x_gaussModulus_proof
      | exact gauss_index_independent_of_choice
      | exact a5x_gaussIndep_proof
      | exact phase_hessian_determinant
      | exact a5x_hessDet_proof
      | exact volume_scaling_identity
      | exact a5x_volScale_proof
      | exact gauss_hessian_index_exists
      | exact a5x_gaussHess_proof
      | exact admissible_gauss_sum_small
      | exact a5x_gaussAdmSmall_proof
      | exact gramRealisation
      | exact gram_realise_cut
      | exact solution
      | exact a5x_stationaryPhase_proof
      | exact germ_expansion_matrix_function
      | exact a5x_germPhi_proof
      | exact germ_expansion_with_head
      | exact a5x_germ_proof
      | exact germ_kernel_expansion
      | exact a5x_germKernel_proof
      | exact germ_identity_bis
      | exact a5x_germIdentity_proof
      | exact theta_omega_bound
      | exact a5x_thOm_proof
      | exact nonStationary
      | exact a5x_nonStationary_proof
      | exact morseLemma
      | exact a5x_morseLemma_proof
      | exact integral_field_refinement
      | exact a5x_intKRefine_proof
      | exact rootsFinite
      | exact a5x_rootsFinite_proof
      | exact compactOpenChoice
      | exact a5x_latChoice_proof
      | exact orthogonal_lattice_properties
      | exact a5x_perpLat_proof
      | exact modulusLocallyConstant
      | exact a5x_modLocConst_proof
      | exact oscillatory_integral_invariant
      | exact a5x_oscInvariant_proof
      | exact rootsSeparated
      | exact a5x_rootsSeparated_proof
      | exact smallModules
      | exact a5x_smallModules_proof
      | exact lattice_family_finite
      | exact a5x_latFinite_proof
      | exact finite_family_truncation_module
      | exact a5x_supportModule_proof
      | exact head_size_one_in_GL
      | exact a5x_cSizeOne_proof
      | exact rootStableExhaustion
      | exact a5x_exhaust_proof
      | exact posSemidefEntryBound
      | exact a5x_pSDEntryBound_proof
      | exact posSemidefClosed
      | exact a5x_pSDClosed_proof
      | exact boundedSubsequence
      | exact a5x_boundedSubseq_proof
      | exact parsevalGroup_statement
      | exact a5x_parsevalGroup_proof
      | exact orbital_integral_change_of_variables
      | exact a5x_oscReduction_proof
      | exact head_reduction_lemma
      | exact a5x_headReduction_proof
      | exact kernel_as_coset_sum
      | exact a5x_kpFromBB_proof
      | exact gramKernelHermitian
      | exact a5x_kpHerm_proof
      | exact a6x_a2Vanish_proof
      | exact second_vanishing_off_ring
      | exact shiftUnit_statement
      | exact a5x_shiftUnit_proof
      | exact shiftSmall_statement
      | exact a5x_shiftSmall_proof
      | exact rootCutStable
      | exact a5x_cutSame_proof
      | exact rootCorrection
      | exact a5x_rootCorr_proof
      | exact square_near_unit
      | exact a5x_squareNear_proof
      | exact phase_difference_estimate
      | exact a5x_phaseDiff_proof
      | exact phase_locally_constant
      | exact a5x_locConst_proof
      | exact integral_lattice_refinement_identity
      | exact a5x_intLatRefine_proof
      | exact padic_change_of_variables
      | exact a5x_changeVar_proof
      | exact crossTermsVanish
      | exact a5x_crossVanish_proof
      | exact averaged_vector_choices_exist
      | exact a5x_avgDataExists_proof
      | exact smallUnits
      | exact a5x_smallUnits_proof
      | exact gram_equality_of_vectors
      | exact a5x_uGramEq_proof
      | exact averaged_vector_norm_bound
      | exact a5x_uNormBound_proof
      | exact cut_posSemidef
      | exact a5x_cutPSD_proof
      | exact heads_distinct_determinant_orthogonal
      | exact a5x_uBlock_proof
      | exact head_size_add_block
      | exact a5x_cSizeAddBlock_proof
      | exact a6x_kpBlockDiag_proof
      | exact kernel_block_diagonal_by_modulus
      | exact annihilatorCharacters
      | exact a5x_perpDual_proof
      | exact characterMean
      | exact a5x_charMean_proof
      | exact truncated_average_norm_formula
      | exact a5x_cutNormEval_proof
      | exact thetaAverageLower
      | exact a5x_thxLower_proof
      | exact averaged_kernel_periodic_psd
      | exact a5x_thxBasic_proof
      | exact averaged_kernel_parseval
      | exact a5x_thxSum_proof)
end Formalism.FourierDecayAlt.P
