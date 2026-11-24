-- Prove2me | solution 1 for Formalism.L2.Th1.D.integral_part_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:36:45.368347+00:00
-- url     : https://prove2.me/submissions/5b9f8054-a942-4a4e-861f-78ceac80c0bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_L2_Th1_D_ip_integral_add
import Theorems.Thm_Formalism_L2_Th1_D_ip_integral_C_mul
import Theorems.Thm_Formalism_L2_Th1_D_ip_op_zero
import Theorems.Thm_Formalism_L2_Th1_D_ip_op_add
import Theorems.Thm_Formalism_L2_Th1_D_ip_op_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
namespace Formalism.L2.Th1.D
theorem _root_.solution : IPClosure := by
  intro K _ _ _ l σ τ _
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  · rw [ip_op_zero, sub_zero]
    intro n
    simp
  · rintro g g' ⟨h0, hI⟩ ⟨h0', hI'⟩
    refine ⟨by rw [map_add, h0, h0', add_zero], ?_⟩
    rw [ip_op_add, add_sub_add_comm]
    exact ip_integral_add hI hI'
  · rintro c g hc hσ ⟨h0, hI⟩
    refine ⟨by rw [map_mul, h0, mul_zero], ?_⟩
    rw [ip_op_C_mul, hσ, ← mul_sub]
    exact ip_integral_C_mul hc hI
end Formalism.L2.Th1.D
