-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.t_NumDens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:25.76282+00:00
-- url     : https://prove2.me/submissions/e168a695-5933-4e88-98b8-1a40d5bb2929

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_inv_two_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Formalism.FourierDecayAlt.PB Finset
namespace Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
theorem _root_.solution : NumDens := by
  intro k r f hf hk32 hr
  have hkR : (32:ℝ) ≤ k := by exact_mod_cast hk32
  have hk0 : (0:ℝ) < k := by linarith
  have hfk : (f:ℝ) ≤ k := by exact_mod_cast hf
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg f
  have key : 12 * ((2:ℝ) ^ (k - 2 * r - 2))⁻¹ ≤ (2:ℝ) ^ (-(k:ℝ) / 2) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * r + 2 + j := ⟨k - (2 * r + 2), by omega⟩
    have hj : 2 * r + 2 + j - 2 * r - 2 = j := by omega
    rw [hj, inv_two_pow]
    have e : -((2 * r + 2 + j : ℕ) : ℝ) / 2 = -(j:ℝ) + ((j:ℝ) - 2 * r - 2) / 2 := by
      push_cast
      ring
    rw [e, Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have h4 : (4:ℝ) ≤ ((j:ℝ) - 2 * r - 2) / 2 := by
      have : ((4 * r + 12 : ℕ) : ℝ) ≤ ((2 * r + 2 + j : ℕ) : ℝ) := by exact_mod_cast hr
      push_cast at this
      linarith
    have h16 : (16:ℝ) ≤ (2:ℝ) ^ (((j:ℝ) - 2 * r - 2) / 2) := by
      calc (16:ℝ) = (2:ℝ) ^ ((4:ℕ):ℝ) := by rw [Real.rpow_natCast]; norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
    have hp : 0 < (2:ℝ) ^ (-(j:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    nlinarith [mul_le_mul_of_nonneg_left h16 hp.le]
  constructor
  · have := mul_le_mul_of_nonneg_left key hf0
    nlinarith [this]
  · have hL1 := Real.log_two_gt_d9
    have hL2 := Real.log_two_lt_d9
    have hlog : Real.log k ≤ 5 * Real.log 2 + k / 32 - 1 := by
      have h1 := Real.log_le_sub_one_of_pos (show (0:ℝ) < k / 32 by positivity)
      rw [Real.log_div hk0.ne' (by norm_num)] at h1
      have h32 : Real.log (32:ℝ) = 5 * Real.log 2 := by
        rw [show (32:ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
        norm_num
      linarith
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    calc (f:ℝ) * Real.exp (Real.log 2 * (-(k:ℝ) / 2))
        ≤ (k:ℝ) * Real.exp (Real.log 2 * (-(k:ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hfk (Real.exp_pos _).le
      _ = Real.exp (Real.log k + Real.log 2 * (-(k:ℝ) / 2)) := by
          rw [Real.exp_add, Real.exp_log hk0]
      _ ≤ Real.exp (-(k:ℝ) / 5) := by
          apply Real.exp_le_exp.mpr
          nlinarith [mul_le_mul_of_nonneg_left hL1.le hk0.le]
end Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
