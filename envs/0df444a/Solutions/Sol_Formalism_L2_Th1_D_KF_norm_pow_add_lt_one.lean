-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.norm_pow_add_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:06:14.962802+00:00
-- url     : https://prove2.me/submissions/cd827cc1-38cf-47ee-9da6-95ff11e70fb6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_pos_real
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_inv_lt_one

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
open Formalism.DworkPowerSeriesWeights (Unram)
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution {a b : ℂ_[l]} (ha : ‖a‖ < 1) (hb : ‖b‖ ≤ 1) :
    ‖a ^ l + (l : ℂ_[l]) * b‖ < 1 := by
  have h1 : ‖a ^ l‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg a) ha hl.out.ne_zero
  have h2 : ‖(l : ℂ_[l]) * b‖ < 1 := by
    rw [norm_mul, norm_l_eq]
    calc (l : ℝ)⁻¹ * ‖b‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (l_pos_real l).le)
      _ < 1 := by rw [mul_one]; exact l_inv_lt_one l
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
end Formalism.L2.Th1.D.KF
