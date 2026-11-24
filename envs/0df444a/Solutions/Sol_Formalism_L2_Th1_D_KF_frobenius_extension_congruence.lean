-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.frobenius_extension_congruence
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:07:20.769869+00:00
-- url     : https://prove2.me/submissions/b07c9aef-064d-429f-bfdf-43e60cb6f245

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq
import Theorems.Thm_Formalism_L2_Th1_D_KF_l_pos_real
import Theorems.Thm_Formalism_L2_Th1_D_KF_incAB_coe
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_continuous
import Theorems.Thm_Formalism_L2_Th1_D_KF_frobenius_extension_on_inclusion

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
open KF
open Formalism.L2.Th1.D.KF
variable (l : ℕ) [hl : Fact l.Prime]
variable {l}
variable (σ0 : ringA l →+* ringA l) (hiso : ∀ x : ringA l, ‖(σ0 x : ℂ_[l])‖ = ‖(x : ℂ_[l])‖)
namespace Formalism.L2.Th1.D.KF
theorem _root_.solution (hA : ∀ x ∈ ringA l, ‖x‖ ≤ 1)
    (hσ : ∀ x : ringA l, ∃ y : ringA l, σ0 x - x ^ l = (l : ringA l) * y) (x : ringB l) :
    ‖sig1 σ0 hiso x - (x : ℂ_[l]) ^ l‖ ≤ (l : ℝ)⁻¹ := by
  refine (incAB_dense l).induction_on x ?_ ?_
  · exact isClosed_le
      (continuous_norm.comp ((frobenius_extension_continuous σ0 hiso).sub (continuous_subtype_val.pow l))) continuous_const
  · intro a
    rw [frobenius_extension_on_inclusion, incAB_coe]
    obtain ⟨y, hy⟩ := hσ a
    have h := congrArg Subtype.val hy
    push_cast at h
    rw [h, norm_mul, norm_l_eq l]
    calc (l : ℝ)⁻¹ * ‖(y : ℂ_[l])‖ ≤ (l : ℝ)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left (hA _ y.2) (inv_nonneg.mpr (l_pos_real l).le)
      _ = (l : ℝ)⁻¹ := mul_one _
end Formalism.L2.Th1.D.KF
