-- Prove2me | solution 1 for Formalism.L2.Th1.D.KF.norm_eq_of_pow_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:06:11.63581+00:00
-- url     : https://prove2.me/submissions/2bb2d5f4-99bc-4ccb-82a9-6b83452222ce

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusExtensionOnInclusion
import Theorems.Thm_Formalism_L2_Th1_D_KF_norm_l_eq

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
theorem _root_.solution {a b : ℂ_[l]} {N : ℕ} (hN : N ≠ 0) (ha : ‖a‖ < 1)
    (h : a ^ (N + 1) - a = (l : ℂ_[l]) * b) : ‖a‖ = (l : ℝ)⁻¹ * ‖b‖ := by
  have hN1 : ‖a ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg a) ha hN
  have h1 : ‖a ^ N - 1‖ = 1 := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hN1.ne), norm_neg, norm_one]
    exact max_eq_right hN1.le
  have h2 : a ^ (N + 1) - a = a * (a ^ N - 1) := by ring
  have h3 := congrArg norm h
  rw [h2, norm_mul, h1, mul_one, norm_mul, norm_l_eq] at h3
  exact h3
end Formalism.L2.Th1.D.KF
