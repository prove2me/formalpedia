-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.inv_ringA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:41.162462+00:00
-- url     : https://prove2.me/submissions/3881b593-9b19-4c73-bcde-d329f9ee84f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_ringA_le_ringB
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_geom_mem
import Theorems.Thm_Formalism_L2_Th1_D_UnramifiedCompletion_exists_pow_eq
import Theorems.Thm_UpperTheory_Reformulated_B_Qi27_norm_ringA_le


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
open Filter Topology
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.DworkPowerSeriesWeights (Unram)
open UnramifiedCompletion
open Formalism.L2.Th1.D.UnramifiedCompletion
variable {l : ℕ} [hl : Fact l.Prime]
namespace Formalism.L2.Th1.D.UnramifiedCompletion
theorem _root_.solution (hA : PerA l) {u : ℂ_[l]} (hu : u ∈ ringA l) (h : ‖u‖ = 1) : u⁻¹ ∈ ringB l := by
  obtain ⟨f, hf, y, hy, e⟩ := hA u hu
  obtain ⟨N, hN⟩ := exists_pow_eq (l := l) f hf
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
  have e2 : u * (1 - u ^ (N + 1)) = (l : ℂ_[l]) * (-y) := by
    rw [hN] at e
    linear_combination -e
  have hw : ‖1 - u ^ (N + 1)‖ < 1 := by
    have h1 := congrArg norm e2
    rw [norm_mul, norm_mul, h, one_mul, norm_neg] at h1
    rw [h1]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (normL_lt_one l) (norm_ringA_le hy)
  have hB : 1 - u ^ (N + 1) ∈ ringB l := sub_mem (one_mem _) (pow_mem (ringA_le_ringB hu) _)
  have h3 := geom_mem hB hw
  rw [sub_sub_cancel] at h3
  have h4 : u⁻¹ = u ^ N * (u ^ (N + 1))⁻¹ := by
    rw [pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_mul]
  rw [h4]
  exact mul_mem (pow_mem (ringA_le_ringB hu) _) h3
end Formalism.L2.Th1.D.UnramifiedCompletion
