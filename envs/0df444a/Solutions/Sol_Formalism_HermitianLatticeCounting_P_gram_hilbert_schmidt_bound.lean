-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gram_hilbert_schmidt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:07:14.391885+00:00
-- url     : https://prove2.me/submissions/5b958860-c728-426f-9789-cf9dd2c1b31f

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gb_norm_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset
open scoped ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.SkewOperatorFrobeniusBound := by
  intro V _ _ θ h n bs e v
  rw [Finset.sum_comm]
  have p1 : ∀ b, ∑ a, ‖inner ℂ (bs a) (majorantHermitianForm θ (bs b) v • e - majorantHermitianForm θ (bs b) e • v)‖ ^ 2 ≤
      2 * (‖inner ℂ (θ v) (bs b)‖ ^ 2 * ‖e‖ ^ 2 + ‖inner ℂ (θ e) (bs b)‖ ^ 2 * ‖v‖ ^ 2) := by
    intro b
    rw [bs.sum_sq_norm_inner_right]
    unfold majorantHermitianForm
    have t : ‖inner ℂ (θ v) (bs b) • e - inner ℂ (θ e) (bs b) • v‖ ≤
        ‖inner ℂ (θ v) (bs b)‖ * ‖e‖ + ‖inner ℂ (θ e) (bs b)‖ * ‖v‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul]
    calc ‖inner ℂ (θ v) (bs b) • e - inner ℂ (θ e) (bs b) • v‖ ^ 2
        ≤ (‖inner ℂ (θ v) (bs b)‖ * ‖e‖ + ‖inner ℂ (θ e) (bs b)‖ * ‖v‖) ^ 2 := by gcongr
      _ ≤ _ := by
        nlinarith [sq_nonneg (‖inner ℂ (θ v) (bs b)‖ * ‖e‖ - ‖inner ℂ (θ e) (bs b)‖ * ‖v‖)]
  calc _ ≤ ∑ b, 2 * (‖inner ℂ (θ v) (bs b)‖ ^ 2 * ‖e‖ ^ 2 + ‖inner ℂ (θ e) (bs b)‖ ^ 2 * ‖v‖ ^ 2) :=
        Finset.sum_le_sum fun b _ => p1 b
    _ = 2 * ((∑ b, ‖inner ℂ (θ v) (bs b)‖ ^ 2) * ‖e‖ ^ 2 + (∑ b, ‖inner ℂ (θ e) (bs b)‖ ^ 2) * ‖v‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
    _ = 4 * ‖e‖ ^ 2 * ‖v‖ ^ 2 := by
        rw [bs.sum_sq_norm_inner_left, bs.sum_sq_norm_inner_left, gb_norm_theta h, gb_norm_theta h]
        ring
end Formalism.HermitianLatticeCounting.P
