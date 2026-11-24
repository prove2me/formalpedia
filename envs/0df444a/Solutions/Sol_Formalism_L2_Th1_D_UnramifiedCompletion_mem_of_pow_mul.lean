-- Prove2me | solution 1 for Formalism.L2.Th1.D.UnramifiedCompletion.mem_of_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:41.236938+00:00
-- url     : https://prove2.me/submissions/3456b6e3-f7e1-4521-a765-c4d323352ac7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormRingALe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExistsUnitFactorizationBounded

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
theorem _root_.solution (hdiv : DivB l) : ∀ (k : ℕ) (x : ℂ_[l]), ‖x‖ ≤ 1 →
    (l : ℂ_[l]) ^ k * x ∈ ringB l → x ∈ ringB l := by
  intro k
  induction k with
  | zero => intro x _ h; simpa using h
  | succ k ih =>
    intro x hx h
    have h1 : ‖(l : ℂ_[l]) ^ (k + 1) * x‖ < 1 := by
      rw [norm_mul, norm_pow]
      exact mul_lt_one_of_nonneg_of_lt_one_left (pow_nonneg (norm_nonneg _) _)
        (pow_lt_one₀ (norm_nonneg _) (normL_lt_one l) (Nat.succ_ne_zero _)) hx
    obtain ⟨y, hy, e⟩ := hdiv _ h h1
    refine ih x hx ?_
    have e2 : (l : ℂ_[l]) ^ k * x = y := by
      apply mul_left_cancel₀ (castL_ne_zero l)
      rw [← e, pow_succ]; ring
    rw [e2]; exact hy
end Formalism.L2.Th1.D.UnramifiedCompletion
