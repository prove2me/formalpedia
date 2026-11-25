-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.powTwoDivLeExpLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:26.757996+00:00
-- url     : https://prove2.me/submissions/31962a65-6407-4143-b0bd-7825ed491749

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : GainQuadratic := by
  intro k N b g hk hb hg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hb0 : 0 < b := by linarith
  have hb7 : 0 < b ^ 7 := pow_pos hb0 7
  have hb8 : b ^ 8 ≤ g := le_trans (pow_le_pow_left₀ hb0.le (by nlinarith) 8) hg
  have hg0 : 0 < g := lt_of_lt_of_le (pow_pos hb0 8) hb8
  have h1 : 2 / g ≤ (b ^ 7)⁻¹ := by
    rw [div_le_iff₀ hg0]
    have e8 : b ^ 8 = b ^ 7 * b := by ring
    have h27 : b ^ 7 * 2 ≤ g := by nlinarith
    calc (2:ℝ) = (b ^ 7)⁻¹ * (b ^ 7 * 2) := (inv_mul_cancel_left₀ hb7.ne' 2).symm
      _ ≤ (b ^ 7)⁻¹ * g := mul_le_mul_of_nonneg_left h27 (by positivity)
  have e7 : Real.exp (7 * Real.log b) = b ^ 7 := by
    rw [show (7:ℝ) * Real.log b = Real.log (b ^ 7) by rw [Real.log_pow]; norm_num,
      Real.exp_log hb7]
  have heq : Real.exp (-7 * N * Real.log b) = ((b ^ 7)⁻¹) ^ N := by
    rw [show -7 * (N:ℝ) * Real.log b = (N:ℝ) * (-(7 * Real.log b)) by ring, Real.exp_nat_mul,
      Real.exp_neg, e7]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) h1 N
end Formalism.HermitianLatticeCounting.P
