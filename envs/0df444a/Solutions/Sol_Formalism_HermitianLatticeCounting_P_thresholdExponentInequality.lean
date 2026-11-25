-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.thresholdExponentInequality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:05:32.566413+00:00
-- url     : https://prove2.me/submissions/e66b4ad0-9848-407b-b11b-9fb9b4ba56b4

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
theorem _root_.solution : ThresholdP := by
  intro k r A cf hA hcf0 hcf hk
  have hkR : (2 * (r:ℝ) + 2) ^ 3 ≤ k := by exact_mod_cast hk
  have hr1 : (1:ℝ) ≤ (r:ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hA0 : (0:ℝ) ≤ A := by linarith
  have ha := mul_le_mul_of_nonneg_left hkR (by positivity : (0:ℝ) ≤ A * ((r:ℝ) + 1) ^ 2)
  have hb := mul_le_mul_of_nonneg_left hcf (by positivity : (0:ℝ) ≤ A * ((r:ℝ) + 1))
  have hc : (r:ℝ) + 1 ≤ A * ((r:ℝ) + 1) := by nlinarith
  have hd : A * ((r:ℝ) + 1) ^ 2 ≤ A * ((r:ℝ) + 1) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by norm_num)) hA0
  have he : A * ((r:ℝ) + 1) ^ 1 ≤ A * ((r:ℝ) + 1) ^ 5 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr1 (by norm_num)) hA0
  have hf : (0:ℝ) ≤ A * ((r:ℝ) + 1) ^ 5 := by positivity
  linarith
end Formalism.HermitianLatticeCounting.P
