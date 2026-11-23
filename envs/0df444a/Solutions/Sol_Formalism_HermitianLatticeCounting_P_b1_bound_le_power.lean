-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.b1_bound_le_power
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:27.941008+00:00
-- url     : https://prove2.me/submissions/0fe706d0-53ab-4c0f-8ac8-ec0979ae0a13

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {n q f : ℕ} {b Y : ℝ} (hqn : q ≤ n) (hY : 2 ≤ Y) (hnY : (n:ℝ) ≤ Y) (hfY : (f:ℝ) ≤ Y)
    (hb0 : 0 ≤ b) (hbY : b ≤ Y) : b1 n q f b ≤ Y ^ 10 := by
  unfold b1 P0
  push_cast
  have hq' : (q:ℝ) ≤ Y := le_trans (by exact_mod_cast hqn) hnY
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have hf0 : (0:ℝ) ≤ f := Nat.cast_nonneg _
  have hq0 : (0:ℝ) ≤ q := Nat.cast_nonneg _
  have h1 : b ^ 2 ≤ Y ^ 2 := by gcongr
  have h2 : 2 * (8 * (q:ℝ) * (n:ℝ) ^ 2 * f) * n ≤ Y * (Y ^ 3 * Y * Y ^ 2 * Y) * Y := by
    have h8 : (8:ℝ) ≤ Y ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Y ^ 3 := by gcongr
    gcongr
  have h3 : Y ^ 2 ≤ Y ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h9 : 0 < Y ^ 9 := by positivity
  nlinarith
end Formalism.HermitianLatticeCounting.P
