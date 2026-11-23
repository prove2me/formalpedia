-- Prove2me | solution 1 for Formalism.FX.succ_le_max_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:22.437248+00:00
-- url     : https://prove2.me/submissions/235694c6-c2a3-4618-94fa-e7a376ba9c58

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_DivisorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FX
open Finset
namespace Formalism.FX
theorem _root_.solution (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ≤ max 1 (1 / a) * Real.exp (a * k) := by
  have hM1 : (1 : ℝ) ≤ max 1 (1 / a) := le_max_left _ _
  have hMa : 1 ≤ max 1 (1 / a) * a := by
    calc (1 : ℝ) = (1 / a) * a := by field_simp
      _ ≤ max 1 (1 / a) * a := mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  calc ((k : ℝ) + 1) ≤ max 1 (1 / a) * (1 + a * k) := by nlinarith
    _ ≤ max 1 (1 / a) * Real.exp (a * k) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (a * k)]) (by linarith)
end Formalism.FX
