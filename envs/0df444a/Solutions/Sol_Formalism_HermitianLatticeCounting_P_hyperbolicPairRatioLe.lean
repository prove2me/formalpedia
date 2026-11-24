-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hyperbolicPairRatioLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:18.077201+00:00
-- url     : https://prove2.me/submissions/e0f60cf0-b825-4249-b028-bd11d07fbddb

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
theorem _root_.solution : ChShPair := by
  intro sh₁ ch₁ sh₂ ch₂ h1 hc1 e1 h2 hc2 e2
  have key : ∀ sh ch : ℝ, 0 < sh → 0 ≤ ch → ch ^ 2 = sh ^ 2 + 1 → ch * min 1 sh ≤ 2 * sh := by
    intro sh ch hs hc e
    rcases le_or_gt 1 sh with h | h
    · rw [min_eq_left h, mul_one]; nlinarith
    · rw [min_eq_right h.le]
      have hc2 : ch ≤ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hc2 hs.le
  have m1 : 0 < min 1 sh₁ := lt_min one_pos h1
  have m2 : 0 < min 1 sh₂ := lt_min one_pos h2
  have k1 := key sh₁ ch₁ h1 hc1 e1
  have k2 := key sh₂ ch₂ h2 hc2 e2
  have l1 : min 1 sh₁ ≤ sh₁ := min_le_right _ _
  have l2 : min 1 sh₂ ≤ sh₂ := min_le_right _ _
  rw [div_le_iff₀ (mul_pos h1 h2), div_mul_eq_mul_div, le_div_iff₀ (mul_pos m1 m2)]
  nlinarith [mul_le_mul_of_nonneg_right k1 m2.le, mul_le_mul_of_nonneg_right k2 m1.le,
    mul_le_mul_of_nonneg_left l2 h1.le, mul_le_mul_of_nonneg_left l1 h2.le]
end Formalism.HermitianLatticeCounting.P
