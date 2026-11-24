-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.maxInvSinhSqLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:38.290802+00:00
-- url     : https://prove2.me/submissions/051d3842-cef1-43fa-ba82-ec7a33f6ead6

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
theorem _root_.solution : ShInvPlace := by
  intro sh G T T' Dr hsh hG hDr hTT hGeq
  have hTT0 : 0 < T * T' := by linarith
  have hsh0 : sh ≠ 0 := hsh.ne'
  have hDr0 : Dr ≠ 0 := hDr.ne'
  have hT0 : T * T' ≠ 0 := hTT0.ne'
  apply max_le
  · exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hTT (le_max_left _ _))
      (le_max_left _ _)
  · have e : 1 / sh ^ 2 = T * T' * Dr ^ 2 * (1 / G) := by
      rw [hGeq, mul_one_div, div_eq_div_iff (by positivity) (by rw [← hGeq]; exact hG.ne')]
      ring
    rw [e]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (le_max_right _ _) hTT0.le) (le_max_right _ _)
      (by positivity) (by positivity)
end Formalism.HermitianLatticeCounting.P
