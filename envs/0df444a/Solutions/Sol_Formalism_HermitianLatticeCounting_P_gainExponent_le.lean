-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gainExponent_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:49.149337+00:00
-- url     : https://prove2.me/submissions/f8f81638-b80c-4f32-8a83-5dc7eae7657c

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
theorem _root_.solution (k r : ℕ) (hk : 1 ≤ k) : expo k r ≤ 2 * r := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.expo
  rw [div_le_iff₀ hk0]
  have h : 2 * r * (k - 2 - r) ≤ 2 * r * k := Nat.mul_le_mul_left _ (by omega)
  calc ((2 * r * (k - 2 - r) : ℕ) : ℝ) ≤ ((2 * r * k : ℕ) : ℝ) := by exact_mod_cast h
    _ = 2 * r * k := by push_cast; try ring
end Formalism.HermitianLatticeCounting.P
