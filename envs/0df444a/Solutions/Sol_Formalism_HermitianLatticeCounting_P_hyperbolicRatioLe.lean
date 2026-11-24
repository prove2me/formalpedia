-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hyperbolicRatioLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:46.633127+00:00
-- url     : https://prove2.me/submissions/7ad6f934-1289-41b0-b215-5fc34ade4c23

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
theorem _root_.solution : ChShBound := by
  intro sh ch hsh hch hc
  have hch2 : ch ≤ sh + 1 := by nlinarith
  rcases le_or_gt 1 sh with h1 | h1
  · calc (1 + ch) / sh ≤ 3 := by rw [div_le_iff₀ hsh]; linarith
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_left 1 (1 / sh); linarith
  · have hc2 : ch ≤ 2 := by nlinarith
    calc (1 + ch) / sh ≤ 3 / sh := div_le_div_of_nonneg_right (by linarith) hsh.le
      _ = 3 * (1 / sh) := by ring
      _ ≤ 3 * max 1 (1 / sh) := by have := le_max_right 1 (1 / sh); linarith
end Formalism.HermitianLatticeCounting.P
