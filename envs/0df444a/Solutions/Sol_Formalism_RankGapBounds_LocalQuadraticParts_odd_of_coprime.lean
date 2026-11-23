-- Prove2me | solution 1 for Formalism.RankGapBounds.LocalQuadraticParts.odd_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:27.517253+00:00
-- url     : https://prove2.me/submissions/ce548b30-3984-4c2c-8b60-6e6e764134c4

import Definitions.Def_Formalism_RankGapBounds_RandomSubsetCounterexample
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.LocalQuadraticParts
namespace Formalism.RankGapBounds.LocalQuadraticParts
theorem _root_.solution (e l : ℕ) (hl : Nat.Coprime l (4 * 2 ^ e)) : Odd (l : ℤ) := by
  have h2 : ¬ 2 ∣ l := fun h => by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h hl)
      (dvd_mul_of_dvd_left (by norm_num) _)
    omega
  exact Int.odd_iff.mpr (by omega)
end Formalism.RankGapBounds.LocalQuadraticParts
