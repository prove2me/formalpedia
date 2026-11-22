-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.three_le_modulus_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:13:05.216412+00:00
-- url     : https://prove2.me/submissions/00a7b777-a3f0-4ec3-903d-d4cf4ba57442

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LDerivNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) : 3 ≤ q := by
  by_contra h
  push_neg at h
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  all_goals
    apply hχ
    ext a
    have ha : a = 1 := by revert a; decide
    rw [ha]
    simp
end Formalism.ZeroFreeDirichlet
