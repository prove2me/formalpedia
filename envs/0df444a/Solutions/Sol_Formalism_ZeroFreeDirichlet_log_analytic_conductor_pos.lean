-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_analytic_conductor_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:11.156048+00:00
-- url     : https://prove2.me/submissions/c4ea3b57-5bf6-49f7-81a3-76c40b903a85

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SiegelWalfiszOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) : 0 < Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1:ℝ) ≤ q := by
    have h1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast h1
  apply Real.log_pos
  have ht := abs_nonneg t
  nlinarith
end Formalism.ZeroFreeDirichlet
