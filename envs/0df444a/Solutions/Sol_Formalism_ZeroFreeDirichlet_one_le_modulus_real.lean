-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.one_le_modulus_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:53.349959+00:00
-- url     : https://prove2.me/submissions/27308f2e-2a5d-4b73-9e8b-8f583a65eac1

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] : (1 : ℝ) ≤ q := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne q)
end Formalism.ZeroFreeDirichlet
