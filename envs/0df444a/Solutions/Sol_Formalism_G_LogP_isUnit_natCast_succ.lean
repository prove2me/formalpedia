-- Prove2me | solution 1 for Formalism.G.LogP.isUnit_natCast_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:01.120091+00:00
-- url     : https://prove2.me/submissions/91dd37cc-52a3-478f-88a1-2a5f03345f63

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
namespace Formalism.G.LogP
theorem _root_.solution [Algebra ℚ R] (n : ℕ) : IsUnit ((n : R) + 1) := by
  have h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by simp
  rw [h]
  exact IsUnit.map _ (isUnit_iff_ne_zero.2 (by positivity))
end Formalism.G.LogP
