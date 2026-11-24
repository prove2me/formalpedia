-- Prove2me | solution 1 for Formalism.L2.G.jW_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:01:35.350987+00:00
-- url     : https://prove2.me/submissions/02efdcba-aa12-4a98-91dd-dcad014cb336

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Theorems.Thm_Formalism_L2_G_jW_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution : Function.Injective (jW p n) := by
  intro x y h
  ext k
  have := congrArg (fun z => WittVector.coeff z k) h
  simp only [jW_coeff] at this
  exact (algebraMap (F1 p n) (F2 p n)).injective this
end Formalism.L2.G
