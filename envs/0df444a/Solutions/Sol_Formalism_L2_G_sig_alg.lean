-- Prove2me | solution 1 for Formalism.L2.G.sig_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:32.587535+00:00
-- url     : https://prove2.me/submissions/4b08564b-e057-4644-b73d-869c29157e3a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

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
theorem _root_.solution (x : WQ p n) : sig p n (algebraMap _ _ x) = algebraMap _ _ (WittVector.frobenius x) := by
  unfold sig
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl
end Formalism.L2.G
