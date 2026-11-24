-- Prove2me | solution 1 for Formalism.L2.G.sig_pow_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:01:34.946621+00:00
-- url     : https://prove2.me/submissions/0d3e6e52-f087-41bf-b9d2-c8410358c2a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Theorems.Thm_Formalism_L2_G_sig_alg

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
theorem _root_.solution (k : ℕ) (x : WQ p n) :
    (sig p n ^ k) (algebraMap _ _ x) = algebraMap _ _ ((WittVector.frobenius^[k]) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ]
    show (sig p n ^ k) (sig p n (algebraMap _ _ x)) = _
    rw [sig_alg, ih, Function.iterate_succ_apply]
end Formalism.L2.G
