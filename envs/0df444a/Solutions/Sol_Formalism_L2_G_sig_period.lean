-- Prove2me | solution 1 for Formalism.L2.G.sig_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:29.985325+00:00
-- url     : https://prove2.me/submissions/f064438d-3a89-4c55-b1c5-13d157d9a4e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Theorems.Thm_Formalism_L2_G_frob_iter_WQ
import Theorems.Thm_Formalism_L2_G_sig_pow_alg

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
namespace Formalism.L2.G
theorem _root_.solution : sig p n ^ n = 1 := by
  have h : ((sig p n ^ n).toRingHom : FractionRing (WQ p n) →+* FractionRing (WQ p n)) =
      RingHom.id _ := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (WQ p n)) ?_
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingHom.id_apply]
    rw [sig_pow_alg, frob_iter_WQ]
  ext y
  have := congrArg (fun f : FractionRing (WQ p n) →+* FractionRing (WQ p n) => f y) h
  simpa using this
end Formalism.L2.G
