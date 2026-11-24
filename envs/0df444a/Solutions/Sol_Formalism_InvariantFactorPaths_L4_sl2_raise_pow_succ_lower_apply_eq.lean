-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sl2_raise_pow_succ_lower_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:41:38.317869+00:00
-- url     : https://prove2.me/submissions/18d1a4a7-b328-44fa-889e-ab1df150597e

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_weight_raise_pow_apply_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
variable {k V : Type} [Field k] [CharZero k] [AddCommGroup V] [Module k V] {e f h : V →ₗ[k] V}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) (hef : ∀ x, e (f x) - f (e x) = h x)
    {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    (e ^ (m + 1)) (f u) = f ((e ^ (m + 1)) u) + (((m : k) + 1) * (μ + (m : k))) • (e ^ m) u := by
  induction m with
  | zero =>
    have h1 := hef u
    rw [sub_eq_iff_eq_add] at h1
    simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero, one_mul]
    rw [h1, hu, add_comm]
  | succ m ih =>
    have hs : e ((e ^ m) u) = (e ^ (m + 1)) u := by rw [pow_succ', Module.End.mul_apply]
    rw [pow_succ' e (m + 1), Module.End.mul_apply, Module.End.mul_apply, ih, map_add, map_smul]
    have h1 := hef ((e ^ (m + 1)) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, sl2_weight_raise_pow_apply_eq he hu (m + 1), hs, add_comm (_ • _) (f _), add_assoc, ← add_smul]
    congr 1
    congr 1
    push_cast
    ring
end Formalism.InvariantFactorPaths.L4
