-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sl2_weight_raise_pow_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:50.752895+00:00
-- url     : https://prove2.me/submissions/db024004-1734-425a-95b1-84edbc159c2c

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq

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
theorem _root_.solution (he : ∀ x, h (e x) - e (h x) = (2 : k) • e x) {u : V} {μ : k} (hu : h u = μ • u) (m : ℕ) :
    h ((e ^ m) u) = (μ + 2 * (m : k)) • (e ^ m) u := by
  induction m with
  | zero => simp [hu]
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h1 := he ((e ^ m) u)
    rw [sub_eq_iff_eq_add] at h1
    rw [h1, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
end Formalism.InvariantFactorPaths.L4
