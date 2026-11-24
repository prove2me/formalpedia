-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.sl2_eq_zero_of_lower_zero_of_raise_pow_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:49:48.891272+00:00
-- url     : https://prove2.me/submissions/070a3f3f-06df-4a0a-9fa3-a6dda7b12423

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_sl2_raise_pow_succ_lower_apply_eq

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
    {u : V} {μ : ℤ} (hu : h u = ((μ : ℤ) : k) • u) (hf : f u = 0) :
    ∀ j : ℕ, μ + j ≤ 0 → (e ^ j) u = 0 → u = 0 := by
  intro j
  induction j with
  | zero =>
    intro _ h0
    simpa using h0
  | succ j ih =>
    intro hj h0
    apply ih (by omega)
    have hc := sl2_raise_pow_succ_lower_apply_eq he hef hu j
    rw [hf, map_zero, h0, map_zero, zero_add] at hc
    have hne : ((j : k) + 1) * (((μ : ℤ) : k) + (j : k)) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast Nat.succ_ne_zero j
      · have h5 : (μ + j : ℤ) ≠ 0 := by omega
        exact_mod_cast h5
    exact (smul_eq_zero.mp hc.symm).resolve_left hne
end Formalism.InvariantFactorPaths.L4
