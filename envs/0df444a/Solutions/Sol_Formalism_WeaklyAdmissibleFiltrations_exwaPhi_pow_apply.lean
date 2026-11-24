-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaPhi_pow_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:03.914666+00:00
-- url     : https://prove2.me/submissions/3bee2640-776a-45c4-8cff-de75de959ec2

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module
variable {LL : Type} [Field LL] {n : ℕ} [NeZero n]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution (c : LL) (hc : c ≠ 0) (k : ℕ) (x : ZMod n → LL) :
    (((exwaPhi (n := n) c hc).toLinearMap ^ k) x) =
      c ^ k • fun i => x (i - k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe, exwaPhi_apply, exwaShift_apply,
      Nat.cast_succ, sub_sub, pow_succ]
    ring
end Formalism.WeaklyAdmissibleFiltrations
