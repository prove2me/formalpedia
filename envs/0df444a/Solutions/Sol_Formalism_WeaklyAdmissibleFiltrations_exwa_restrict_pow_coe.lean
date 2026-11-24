-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwa_restrict_pow_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:40:51.463408+00:00
-- url     : https://prove2.me/submissions/56374887-d565-4d7a-9c5d-b139bd7839e9

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
variable {LL : Type} [Field LL]
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution {M : Type} [AddCommGroup M] [Module LL M] (f : M →ₗ[LL] M)
    (p : Submodule LL M) (h : ∀ x ∈ p, f x ∈ p) (k : ℕ) (x : p) :
    (((f.restrict h) ^ k) x : M) = (f ^ k) x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply,
      LinearMap.coe_restrict_apply]
end Formalism.WeaklyAdmissibleFiltrations
