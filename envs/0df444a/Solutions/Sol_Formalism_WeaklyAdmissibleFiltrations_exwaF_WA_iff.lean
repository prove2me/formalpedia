-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_WA_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:29:42.048694+00:00
-- url     : https://prove2.me/submissions/c93dc1c0-7367-4ff1-8a0d-5c78422c2598

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_tH_top
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_tH_bot
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_e
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_val_det
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_val_det_top
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwa_sub_cases

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
theorem _root_.solution (v : AddValuation LL (WithTop ℚ)) (c : LL) (hc : c ≠ 0) (r : ℚ)
    (hr : v c = (r : WithTop ℚ)) : (exwaF (n := n) c hc).WeaklyAdmissible v ↔ r = -1 := by
  have hn : (n : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have key : (((exwaF (n := n) c hc).tH ⊤ : ℚ) : WithTop ℚ) =
      (exwaF (n := n) c hc).e • v (LinearMap.det ((exwaF (n := n) c hc).φ :
        (ZMod n → LL) →ₗ[LL] (ZMod n → LL))) ↔ r = -1 := by
    rw [exwaF_tH_top, exwaF_val_det v c hc r hr, exwaF_e, one_nsmul, WithTop.coe_inj]
    push_cast
    constructor
    · intro h
      have h' : (n : ℚ) * r = (n : ℚ) * (-1) := by linarith
      exact mul_left_cancel₀ hn h'
    · intro h; rw [h]; ring
  constructor
  · intro h; exact key.mp h.1
  · intro h
    refine ⟨key.mpr h, ?_⟩
    intro D' hD
    rcases exwa_sub_cases c hc D' hD with rfl | rfl
    · unfold FilPhi.NewtonAbove
      rw [exwaF_tH_bot, LinearMap.det_eq_one_of_finrank_eq_zero (finrank_bot _ _), AddValuation.map_one]
      simp
    · unfold FilPhi.NewtonAbove
      rw [exwaF_tH_top, exwaF_val_det_top v c hc r hr, exwaF_e, one_nsmul, h]
      apply le_of_eq
      rw [WithTop.coe_inj]
      push_cast
      ring
end Formalism.WeaklyAdmissibleFiltrations
