-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exWA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:37:53.806734+00:00
-- url     : https://prove2.me/submissions/9c2add4c-d223-4423-826f-a34f4c78246a

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaFiltration_neg_one_eq_span_single
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_Fil_0
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_WA_iff

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
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : ExWA := by
  intro LL _ v l hv n _
  have hl : l ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hv
    exact absurd hv (by simp)
  have hinv : v l⁻¹ = ((-1 : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_inv, hv]
    rfl
  have hone : v (1 : LL) = ((0 : ℚ) : WithTop ℚ) := by
    rw [AddValuation.map_one]
    rfl
  refine ⟨ZMod n → LL, inferInstance, inferInstance, inferInstance,
    exwaF l⁻¹ (inv_ne_zero hl), exwaF 1 one_ne_zero, ?_, ?_, ?_⟩
  · exact (exwaF_WA_iff v _ _ _ hinv).mpr rfl
  · intro τ
    unfold FilPhi.IsJump
    rw [show (-1 : ℤ) + 1 = 0 by norm_num, exwaF_Fil_0, exwaFiltration_neg_one_eq_span_single]
    intro h
    have h2 := Submodule.span_singleton_eq_bot.mp h.symm
    simp at h2
  · rw [exwaF_WA_iff v _ _ _ hone]
    norm_num
end Formalism.WeaklyAdmissibleFiltrations
