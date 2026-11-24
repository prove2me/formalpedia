-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_tH_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:01.428925+00:00
-- url     : https://prove2.me/submissions/f5e9cc69-f629-496a-9fc5-b65964c91d93

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_tH

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).tH ⊥ = 0 := by
  rw [exwaF_tH]
  have h1 : ∀ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ ⊥) : ℤ) = 0 := by
    intro τ
    rw [inf_bot_eq, finrank_bot]
    rfl
  simp only [h1, Finset.sum_const_zero, neg_zero]
end Formalism.WeaklyAdmissibleFiltrations
