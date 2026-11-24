-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_tH_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:41:02.266793+00:00
-- url     : https://prove2.me/submissions/ba50bfcb-37cd-4d61-8911-c6d1fe50a5d9

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) : (exwaF (n := n) c hc).tH ⊤ = -(n : ℤ) := by
  rw [exwaF_tH]
  have h1 : ∀ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ ⊤) : ℤ) = 1 := by
    intro τ
    rw [inf_top_eq, finrank_span_singleton (by simp)]
    rfl
  simp only [h1, Finset.sum_const, Finset.card_univ, ZMod.card n, nsmul_eq_mul, mul_one]
end Formalism.WeaklyAdmissibleFiltrations
