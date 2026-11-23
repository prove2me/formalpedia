-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaFiltration_neg_one_eq_span_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:55.383394+00:00
-- url     : https://prove2.me/submissions/edc332ef-9b54-4f9b-9b57-99bc9ad43865

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) (τ : ZMod n) :
    (exwaF c hc).Fil τ (-1) = LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL) := by
  simp [exwaF]
end Formalism.WeaklyAdmissibleFiltrations
