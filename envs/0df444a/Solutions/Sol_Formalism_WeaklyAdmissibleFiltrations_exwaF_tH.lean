-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.exwaF_tH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:29.245454+00:00
-- url     : https://prove2.me/submissions/62ca59ea-3f76-4f57-b9f3-a9193d1efe5c

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExwaFiltrationNegOneEqSpanSingle
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaFiltration_neg_one_eq_span_single
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_exwaF_Fil_0

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
theorem _root_.solution (c : LL) (hc : c ≠ 0) (D' : Submodule LL (ZMod n → LL)) :
    (exwaF c hc).tH D' =
      -∑ τ : ZMod n, (finrank LL ↥((LL ∙ (Pi.single τ (1 : LL) : ZMod n → LL)) ⊓ D') : ℤ) := by
  have hI : Finset.Ico (-1 : ℤ) 0 = {-1} := by ext a; simp; omega
  simp only [FilPhi.tH, FilPhi.tHw, FilPhi.mult]
  show ∑ τ, ∑ a ∈ Finset.Ico (-1 : ℤ) 0, a * _ = _
  rw [hI, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_singleton, show (-1 : ℤ) + 1 = 0 by norm_num, exwaFiltration_neg_one_eq_span_single, exwaF_Fil_0, bot_inf_eq,
    finrank_bot]
  push_cast
  ring
end Formalism.WeaklyAdmissibleFiltrations
