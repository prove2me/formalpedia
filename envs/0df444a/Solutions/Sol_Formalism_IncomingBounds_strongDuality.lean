-- Prove2me | solution 1 for Formalism.IncomingBounds.strongDuality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:00.706392+00:00
-- url     : https://prove2.me/submissions/1af428df-4aad-4f74-8be2-2ee12f00ff7a

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_opt_flow
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_maxFlow_eq
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_strong
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_dualAll_of_dual
import Theorems.Thm_Formalism_IncomingBounds_weakDuality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open FlowLoadBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : LemmaFa := by
  intro l d _ hl hd hev D hD
  have hl1 : 1 ≤ l := by omega
  obtain ⟨σ, hσ, heq⟩ := Formalism.IncomingBounds.FlowLoadBounds.strong hl1 D hD
  obtain ⟨x, hx, hmax⟩ := Formalism.IncomingBounds.FlowLoadBounds.exists_opt_flow hl1 D hD
  have hdef : Fnum l d D = ∑ s, D s * (gam l - σ s) := by
    unfold Fnum
    rw [← heq]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  refine ⟨⟨σ, hσ, Formalism.IncomingBounds.FlowLoadBounds.dualAll_of_dual hl1 hev hσ, hdef⟩, ⟨σ, hσ, hdef⟩, ?_⟩
  rintro t ⟨τ, hτ, rfl⟩
  have h1 : ∑ s, D s * σ s ≤ ∑ s, D s * τ s := by
    rw [heq, Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq hx hmax]
    exact weakDuality l d D x τ hx hτ
  rw [hdef]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith
end Formalism.IncomingBounds
