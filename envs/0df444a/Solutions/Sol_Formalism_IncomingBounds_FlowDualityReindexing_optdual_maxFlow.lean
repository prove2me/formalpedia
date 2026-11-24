-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.optdual_maxFlow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:06.873812+00:00
-- url     : https://prove2.me/submissions/2b78d0fa-ca7d-440d-b37a-7da1a09abb2a

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd

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
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowDualityReindexing
theorem _root_.solution (D sig : ZMod d → ℝ) (h : IsOptDual l d D sig) :
    maxFlow l d D = ∑ s : ZMod d, D s * sig s := by
  obtain ⟨_, h2⟩ := h
  unfold Formalism.IncomingBounds.Fnum at h2
  have : ∑ s : ZMod d, D s * (Formalism.IncomingBounds.gam l - sig s) =
      Formalism.IncomingBounds.gam l * ∑ s : ZMod d, D s - ∑ s : ZMod d, D s * sig s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  linarith
end Formalism.IncomingBounds.FlowDualityReindexing
