-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.isCompact_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:08.80711+00:00
-- url     : https://prove2.me/submissions/b7eece53-ca5e-4b04-9e00-d10ad8093dc6

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained

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
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution : IsCompact {sig : ZMod d → ℝ | IsDual l d sig} := by
  have e : {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} =
      ((⋂ s, {sig : ZMod d → ℝ | 0 ≤ sig s}) ∩ ⋂ s, {sig : ZMod d → ℝ | sig s ≤ 1}) ∩
        ⋂ s, ⋂ i ∈ oddLevels d, {sig : ZMod d → ℝ | 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))} := by
    ext sig
    simp only [Formalism.IncomingBounds.IsDual, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, forall_and]
  have hclosed : IsClosed {sig : ZMod d → ℝ | Formalism.IncomingBounds.IsDual l d sig} := by
    rw [e]
    exact ((isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)).inter
      (isClosed_iInter fun s => isClosed_le (continuous_apply s) continuous_const)).inter
      (isClosed_iInter fun s => isClosed_biInter fun i _ =>
        isClosed_le continuous_const (by fun_prop))
  refine (isCompact_univ_pi fun _ : ZMod d => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
    hclosed ?_
  intro sig hsig
  have hs : Formalism.IncomingBounds.IsDual l d sig := hsig
  exact Set.mem_univ_pi.2 fun s => hs.1 s
end Formalism.IncomingBounds.FlowLoadBounds
