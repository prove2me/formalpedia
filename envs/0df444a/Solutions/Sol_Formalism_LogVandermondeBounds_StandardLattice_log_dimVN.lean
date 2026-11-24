-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.log_dimVN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:37:41.832736+00:00
-- url     : https://prove2.me/submissions/d1845d7b-4420-4258-8808-7f2eb9f94317

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution (x : ℕ → ℝ) (N : ℕ) (h : 0 < vandN x N) :
    0 < dimVN x N ∧ Real.log (dimVN x N)
      = Real.log (vandN x N) - ∑ i ∈ range N, Real.log ((i.factorial : ℕ) : ℝ) := by
  have hF : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := prod_pos (fun i _ => by positivity)
  refine ⟨div_pos h hF, ?_⟩
  unfold dimVN
  rw [Real.log_div h.ne' hF.ne', Real.log_prod (fun i _ => by positivity)]
end Formalism.LogVandermondeBounds.StandardLattice
