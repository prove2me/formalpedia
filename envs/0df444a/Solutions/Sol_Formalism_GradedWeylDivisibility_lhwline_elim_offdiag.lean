-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwline_elim_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:21.428766+00:00
-- url     : https://prove2.me/submissions/5c2a8289-afc7-4cc6-b1a2-70c1f0cc31c6

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwline_elim_cleared

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable {K : Type} [Field K] {r n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution [Infinite K] (x : Fin r × Fin n → K)
    (hx : ∀ (s : ℕ) (hr : s + 1 ≤ r) (hn : s + 1 ≤ n), eval x (lpMinor K (s + 1) hr hn) ≠ 0)
    (a : Fin r) (j : Fin n) (h : a.val ≠ j.val) : lhwline_elim (min r n) x (a, j) = 0 := by
  apply lhwline_elim_cleared x hx (min r n) le_rfl a j h
  rcases le_total r n with hrn | hrn
  · left
    rw [min_eq_left hrn]
    exact a.isLt
  · right
    rw [min_eq_right hrn]
    exact j.isLt
end Formalism.GradedWeylDivisibility
