-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sum_fin_filter_lt_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:07.080909+00:00
-- url     : https://prove2.me/submissions/f04a77e4-0904-4611-b5df-33898a962832

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_BideterminantDominance
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {N : ℕ} (G : ℕ → ℕ) (k : ℕ) :
    ∑ a : Fin N with a.val < k, G a.val = ∑ i ∈ Finset.range (min N k), G i := by
  rw [Finset.sum_filter]
  refine (Fin.sum_univ_eq_sum_range (fun i => if i < k then G i else 0) N).trans ?_
  show ∑ i ∈ Finset.range N, (if i < k then G i else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega
end Formalism.GradedWeylDivisibility
