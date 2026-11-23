-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wt_min
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.568899+00:00
-- url     : https://prove2.me/submissions/6a3831a3-7af2-4ac2-880a-7c04b345499f

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (c : Fin r) : wt LL j c = wt LL (min j N) c := by
  funext m
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (i : ℕ) < j
  · rw [if_pos h, if_pos (lt_min h i.isLt)]
  · rw [if_neg h, if_neg (fun h' => h (lt_of_lt_of_le h' (min_le_left _ _)))]
end Formalism.CountingSumsFrames
