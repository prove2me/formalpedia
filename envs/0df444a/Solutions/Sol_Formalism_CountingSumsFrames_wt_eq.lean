-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:48:34.104175+00:00
-- url     : https://prove2.me/submissions/a6451a9a-48cb-4a74-8b8d-ffc97fdf8747

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) :
    wt LL j c m = ∑ i : Fin N, (if (i : ℕ) < j then (if LL.vec i then (1 : ℤ) else -1) else 0) * (m (i, c) : ℤ) := by
  unfold wt
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp
end Formalism.CountingSumsFrames
