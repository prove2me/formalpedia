-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sumLogZetaSeriesLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:05:13.614607+00:00
-- url     : https://prove2.me/submissions/2443cc70-9353-4e96-9f97-5fba6c0c2cbe

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sum_zetaSeries_sub_one_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_one_le_zetaSeries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : ZetaLogSum := by
  intro N
  calc ∑ j ∈ Finset.Icc 3 N, Real.log (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j) ≤ ∑ j ∈ Finset.Icc 3 N, (Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR j - 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj2 : 2 ≤ j := by simp only [Finset.mem_Icc] at hj; omega
        exact Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (one_le_zetaSeries j hj2))
    _ ≤ 0.356 := sum_zetaSeries_sub_one_le N
end Formalism.HermitianLatticeCounting.P
