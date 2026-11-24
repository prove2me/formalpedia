-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.one_le_zetaSeries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:00.149823+00:00
-- url     : https://prove2.me/submissions/92a889a4-81e8-45cd-a446-71673f2b5a51

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_zetaSeries_eq_one_add_tsum

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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) : 1 ≤ zetaR j := by
  rw [zetaSeries_eq_one_add_tsum j hj]
  have : 0 ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ j := tsum_nonneg (fun n => by positivity)
  linarith
end Formalism.HermitianLatticeCounting.P
