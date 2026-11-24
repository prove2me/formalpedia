-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.zetaSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:25.239718+00:00
-- url     : https://prove2.me/submissions/7e1641b3-effe-4823-98fe-4905ed7c4ee0

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
theorem _root_.solution (j : ℕ) (hj : 3 ≤ j) : zetaR j ≤ 1.356 := by
  have hmem : j ∈ Finset.Icc 3 j := Finset.mem_Icc.mpr ⟨hj, le_rfl⟩
  have hnn : ∀ i ∈ Finset.Icc 3 j, (0:ℝ) ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.zetaR i - 1 := by
    intro i hi
    have : 2 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    linarith [one_le_zetaSeries i this]
  have h := Finset.single_le_sum hnn hmem
  linarith [sum_zetaSeries_sub_one_le j]
end Formalism.HermitianLatticeCounting.P
