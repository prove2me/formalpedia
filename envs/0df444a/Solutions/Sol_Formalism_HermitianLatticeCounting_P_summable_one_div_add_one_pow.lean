-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.summable_one_div_add_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:37.866303+00:00
-- url     : https://prove2.me/submissions/51582eb5-52dd-44bb-b397-9669da9b7925

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

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
theorem _root_.solution (j : ℕ) (hj : 2 ≤ j) : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ j) := by
  have h := Real.summable_one_div_nat_pow.mpr (show 1 < j by omega)
  have h1 := (summable_nat_add_iff 1).mpr h
  exact h1.congr (fun n => by simp)
end Formalism.HermitianLatticeCounting.P
