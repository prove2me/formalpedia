-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.CellDecomposition.sum_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:11.033025+00:00
-- url     : https://prove2.me/submissions/73765349-d210-49d1-923d-e4e2c53a4d9f

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open CellDecomposition
namespace Formalism.HermitianLatticeCounting.P
namespace CellDecomposition
theorem _root_.solution (n : ℕ) : ∑ s ∈ Finset.Icc 1 n, (1 / 2 : ℝ) ^ s = 1 - (1 / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring
end CellDecomposition
end Formalism.HermitianLatticeCounting.P
