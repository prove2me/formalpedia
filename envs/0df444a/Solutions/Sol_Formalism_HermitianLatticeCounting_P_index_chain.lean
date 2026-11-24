-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.index_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:47.612162+00:00
-- url     : https://prove2.me/submissions/dcf41690-f11e-445c-99ea-bed6bf90c512

import Definitions.Def_Formalism_FlagUnipotentLattices_LiftUnitaryFixesBase
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LiftingDecomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_relIndex_intersection

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.IndexChain := by
  intro G _ abelian₂ L W La h1 h2 h0
  refine ⟨?_, ?_⟩
  · rw [mul_comm]; exact AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2
  · exact Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (relIndex_intersection G abelian₂ L W (L ⊓ W) le_rfl)
end Formalism.HermitianLatticeCounting.P
