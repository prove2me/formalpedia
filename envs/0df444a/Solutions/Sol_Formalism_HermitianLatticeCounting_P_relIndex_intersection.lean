-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.relIndex_intersection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:51.925957+00:00
-- url     : https://prove2.me/submissions/4228a94c-c240-476a-9d0d-9fb16b427bb8

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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.RelIndexInter := by
  intro G _ abelian₂ M W La hle
  have hM : La ≤ M := hle.trans inf_le_left
  have hW : La ≤ W := hle.trans inf_le_right
  have e1 : (abelian₂ ⊓ W).relIndex La = abelian₂.relIndex La := by
    rw [← AddSubgroup.inf_relIndex_right, inf_assoc, inf_eq_right.2 hW, AddSubgroup.inf_relIndex_right]
  rw [e1, ← AddSubgroup.relIndex_addSubgroupOf hM]
  exact AddSubgroup.relIndex_dvd_index_of_normal _ _
end Formalism.HermitianLatticeCounting.P
