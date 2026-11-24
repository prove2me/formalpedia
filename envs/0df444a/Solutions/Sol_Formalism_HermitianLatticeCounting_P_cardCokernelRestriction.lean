-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cardCokernelRestriction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:04.118851+00:00
-- url     : https://prove2.me/submissions/b3a61b0d-b2ec-4bd6-977e-1295016caf2c

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LatticeSumBounds.HomRestrictIndex := by
  intro O M X _ _ _ _ _ _ _ _ _ _ P hO hfin
  have h := s5b7_main hO X (Nat.card (M ⧸ P)) P M P.subtype P.injective_subtype Nat.card_pos.ne'
    (by rw [Submodule.range_subtype])
  exact h
end Formalism.HermitianLatticeCounting.P
