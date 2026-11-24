-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.map_prod_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:35.226155+00:00
-- url     : https://prove2.me/submissions/ce883a30-2be8-4499-b715-f79284896729

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
attribute [instance] LetSys.fin
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (V : VF C) {α : Type} (s : Finset α) (x : α → C) : V.v (∏ o ∈ s, x o) = ∑ o ∈ s, V.v (x o) := by
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, AddValuation.map_one]
  · intro a s ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]
end Formalism.L2.FormalSeriesBounds
