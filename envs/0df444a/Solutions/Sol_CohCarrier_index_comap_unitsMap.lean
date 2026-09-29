-- Prove2me | solution 1 for CohCarrier.index_comap_unitsMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9d017509-fdcb-5bf6-aff9-53e610d31b94

import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_index_comap_unitsMap

set_option autoImplicit false

theorem solution
    {M M' : ℕ} [NeZero M'] (hMM' : M ∣ M') (H₀ : Subgroup (ZMod M)ˣ) :
    (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index :=
  Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hMM')

end S_CohCarrier_index_comap_unitsMap
end P2MW
export P2MW.S_CohCarrier_index_comap_unitsMap (solution)
