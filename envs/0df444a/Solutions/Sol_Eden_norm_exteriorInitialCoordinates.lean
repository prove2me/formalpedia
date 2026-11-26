-- Prove2me | solution 1 for Eden.norm_exteriorInitialCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:08.25893+00:00
-- url     : https://prove2.me/submissions/bb7d4550-8278-4d41-8cfd-d7f518735614

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm
import Theorems.Thm_Eden_norm_exterior_map_isometry


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (p : PhaseSpace) (v : ExteriorSpace k) :
    ‖exteriorInitialCoordinates k p v‖ = ‖v‖ := by
  rw [exteriorInitialCoordinates, (exteriorBasis k).repr.norm_map,
    norm_exterior_map_isometry]
end Eden
