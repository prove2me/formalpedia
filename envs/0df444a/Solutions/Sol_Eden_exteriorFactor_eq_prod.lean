-- Prove2me | solution 1 for Eden.exteriorFactor_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:34:27.816833+00:00
-- url     : https://prove2.me/submissions/4e4a551f-85e4-491b-8c51-11b0f3d5b634

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorFactor k d s = ∏ j ∈ s.val, d j := by
  unfold exteriorFactor
  change (∏ i : Fin k, d (s.val.orderEmbOfFin s.property i)) = _
  conv_rhs => rw [← Finset.image_orderEmbOfFin_univ s.val s.property]
  rw [Finset.prod_image (fun _ _ _ _ h => (s.val.orderEmbOfFin s.property).injective h)]
end Eden
