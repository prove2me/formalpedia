-- Prove2me | solution 1 for Eden.supremum_finiteTimeDimension_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:10:28.000284+00:00
-- url     : https://prove2.me/submissions/4893ab3e-57f9-4f17-94d0-5db1e8800b2c

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_finiteTimeDimension_attractor_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' attractor) = targetDimension c :=
  (finiteTimeDimension_attractor_isGreatest hc ht).csSup_eq
end Eden
