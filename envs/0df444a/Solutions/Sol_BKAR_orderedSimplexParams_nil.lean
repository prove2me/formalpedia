-- Prove2me | solution 1 for BKAR.orderedSimplexParams_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:25.080549+00:00
-- url     : https://prove2.me/submissions/1d8b87b1-c04d-44a1-957e-048ee6359d53

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top : ℝ) :
    OrderedSimplexParams top [] :=
  trivial
end BKAR
