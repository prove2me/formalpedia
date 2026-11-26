-- Prove2me | solution 1 for BKAR.orderedSimplexIntegralAux_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:01.901675+00:00
-- url     : https://prove2.me/submissions/9c42b590-5d12-4245-8041-f5405c0fa133

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution (top : ℝ) (f : List ℝ → ℝ) :
    orderedSimplexIntegralAux top ([] : List (Edge V)) f = f [] :=
  rfl
end BKAR
