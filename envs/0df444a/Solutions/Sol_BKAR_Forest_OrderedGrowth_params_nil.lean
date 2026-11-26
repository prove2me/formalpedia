-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.params_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:05.978948+00:00
-- url     : https://prove2.me/submissions/f6da7076-74b1-4ec7-9b85-98047cdf5f67

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).params u ts = u :=
  rfl
end BKAR.Forest.OrderedGrowth
