-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_congr_of_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:58:42.3396+00:00
-- url     : https://prove2.me/submissions/d2801182-0a4e-4ca7-9e22-da4956cf72f9

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr_of_length

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution {order : List (Edge V)}
    {f g : List ℝ → ℝ}
    (hfg : ∀ ts, ts.length = order.length → f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by
  rw [orderedSimplexIntegral]
  exact orderedSimplexIntegralAux_congr_of_length 1 order hfg
end BKAR
