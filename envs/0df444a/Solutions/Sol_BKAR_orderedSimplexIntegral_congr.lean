-- Prove2me | solution 1 for BKAR.orderedSimplexIntegral_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:17:52.38255+00:00
-- url     : https://prove2.me/submissions/0547b9af-fdff-4da3-8555-bc125a7d57b6

import Definitions.Def_BKAR_OrderedForest
import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_congr

set_option autoImplicit false
noncomputable section
open BKAR
variable {V : Type*} [DecidableEq V]
namespace BKAR
theorem _root_.solution {order : List (Edge V)}
    {f g : List ℝ → ℝ} (hfg : ∀ ts, f ts = g ts) :
    orderedSimplexIntegral order f = orderedSimplexIntegral order g := by
  rw [orderedSimplexIntegral]
  exact orderedSimplexIntegralAux_congr 1 order hfg
end BKAR
