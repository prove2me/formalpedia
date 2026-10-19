-- Prove2me | solution 1 for CompactnessConjecture.encodedKQuotient_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/2f1d81d2-d3e5-4a76-a79a-504eb63cfeb3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_kTemplate_connected
import Theorems.Thm_CompactnessConjecture_quotientGraph_connected_of_colorRespecting
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_connected

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {f : KVertex → KVertex}
    (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1 kTemplate_connected)
end CompactnessConjecture
