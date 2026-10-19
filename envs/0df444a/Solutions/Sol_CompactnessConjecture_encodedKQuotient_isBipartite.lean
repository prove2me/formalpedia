-- Prove2me | solution 1 for CompactnessConjecture.encodedKQuotient_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/d8b8d243-573b-4270-b78d-54d728ba2141

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_colorRespectingQuotient_isBipartite
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_isBipartite

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h) f hf.1)
end CompactnessConjecture
