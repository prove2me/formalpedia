-- Prove2me | solution 1 for CompactnessConjecture.encodedJQuotient_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/33f69739-4c3a-46c0-9128-167cd770fb32

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
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsBipartite :=
  encodeFiniteGraph_isBipartite _
    (colorRespectingQuotient_isBipartite jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1)
end CompactnessConjecture
