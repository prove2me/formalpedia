-- Prove2me | solution 1 for CompactnessConjecture.encodedJQuotient_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/71deefdb-c151-4ab7-b476-45e651ded01c

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_jTemplate_connected
import Theorems.Thm_CompactnessConjecture_quotientGraph_connected_of_colorRespecting
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_connected

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution {f : JVertex → JVertex}
    (hf : JAdmissible f) :
    (encodeFiniteGraph (quotientGraph jTemplate f)).graph.Connected :=
  encodeFiniteGraph_connected _
    (quotientGraph_connected_of_colorRespecting jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h) f hf.1 jTemplate_connected)
end CompactnessConjecture
