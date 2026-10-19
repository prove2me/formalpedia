-- Prove2me | solution 1 for CompactnessConjecture.encodedJQuotient_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/c7ac545b-843f-481a-a817-87d328f9f689

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_quotientGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_jTemplate_no_isolated

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph jTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph jTemplate f)
    (quotientGraph_no_isolated jTemplate jColor
      (fun _ _ h => jTemplate_adj_color_ne h)
      jTemplate_no_isolated f hf.1)
end CompactnessConjecture
