-- Prove2me | solution 1 for CompactnessConjecture.encodedKQuotient_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/2279aaca-e90b-4ea9-946b-c46c5060b8f6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_quotientGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_encodeFiniteGraph_no_isolated
import Theorems.Thm_CompactnessConjecture_kTemplate_no_isolated

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    GraphHasNoIsolated
      (encodeFiniteGraph (quotientGraph kTemplate f)).graph := by
  exact encodeFiniteGraph_no_isolated (quotientGraph kTemplate f)
    (quotientGraph_no_isolated kTemplate kColor
      (fun _ _ h => kTemplate_adj_color_ne h)
      kTemplate_no_isolated f hf.1)
end CompactnessConjecture
