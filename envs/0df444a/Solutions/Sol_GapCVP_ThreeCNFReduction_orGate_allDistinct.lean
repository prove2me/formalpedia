-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.orGate_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/2b19d75d-3a68-41b8-a94e-f03b917a06ae

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_triple_distinct
import Theorems.Thm_GapCVP_ThreeCNFReduction_paddedBinary_allDistinct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution (a b output : Literal)
    (hab : a.1 ≠ b.1)
    (hao : a.1 ≠ output.1)
    (hbo : b.1 ≠ output.1)
    (ha : a.1 ≠ paddingVariable₀)
    (hb : b.1 ≠ paddingVariable₀)
    (ho : output.1 ≠ paddingVariable₀) :
    allDistinct (orGate a b output) := by
  rw [orGate, allDistinct_append, allDistinct_append,
    allDistinct_singleton]
  refine ⟨⟨paddedBinary_allDistinct _ _ ?_ ?_ ho,
    paddedBinary_allDistinct _ _ ?_ ?_ ho⟩,
    triple_distinct _ _ _ hab ?_ ?_⟩
  · exact hao
  · exact ha
  · exact hbo
  · exact hb
  · exact hao
  · exact hbo
end GapCVP.ThreeCNFReduction
