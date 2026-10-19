-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.encodeFormula_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/be38fdbb-e238-4656-a67d-304b6efb7262

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeFormulaFrom_allDistinct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ} (formula : Formula T S) :
    allDistinct (encodeFormula formula) :=
  encodeFormulaFrom_allDistinct 0 (sortedElements formula)
end GapCVP.ThreeCNFReduction
