-- Prove2me | solution 1 for GapCVP.CLVerifier.encodedTableau_mem_threeSAT_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/b9516f2f-dc64-4344-9220-92db905c8267

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_encodeTableau_satisfiable_iff_validTrace
import Theorems.Thm_GapCVP_CLVerifier_threeSATLanguage_encode_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CLVerifier
open Computability GapCVP.CL
namespace GapCVP.CLVerifier
theorem _root_.solution
    {bound : Polynomial ℕ}
    {verifier : List Bool × List Bool → Bool}
    {machine : VerifierTM verifier}
    (simulation : TableauSimulation bound machine)
    (x : List Bool) :
    threeSATLanguage (encodedTableau simulation x) ↔
      Nonempty (AcceptedExecution bound machine x) := by
  unfold encodedTableau
  exact
    (threeSATLanguage_encode_iff
      (ThreeCNFReduction.encodeTableau (simulation.specification x))).trans
      ((ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace
        (simulation.specification x)).trans (simulation.correct x))
end GapCVP.CLVerifier
