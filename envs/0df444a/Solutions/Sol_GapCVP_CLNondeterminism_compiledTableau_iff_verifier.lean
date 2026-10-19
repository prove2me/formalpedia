-- Prove2me | solution 1 for GapCVP.CLNondeterminism.compiledTableau_iff_verifier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/d3e684a4-e311-4330-b5c0-8ee482195c27

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_CLVerifier_encodedTableau_mem_threeSAT_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.CLNondeterminism
open Computability GapCVP.CLVerifier
namespace GapCVP.CLNondeterminism
theorem _root_.solution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (compiler : LocalTableauCompiler bound machine)
    (x : List Bool) :
    threeSATLanguage
      (encodedTableau
        (tableauSimulationOfLocalCompiler bound machine compiler) x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by
  exact (encodedTableau_mem_threeSAT_iff
    (tableauSimulationOfLocalCompiler bound machine compiler) x).trans
    (acceptedExecution_iff bound machine x)
end GapCVP.CLNondeterminism
