-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.integerCorrection_sourceShellStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:57.423808+00:00
-- url     : https://prove2.me/submissions/f210983b-9625-4f78-b27f-699ab1cb185e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrection_parityVec


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    Terras.integerCorrection M (sourceShellStart x) =
      sourceCodeCorrection x := by
  rw [← wordCorrection_parityVec]
  rw [parityVec_sourceShellStart, ofFn_sourceCodeWord]
  exact wordCorrection_sourceCodeList x
end CollatzEndpointTransport.FixedTotal
