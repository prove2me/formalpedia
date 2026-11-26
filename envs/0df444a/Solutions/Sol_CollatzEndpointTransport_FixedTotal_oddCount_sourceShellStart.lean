-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.oddCount_sourceShellStart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:43.775429+00:00
-- url     : https://prove2.me/submissions/4ac0060d-b222-4093-98f4-d3cb91692a8e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceShellStart
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_ofFn
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_sourceCodeList
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_wordWeight


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} (x : SourceCode M) :
    Terras.oddCount M (sourceShellStart x) =
      sourceCodeOddCount x := by
  rw [Terras.oddCount_eq_wordWeight, parityVec_sourceShellStart]
  rw [← listOddCount_ofFn, ofFn_sourceCodeWord,
    listOddCount_sourceCodeList]
end CollatzEndpointTransport.FixedTotal
