-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.oddCount_sourceCodeEquivResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:28:12.564516+00:00
-- url     : https://prove2.me/submissions/91da0c5c-a1d9-42e5-92f1-b39496900032

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_ofFn
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_sourceCodeList
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_sourceCodeEquivResidue
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_eq_wordWeight


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (M : ℕ) (x : SourceCode M) :
    Terras.oddCount M (sourceCodeEquivResidue M x : ℕ) =
      sourceCodeOddCount x := by
  rw [Terras.oddCount_eq_wordWeight,
    parityVec_sourceCodeEquivResidue]
  rw [← listOddCount_ofFn, ofFn_sourceCodeWord,
    listOddCount_sourceCodeList]
end CollatzEndpointTransport.FixedTotal
