-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_zero_encodeBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:19.778619+00:00
-- url     : https://prove2.me/submissions/ded10b3a-434d-40ec-900a-25458bcb9fa9

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_encodeBlocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (u : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) :
    wordCorrectionFrom u 0 (encodeBlocks ks) =
      2 ^ u * syracuseNumeratorList ks := by
  simpa using wordCorrectionFrom_encodeBlocks u 0 ks hpos
end CollatzEndpointTransport.FixedTotal
