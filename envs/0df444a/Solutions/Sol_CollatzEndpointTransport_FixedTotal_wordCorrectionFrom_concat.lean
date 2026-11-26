-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_concat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:08.417372+00:00
-- url     : https://prove2.me/submissions/176b98dc-88dd-485f-a47a-3b507db1c8ed

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_append
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
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
    (i c : ℕ) (xs : List Bool) (b : Bool) :
    wordCorrectionFrom i c (xs.concat b) =
      if b then
        3 * wordCorrectionFrom i c xs + 2 ^ (i + xs.length)
      else
        wordCorrectionFrom i c xs := by
  rw [List.concat_eq_append, wordCorrectionFrom_append]
  simp [wordCorrectionFrom_cons]
end CollatzEndpointTransport.FixedTotal
