-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_prefix_encodeComposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:16.679609+00:00
-- url     : https://prove2.me/submissions/e7f1412d-150e-448b-a9cb-5850e5c7cbd6

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_replicate_false_append
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_zero_encodeBlocks
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
    {N : ℕ} (u : ℕ) (c : Composition N) :
    wordCorrectionFrom 0 0
        (List.replicate u false ++ encodeBlocks c.blocks) =
      2 ^ u * syracuseNumerator c := by
  rw [wordCorrectionFrom_replicate_false_append]
  simpa [syracuseNumerator] using
    wordCorrectionFrom_zero_encodeBlocks u c.blocks
      (fun k hk => c.blocks_pos hk)
end CollatzEndpointTransport.FixedTotal
