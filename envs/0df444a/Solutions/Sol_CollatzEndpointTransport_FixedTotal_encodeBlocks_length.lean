-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.encodeBlocks_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:47:58.450108+00:00
-- url     : https://prove2.me/submissions/801b9a30-2dae-4e35-b23a-c7c262061a75

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodePart_length
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
    {ks : List ℕ} (hpos : ∀ k ∈ ks, 0 < k) :
    (encodeBlocks ks).length = ks.sum := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have htail : ∀ l ∈ ks, 0 < l :=
        fun l hl => hpos l (by simp [hl])
      simp only [encodeBlocks_cons, List.length_append, List.sum_cons]
      rw [encodePart_length hk, ih htail]
end CollatzEndpointTransport.FixedTotal
