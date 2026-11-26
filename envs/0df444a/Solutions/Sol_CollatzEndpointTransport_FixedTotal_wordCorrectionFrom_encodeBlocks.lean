-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_encodeBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:09.912777+00:00
-- url     : https://prove2.me/submissions/a3e5b2da-2ee2-42e4-9972-08f79fa28cc5

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_replicate_false_append
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
    (u c : ℕ) (ks : List ℕ)
    (hpos : ∀ k ∈ ks, 0 < k) :
    wordCorrectionFrom u c (encodeBlocks ks) =
      3 ^ ks.length * c + 2 ^ u * syracuseNumeratorList ks := by
  induction ks generalizing u c with
  | nil => simp
  | cons k ks ih =>
      have hk : 0 < k := hpos k (by simp)
      have htail : ∀ l ∈ ks, 0 < l :=
        fun l hl => hpos l (by simp [hl])
      rw [encodeBlocks_cons, encodePart]
      simp only [List.cons_append, wordCorrectionFrom_cons, if_true]
      rw [wordCorrectionFrom_replicate_false_append]
      have htime : u + 1 + (k - 1) = u + k := by omega
      rw [htime, ih (u := u + k) (c := 3 * c + 2 ^ u) htail]
      simp only [syracuseNumeratorList_cons, List.length_cons, pow_succ]
      rw [pow_add]
      ring
end CollatzEndpointTransport.FixedTotal
