-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:02.137806+00:00
-- url     : https://prove2.me/submissions/d7ed3e7f-d187-4704-aa6b-d220f2bb0f9a

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero


attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (i c : ℕ) (xs ys : List Bool) :
    wordCorrectionFrom i c (xs ++ ys) =
      wordCorrectionFrom (i + xs.length)
        (wordCorrectionFrom i c xs) ys := by
  induction xs generalizing i c with
  | nil => simp
  | cons b bs ih =>
      rw [List.cons_append, wordCorrectionFrom_cons, ih]
      simp [wordCorrectionFrom_cons, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm]
end CollatzEndpointTransport.FixedTotal
