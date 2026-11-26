-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_replicate_false_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:28:09.037701+00:00
-- url     : https://prove2.me/submissions/55b10d80-3f3a-4502-a2e7-a31cee852905

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
    (i c r : ℕ) (ys : List Bool) :
    wordCorrectionFrom i c (List.replicate r false ++ ys) =
      wordCorrectionFrom (i + r) c ys := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
      rw [List.replicate_succ, List.cons_append, wordCorrectionFrom_cons]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
end CollatzEndpointTransport.FixedTotal
