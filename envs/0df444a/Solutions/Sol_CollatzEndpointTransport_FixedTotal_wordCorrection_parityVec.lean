-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.wordCorrection_parityVec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:06.305183+00:00
-- url     : https://prove2.me/submissions/26c5a4ee-5ff7-4401-a392-2cf66dc2aee2

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_concat
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_parityVec_castSucc
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_succ
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
    (M n : ℕ) :
    wordCorrectionFrom 0 0 (List.ofFn (Terras.parityVec M n)) =
      Terras.integerCorrection M n := by
  induction M with
  | zero => simp [wordCorrectionFrom, Terras.integerCorrection]
  | succ M ih =>
      rw [List.ofFn_succ']
      have hprefix :
          List.ofFn
              (fun i : Fin M =>
                Terras.parityVec (M + 1) n i.castSucc) =
            List.ofFn (Terras.parityVec M n) := by
        rw [parityVec_castSucc]
      rw [hprefix, wordCorrectionFrom_concat, ih,
        Terras.integerCorrection_succ]
      simp [Terras.parityVec]
end CollatzEndpointTransport.FixedTotal
