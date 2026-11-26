-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.cohortEndpoint_eq_iff_numeratorResidue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:41.366397+00:00
-- url     : https://prove2.me/submissions/4d10674f-3892-4811-99e1-08a691de96d5

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointBridge
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_encodeBlocks_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_collision_modEq_numerator
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_eq_iff_correction_modEq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_wordCorrectionFrom_nil
import Theorems.Thm_CollatzEndpointTransport_Terras_integerCorrection_zero
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.encodeBlocks_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.wordCorrectionFrom_nil
attribute [local simp] CollatzEndpointTransport.Terras.integerCorrection_zero



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.endpointCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M s : ℕ} (u : Fin M)
    {c d : Composition (M - (u : ℕ))}
    (hc : c ∈ fixedSet (M - (u : ℕ)) s)
    (hd : d ∈ fixedSet (M - (u : ℕ)) s) :
    cohortEndpoint u c = cohortEndpoint u d ↔
      cohortNumeratorResidue (s := s) c =
        cohortNumeratorResidue (s := s) d := by
  have hcLen : c.length = s := (Finset.mem_filter.mp hc).2
  have hdLen : d.length = s := (Finset.mem_filter.mp hd).2
  constructor
  · intro hout
    apply Fin.ext
    exact sourceEndpoint_collision_modEq_numerator
      u c d hcLen hdLen hout
  · intro hres
    have hnum :
        Nat.ModEq (3 ^ s) (syracuseNumerator c)
          (syracuseNumerator d) := by
      rw [Nat.ModEq]
      exact congrArg Fin.val hres
    have hcorr :
        Nat.ModEq (3 ^ s)
          (2 ^ (u : ℕ) * syracuseNumerator c)
          (2 ^ (u : ℕ) * syracuseNumerator d) :=
      Nat.ModEq.mul_left _ hnum
    exact
      (sourceEndpoint_eq_iff_correction_modEq
        (M := M) (s := s)
        (x := (Sum.inr ⟨u, c⟩ : SourceCode M))
        (y := (Sum.inr ⟨u, d⟩ : SourceCode M))
        (by simpa [sourceCodeOddCount] using hcLen)
        (by simpa [sourceCodeOddCount] using hdLen)).2 <| by
          simpa [sourceCodeCorrection] using hcorr
end CollatzEndpointTransport.FixedTotal
