-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulusCode_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:43:44.681785+00:00
-- url     : https://prove2.me/submissions/3a8d9c6d-da1b-4bd1-8bb7-44ac3aa08696

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (H : ℕ) :
    Function.Injective (binomialAnnulusCode H) := by
  intro k l hkl
  have hside := congrArg Prod.fst hkl
  have hdist := congrArg Prod.snd hkl
  by_cases hk : k ≤ H / 2 <;> by_cases hl : l ≤ H / 2
  · simp [binomialAnnulusCode, binomialCenterDistance, hk, hl] at hdist
    omega
  · simp [binomialAnnulusCode, hk, hl] at hside
  · simp [binomialAnnulusCode, hk, hl] at hside
  · simp [binomialAnnulusCode, binomialCenterDistance, hk, hl] at hdist
    omega
end CollatzEndpointTransport.FixedTotal
