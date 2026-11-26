-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceRealParityTail_subset_sourceParityTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:04.33435+00:00
-- url     : https://prove2.me/submissions/01299869-6852-4d0b-85fe-f5bbca9ec459

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_Terras_parityLowerCutoff_cast_le


set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (htHalf : t ≤ 1 / 2)
    (htM : 2 ≤ t * M) :
    sourceRealParityTail M t ⊆ sourceParityTail M (t / 2) := by
  classical
  intro x hx
  rw [sourceRealParityTail, Finset.mem_filter] at hx
  rw [sourceParityTail, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have htHalf' : t / 2 ≤ 1 / 2 := by linarith
  let K := Terras.parityLowerCutoff (t / 2) M
  have hKcast : (K : ℝ) ≤ (1 / 2 - t / 2) * M := by
    exact Terras.parityLowerCutoff_cast_le htHalf' M
  have hKM : K ≤ M := by
    have hcoef : (1 / 2 - t / 2) * (M : ℝ) ≤ M := by
      have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
      nlinarith
    exact_mod_cast hKcast.trans hcoef
  have hdev :
      t * M < |(sourceCodeOddCount x : ℝ) - (M : ℝ) / 2| := hx.2
  rcases (lt_abs.mp hdev) with hhigh | hlow
  · right
    have hfloorlt :
        (1 / 2 - t / 2) * (M : ℝ) < (K : ℝ) + 1 := by
      exact Nat.lt_floor_add_one _
    have hcast : ((M - K : ℕ) : ℝ) ≤ sourceCodeOddCount x := by
      rw [Nat.cast_sub hKM]
      have hs0 : (0 : ℝ) ≤ sourceCodeOddCount x := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast hcast
  · left
    have hcast :
        ((sourceCodeOddCount x : ℕ) : ℝ) ≤
          (1 / 2 - t / 2) * M := by
      nlinarith
    exact Nat.le_floor hcast
end CollatzEndpointTransport.FixedTotal
