-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_terminalPatterns_by_spend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:57.00991+00:00
-- url     : https://prove2.me/submissions/1d2d4137-2f97-4454-8280-7502b29a7b95

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseSpend_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {R : Type*} [CommSemiring R]
    {N s r : ℕ} (f : ℕ → List ℕ → R) :
    (∑ d ∈ terminalPatternImage N s r, f d.sum d) =
      ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D, f D d := by
  calc
    (∑ d ∈ terminalPatternImage N s r, f d.sum d) =
        ∑ D ∈ range (N + 1),
          ∑ d ∈ terminalPatternSet N s r D, f d.sum d := by
      symm
      simpa [terminalPatternSet] using
        (Finset.sum_fiberwise_of_maps_to
          (s := terminalPatternImage N s r)
          (t := range (N + 1))
          (g := fun d : List ℕ => d.sum)
          (fun d hd => by
            rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
            apply Finset.mem_range.mpr
            exact Nat.lt_succ_of_le (reverseSpend_le (N := N) c r))
          (fun d : List ℕ => f d.sum d))
    _ = ∑ D ∈ range (N + 1),
        ∑ d ∈ terminalPatternSet N s r D, f D d := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro d hd
      rw [(Finset.mem_filter.mp hd).2]
end CollatzEndpointTransport.FixedTotal
