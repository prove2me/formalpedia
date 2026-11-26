-- Prove2me | solution 1 for BKAR.Forest.orderedContribution_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:02:32.48883+00:00
-- url     : https://prove2.me/submissions/05fedff7-126f-40eb-931c-954a4c8036ac

import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_Forest_empty_standardInterp
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegral_nil



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (ρ : (Edge V → ℝ) → ℝ) :
    (Forest.empty V).orderedContribution [] ρ = ρ zeroConfig := by
  rw [orderedContribution, orderedSimplexIntegral_nil]
  rw [List.reverse_nil, mixedPartialList_nil_apply]
  rw [Forest.empty_standardInterp]
end BKAR.Forest
