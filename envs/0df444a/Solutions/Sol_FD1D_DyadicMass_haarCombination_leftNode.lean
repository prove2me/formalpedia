-- Prove2me | solution 1 for FD1D.DyadicMass.haarCombination_leftNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:38.794797+00:00
-- url     : https://prove2.me/submissions/9a7738b3-aa07-4e61-9898-ae145f54dd3e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_haarNodeWidth_pos
import Theorems.Thm_FD1D_DyadicMass_dyadicTent_scale_left

set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ} (b : CompleteHaarNode L → ℝ)
    (z : ℝ) :
    (∑ v : CompleteHaarNode L, b v *
      dyadicTent (haarNodeLeft (leftNode v)) (haarNodeWidth (leftNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z) := by
  unfold haarCombination
  apply Finset.sum_congr rfl
  intro v _
  rw [haarNodeLeft_leftNode, haarNodeWidth_leftNode,
    dyadicTent_scale_left _ _ _ (haarNodeWidth_pos v).ne']
end FD1D.DyadicMass
