-- Prove2me | solution 1 for FD1D.DyadicMass.haarCombination_rightNode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:42.381828+00:00
-- url     : https://prove2.me/submissions/701c7d8e-f1fd-4b88-91bc-8c52bee0dc5b

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_haarNodeWidth_pos
import Theorems.Thm_FD1D_DyadicMass_dyadicTent_scale_right

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
      dyadicTent (haarNodeLeft (rightNode v)) (haarNodeWidth (rightNode v)) z) =
      haarCombination haarNodeLeft haarNodeWidth b (2 * z - 1) := by
  unfold haarCombination
  apply Finset.sum_congr rfl
  intro v _
  rw [haarNodeLeft_rightNode, haarNodeWidth_rightNode,
    dyadicTent_scale_right _ _ _ (haarNodeWidth_pos v).ne']
end FD1D.DyadicMass
