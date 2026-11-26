-- Prove2me | solution 1 for FD1D.DyadicMass.haarCombination_eq_zero_of_outside
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:04.018953+00:00
-- url     : https://prove2.me/submissions/1ba3039f-4486-4795-8527-b00a5d58ed0f

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_ne_zero_mem_Ioo
import Theorems.Thm_FD1D_haarNodeWidth_pos
import Theorems.Thm_FD1D_DyadicMass_haarNodeLeft_nonneg
import Theorems.Thm_FD1D_DyadicMass_haarNodeRight_le_one
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution {L : ℕ}
    (b : CompleteHaarNode L → ℝ) {z : ℝ} (hz : z ≤ 0 ∨ 1 ≤ z) :
    haarCombination haarNodeLeft haarNodeWidth b z = 0 := by
  unfold haarCombination
  apply Finset.sum_eq_zero
  intro v _
  suffices dyadicTent (haarNodeLeft v) (haarNodeWidth v) z = 0 by
    simp [this]
  by_contra h
  have hm := dyadicTent_ne_zero_mem_Ioo (haarNodeWidth_pos v) h
  rcases hz with hz | hz
  · linarith [hm.1, haarNodeLeft_nonneg v]
  · linarith [hm.2, haarNodeRight_le_one v]
end FD1D.DyadicMass
