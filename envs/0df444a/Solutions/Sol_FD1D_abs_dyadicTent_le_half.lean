-- Prove2me | solution 1 for FD1D.abs_dyadicTent_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:28:05.395695+00:00
-- url     : https://prove2.me/submissions/f7f6b30a-2ad5-49ba-9da8-6f61c88e093e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution (l p z : ℝ) (hp : 0 < p) :
    |dyadicTent l p z| ≤ 1 / 2 := by
  by_cases hL : z ∈ Icc l (l + p / 2)
  · have hR : z ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [hL.2, h.1]
    rw [dyadicTent]
    simp only [Set.indicator_of_mem hL, Set.indicator_of_notMem hR, add_zero]
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hL.1) hp.le)]
    exact (div_le_iff₀ hp).2 (by linarith [hL.2])
  · by_cases hR : z ∈ Ioc (l + p / 2) (l + p)
    · rw [dyadicTent]
      simp only [Set.indicator_of_notMem hL, Set.indicator_of_mem hR, zero_add]
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr hR.2) hp.le)]
      exact (div_le_iff₀ hp).2 (by linarith [hR.1])
    · simp [dyadicTent, hL, hR]
end FD1D
