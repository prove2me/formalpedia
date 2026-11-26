-- Prove2me | solution 1 for FD1D.dyadicTent_ne_zero_mem_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:10:16.401468+00:00
-- url     : https://prove2.me/submissions/fe8ac55a-7143-4a60-881a-102ce0df7e1d

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_eq_zero_of_not_mem
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution {l p z : ℝ} (hp : 0 < p)
    (hz : dyadicTent l p z ≠ 0) :
    z ∈ Ioo l (l + p) := by
  have hmem : z ∈ Icc l (l + p) := by
    by_contra hout
    exact hz (dyadicTent_eq_zero_of_not_mem hp.le hout)
  have hneL : z ≠ l := by
    intro heq
    subst z
    have hL : l ∈ Icc l (l + p / 2) := by constructor <;> linarith
    have hR : l ∉ Ioc (l + p / 2) (l + p) := by
      intro h
      linarith [h.1]
    simp [dyadicTent, hL, hR] at hz
  have hneR : z ≠ l + p := by
    intro heq
    subst z
    have hL : l + p ∉ Icc l (l + p / 2) := by
      intro h
      linarith [h.2]
    have hR : l + p ∈ Ioc (l + p / 2) (l + p) := by
      constructor <;> linarith
    simp [dyadicTent, hL, hR] at hz
  exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hneL), lt_of_le_of_ne hmem.2 hneR⟩
end FD1D
