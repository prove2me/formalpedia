-- Prove2me | solution 1 for FD1D.DyadicMass.dyadicTent_scale_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:05.984055+00:00
-- url     : https://prove2.me/submissions/ef3b7289-f46e-4698-a83f-1654557907c9

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
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
theorem _root_.solution (l p z : ℝ) (hp : p ≠ 0) :
    dyadicTent (l / 2) (p / 2) z = dyadicTent l p (2 * z) := by
  have hL : z ∈ Icc (l / 2) (l / 2 + (p / 2) / 2) ↔
      2 * z ∈ Icc l (l + p / 2) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hR : z ∈ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2) ↔
      2 * z ∈ Ioc (l + p / 2) (l + p) := by
    simp only [mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  by_cases hzL : z ∈ Icc (l / 2) (l / 2 + (p / 2) / 2)
  · have h2zL := hL.mp hzL
    have hzR : z ∉ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2) := by
      intro h
      linarith [hzL.2, h.1]
    have h2zR : 2 * z ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
    rw [dyadicTent, dyadicTent, indicator_of_mem hzL,
      indicator_of_notMem hzR, indicator_of_mem h2zL,
      indicator_of_notMem h2zR]
    field_simp [hp]
  · have h2zL : 2 * z ∉ Icc l (l + p / 2) := hL.not.mp hzL
    by_cases hzR : z ∈ Ioc (l / 2 + (p / 2) / 2) (l / 2 + p / 2)
    · have h2zR := hR.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_mem hzR, indicator_of_notMem h2zL,
        indicator_of_mem h2zR]
      field_simp [hp]
    · have h2zR : 2 * z ∉ Ioc (l + p / 2) (l + p) := hR.not.mp hzR
      rw [dyadicTent, dyadicTent, indicator_of_notMem hzL,
        indicator_of_notMem hzR, indicator_of_notMem h2zL,
        indicator_of_notMem h2zR]
end FD1D.DyadicMass
