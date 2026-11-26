-- Prove2me | solution 1 for FD1D.dyadicTent_mul_eq_zero_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:17.040447+00:00
-- url     : https://prove2.me/submissions/33646f22-c209-491f-9b3a-bf61857373fa

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_ne_zero_mem_Ioo
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution {l₁ p₁ l₂ p₂ z : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hsep : l₁ + p₁ ≤ l₂ ∨ l₂ + p₂ ≤ l₁) :
    dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z = 0 := by
  by_cases h1 : dyadicTent l₁ p₁ z = 0
  · simp [h1]
  by_cases h2 : dyadicTent l₂ p₂ z = 0
  · simp [h2]
  have hm1 := dyadicTent_ne_zero_mem_Ioo hp₁ h1
  have hm2 := dyadicTent_ne_zero_mem_Ioo hp₂ h2
  rcases hsep with hsep | hsep
  · exfalso
    linarith [hm1.2, hm2.1]
  · exfalso
    linarith [hm2.2, hm1.1]
end FD1D
