-- Prove2me | solution 1 for FD1D.dyadicTent_mul_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:16.135159+00:00
-- url     : https://prove2.me/submissions/901aa335-acf9-4b22-8d46-ed74f564292e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Transport
import Theorems.Thm_FD1D_dyadicTent_stronglyMeasurable
import Theorems.Thm_FD1D_dyadicTent_integrable
import Theorems.Thm_FD1D_abs_dyadicTent_le_half
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators ENNReal NNReal Topology
open Set MeasureTheory intervalIntegral
namespace FD1D
theorem _root_.solution (l₁ p₁ l₂ p₂ : ℝ) (hp₁ : 0 < p₁) :
    Integrable (fun z => dyadicTent l₁ p₁ z * dyadicTent l₂ p₂ z) := by
  apply (dyadicTent_integrable l₂ p₂).bdd_mul
  · exact (dyadicTent_stronglyMeasurable l₁ p₁).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using abs_dyadicTent_le_half l₁ p₁ z hp₁
end FD1D
