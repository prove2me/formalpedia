-- Prove2me | solution 1 for FD1D.DyadicMass.uniformArrivalMass_piecewiseCDF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:19:10.808634+00:00
-- url     : https://prove2.me/submissions/2e8a2a2c-2c45-49c0-80fd-e1fadda4e46e

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
import Theorems.Thm_FD1D_DeletionRule_kernel_apply
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_SupplyConfiguration_countState_apply
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.DeletionRule.kernel_apply
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.SupplyConfiguration.countState_apply
attribute [local simp] FD1D.weightedLevel_zero


section
namespace FD1D
noncomputable section
open Set MeasureTheory
namespace DyadicMass
private theorem piecewiseCDF_constantLeafMass
    (L : ℕ) (c : ℝ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (constantLeafMass L c).piecewiseCDF z =
      ((2 ^ L : ℕ) : ℝ) * c * z := by
  induction L generalizing z with
  | zero =>
      simp [constantLeafMass, piecewiseCDF]
  | succ L ih =>
      simp only [constantLeafMass, piecewiseCDF]
      by_cases hhalf : z ≤ 1 / 2
      · rw [if_pos hhalf, ih ⟨by linarith [hz.1], by linarith⟩]
        rw [pow_succ]
        push_cast
        ring
      · rw [if_neg hhalf, total_constantLeafMass,
          ih ⟨by linarith, by linarith [hz.2]⟩]
        rw [pow_succ]
        push_cast
        ring
end DyadicMass
end
end FD1D
end

set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass
namespace FD1D.DyadicMass
theorem _root_.solution
    (L : ℕ) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) :
    (uniformArrivalMass L).piecewiseCDF z = z := by
  rw [uniformArrivalMass, piecewiseCDF_constantLeafMass L _ hz]
  have hpow : (((2 ^ L : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp
end FD1D.DyadicMass
