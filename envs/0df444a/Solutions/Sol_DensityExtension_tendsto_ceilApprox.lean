-- Prove2me | solution 1 for DensityExtension.tendsto_ceilApprox
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:17:23.658882+00:00
-- url     : https://prove2.me/submissions/e1416b79-306e-4146-a5fa-1e2d203896fa

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Theorems.Thm_DensityExtension_ceilApprox_ge
import Theorems.Thm_DensityExtension_ceilApprox_coe

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology DensityExtension
open scoped NNReal Topology

/-- Original convergent ceiling-rational approximation, with a pinned scoped import. -/
theorem solution (t : ℝ≥0) :
    Tendsto (ceilApprox t) atTop (𝓝 t) := by
  rw [← NNReal.tendsto_coe]
  have hf_ge : ∀ m : ℕ, (t : ℝ) ≤ (ceilApprox t m : ℝ) :=
    fun m => NNReal.coe_le_coe.mpr (ceilApprox_ge t m)
  have hf_le : ∀ m : ℕ, (ceilApprox t m : ℝ) ≤ (t : ℝ) + 1 / ↑(m + 1) := fun m => by
    rw [ceilApprox_coe]
    have hm_pos : (0 : ℝ) < ↑(m + 1) := by positivity
    calc (↑⌈(t : ℝ) * ↑(m + 1)⌉₊ : ℝ) / ↑(m + 1)
        ≤ ((t : ℝ) * ↑(m + 1) + 1) / ↑(m + 1) :=
          div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le hm_pos.le
      _ = (t : ℝ) + 1 / ↑(m + 1) := by
          rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hm_pos)]
  have h_upper : Tendsto (fun m : ℕ => (t : ℝ) + 1 / ↑(m + 1)) atTop (𝓝 (t : ℝ)) := by
    have h0 : Tendsto (fun m : ℕ => (1 : ℝ) / (↑(m + 1) : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    have := (tendsto_const_nhds (x := (t : ℝ))).add h0
    rwa [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper hf_ge hf_le
