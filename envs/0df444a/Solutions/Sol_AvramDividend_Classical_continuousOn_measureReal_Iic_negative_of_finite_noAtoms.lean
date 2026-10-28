-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_measureReal_Iic_negative_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:13:53.94605+00:00
-- url     : https://prove2.me/submissions/fc097788-3a05-434c-97d3-643f5adc51a3

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_measureReal_Iic_of_finite_noAtoms

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

/-- Localise to a finite measure above each negative evaluation point. -/
theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ a : ℝ, a < 0 → μ (Iic a) ≠ ⊤) :
    ContinuousOn (fun a : ℝ => μ.real (Iic a)) (Iio (0 : ℝ)) := by
  intro x hx
  have hxneg : x < (0 : ℝ) := hx
  let c : ℝ := x / 2
  have hxc : x < c := by dsimp [c]; linarith
  have hcneg : c < 0 := by dsimp [c]; linarith
  let ν : Measure ℝ := μ.restrict (Iic c)
  have hle (y : ℝ) : ν (Iic y) ≤ μ (Iic c) := by
    calc
      ν (Iic y) = μ (Iic y ∩ Iic c) := by simp [ν, Measure.restrict_apply]
      _ ≤ μ (Iic c) := measure_mono Set.inter_subset_right
  have hνfin (y : ℝ) : ν (Iic y) ≠ ⊤ := by
    intro htop
    have hbad : (⊤ : ENNReal) ≤ μ (Iic c) := by
      simpa [htop] using hle y
    exact hfin c hcneg (top_unique hbad)
  have hcontν : Continuous (fun z : ℝ => ν.real (Iic z)) :=
    AvramDividend.Classical.continuous_measureReal_Iic_of_finite_noAtoms ν hνfin
  have hevent : (fun z : ℝ => μ.real (Iic z)) =ᶠ[𝓝 x]
      (fun z : ℝ => ν.real (Iic z)) := by
    filter_upwards [isOpen_Iio.mem_nhds hxc] with y hy
    have hyc : Iic y ⊆ Iic c :=
      Iic_subset_Iic.mpr (le_of_lt hy)
    have hμν : μ (Iic y) = ν (Iic y) := by
      calc
        μ (Iic y) = μ (Iic y ∩ Iic c) := by rw [Set.inter_eq_left.mpr hyc]
        _ = ν (Iic y) := by simp [ν, Measure.restrict_apply]
    simpa [Measure.real] using congrArg ENNReal.toReal hμν
  exact (hcontν.continuousAt.congr_of_eventuallyEq hevent).continuousWithinAt
