-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb26_original_uniform_prefix_discounted_setIntegral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:17:40.244199+00:00
-- url     : https://prove2.me/submissions/64170600-a70e-40f0-bba1-840aa1a2618a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T : ℝ) (hT : 0 < T) :
    Tendsto (fun n : ℕ =>
      ∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))
      atTop (𝓝 (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)))  := by
  have hf : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by
    fun_prop
  have hPrimitive : Continuous (fun b : ℝ =>
      ∫ t in (0 : ℝ)..b, Real.exp (-(q * t)) ∂(volume : Measure ℝ)) :=
    intervalIntegral.continuous_primitive
      (fun a b => hf.intervalIntegrable a b) 0
  have hDiv : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hShift :=
      (Filter.tendsto_add_atTop_iff_nat
        (f := fun n : ℕ => T / (n : ℝ))
        (l := 𝓝 (0 : ℝ)) 2).2
        (tendsto_const_div_atTop_nhds_zero_nat T)
    simpa [Nat.cast_add] using hShift
  have hEndTend : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2))
      atTop (𝓝 T) := by
    simpa using (tendsto_const_nhds.sub hDiv)
  have hBase : Tendsto (fun n : ℕ =>
      ∫ t in (0 : ℝ)..(T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))
      atTop (𝓝 (∫ t in (0 : ℝ)..T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ))) :=
    hPrimitive.continuousAt.tendsto.comp hEndTend
  have hPrefix (n : ℕ) :
      0 ≤ T - T / ((n : ℝ) + 2) := by
    have hDen : 1 ≤ (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact sub_nonneg.mpr (div_le_self hT.le hDen)
  have hGrid (n : ℕ) :
      (∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) =
      (∫ t in (0 : ℝ)..(T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) :=
    (intervalIntegral.integral_of_le (hPrefix n)).symm
  have hEnd :
      (∫ t in Ioc (0 : ℝ) T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)) =
      (∫ t in (0 : ℝ)..T, Real.exp (-(q * t)) ∂(volume : Measure ℝ)) :=
    (intervalIntegral.integral_of_le hT.le).symm
  have hFun :
      (fun n : ℕ => ∫ t in Ioc (0 : ℝ) (T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) =
      (fun n : ℕ => ∫ t in (0 : ℝ)..(T - T / ((n : ℝ) + 2)),
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) := by
    funext n
    exact hGrid n
  rw [hFun, hEnd]
  exact hBase
