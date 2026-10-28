-- Prove2me | solution 2 for AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T08:07:07.288505+00:00
-- url     : https://prove2.me/submissions/0f3dc5ca-b0da-45eb-a0cb-add2653f811e

import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_bound_ws01b
import Mathlib.Order.Filter.Tendsto
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology

/-- Laplace convergence at the total mass forces every fixed positive
    deficit tail to vanish in measure. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hD : ∀ n ω, 0 ≤ D n ω)
    (hMeas : ∀ n, MeasurableSet {ω : Ω | a ≤ D n ω})
    (hLeft : ∀ n, Integrable
      (fun ω => if a ≤ D n ω then (1 - Real.exp (-a) : ℝ) else 0) μ)
    (hOne : Integrable (fun _ : Ω => (1 : ℝ)) μ)
    (hExp : ∀ n, Integrable (fun ω => Real.exp (-D n ω)) μ)
    (hLaplace : Tendsto
      (fun n : ℕ => ∫ ω, Real.exp (-D n ω) ∂μ)
      atTop (𝓝 (μ.real Set.univ))) :
    Tendsto (fun n : ℕ => μ.real {ω : Ω | a ≤ D n ω})
      atTop (𝓝 (0 : ℝ)) := by
  have hbexp : Real.exp (-a) < (1 : ℝ) := by
    calc
      Real.exp (-a) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hb : 0 < (1 - Real.exp (-a) : ℝ) := by linarith
  have hLow (n : ℕ) :
      0 ≤ μ.real {ω : Ω | a ≤ D n ω} :=
    measureReal_nonneg
  have hHigh (n : ℕ) :
      μ.real {ω : Ω | a ≤ D n ω} ≤
        (μ.real Set.univ -
          (∫ ω, Real.exp (-D n ω) ∂μ)) /
          (1 - Real.exp (-a)) := by
    have hGap : Integrable
        (fun ω => (1 : ℝ) - Real.exp (-D n ω)) μ :=
      hOne.sub (hExp n)
    have hBound :=
      laplace_large_deficit_probability_bound_ws01b
        μ (D n) a ha (hD n) (hMeas n)
        (hLeft n) hGap hOne (hExp n)
    exact (le_div_iff₀ hb).2 (by simpa only [mul_comm] using hBound)
  have hTop :
      Tendsto
        (fun n : ℕ => (μ.real Set.univ -
          (∫ ω, Real.exp (-D n ω) ∂μ)) /
          (1 - Real.exp (-a))) atTop (𝓝 (0 : ℝ)) := by
    have hConstant :
        Tendsto (fun _ : ℕ => μ.real Set.univ)
          atTop (𝓝 (μ.real Set.univ)) :=
      tendsto_const_nhds
    have hSub :
        Tendsto (fun n : ℕ => μ.real Set.univ -
          (∫ ω, Real.exp (-D n ω) ∂μ))
          atTop (𝓝 (0 : ℝ)) := by
      simpa using hConstant.sub hLaplace
    have hDiv := hSub.div_const (1 - Real.exp (-a))
    simpa using hDiv
  exact squeeze_zero hLow hHigh hTop
