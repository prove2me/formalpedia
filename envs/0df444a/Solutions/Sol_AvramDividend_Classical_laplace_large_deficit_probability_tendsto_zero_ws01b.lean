-- Prove2me | solution 1 for AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:06:07.821312+00:00
-- url     : https://prove2.me/submissions/4183c60e-b218-4f61-8895-a5a27309d4ea

import Mathlib
import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_bound_ws01b
import Mathlib.Order.Filter.Tendsto
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology
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
  have hc : 0 < 1 - Real.exp (-a) := by
    have := Real.exp_lt_one_iff.2 (by linarith : -a < 0); linarith
  have hb : ∀ n, μ.real {ω : Ω | a ≤ D n ω} ≤
      (μ.real Set.univ - ∫ ω, Real.exp (-D n ω) ∂μ) / (1 - Real.exp (-a)) := by
    intro n
    rw [le_div_iff₀ hc, mul_comm]
    exact AvramDividend.Classical.laplace_large_deficit_probability_bound_ws01b μ (D n) a ha (hD n) (hMeas n)
      (hLeft n) (hOne.sub (hExp n)) hOne (hExp n)
  have hlim : Tendsto (fun n => (μ.real Set.univ - ∫ ω, Real.exp (-D n ω) ∂μ) / (1 - Real.exp (-a)))
      atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := μ.real Set.univ)).sub hLaplace
    simpa using this.div_const (1 - Real.exp (-a))
  exact squeeze_zero (fun n => measureReal_nonneg) hb hlim
