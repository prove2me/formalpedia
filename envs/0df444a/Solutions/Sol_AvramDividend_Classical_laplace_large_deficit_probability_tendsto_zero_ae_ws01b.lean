-- Prove2me | solution 1 for AvramDividend.Classical.laplace_large_deficit_probability_tendsto_zero_ae_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T08:15:17.042172+00:00
-- url     : https://prove2.me/submissions/046bbfd4-dd6b-46b8-9c5d-de95337c5bd6

import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ws01b
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Lattice

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology

/-- The nonnegative-tail Laplace criterion also holds for deficits
    that are nonnegative almost surely at each time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hD : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ D n ω)
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
  let E : ℕ → Ω → ℝ := fun n ω => max (D n ω) 0
  have hE (n : ℕ) (ω : Ω) : 0 ≤ E n ω := by
    exact le_max_right _ _
  have hSet (n : ℕ) :
      {ω : Ω | a ≤ E n ω} = {ω : Ω | a ≤ D n ω} := by
    ext ω
    change (a ≤ max (D n ω) 0) ↔ (a ≤ D n ω)
    constructor
    · intro h
      rcases (le_max_iff).mp h with h' | h'
      · exact h'
      · exact False.elim ((not_le.mpr ha) h')
    · intro h
      exact le_trans h (le_max_left _ _)
  have hMeasE (n : ℕ) : MeasurableSet {ω : Ω | a ≤ E n ω} := by
    rw [hSet n]
    exact hMeas n
  have hIf (n : ℕ) (ω : Ω) :
      (if a ≤ E n ω then (1 - Real.exp (-a) : ℝ) else 0) =
        (if a ≤ D n ω then (1 - Real.exp (-a) : ℝ) else 0) := by
    have hiff : (a ≤ E n ω) ↔ (a ≤ D n ω) := by
      exact Set.ext_iff.mp (hSet n) ω
    simp only [hiff]
  have hLeftE (n : ℕ) :
      Integrable (fun ω => if a ≤ E n ω then
        (1 - Real.exp (-a) : ℝ) else 0) μ :=
    (hLeft n).congr
      (Filter.Eventually.of_forall (fun ω => (hIf n ω).symm))
  have hAeExp (n : ℕ) :
      (fun ω => Real.exp (-E n ω)) =ᵐ[μ]
        (fun ω => Real.exp (-D n ω)) := by
    filter_upwards [hD n] with ω hnonneg
    simp [E, max_eq_left hnonneg]
  have hExpE (n : ℕ) :
      Integrable (fun ω => Real.exp (-E n ω)) μ :=
    (hExp n).congr (hAeExp n).symm
  have hIntegralEq (n : ℕ) :
      (∫ ω, Real.exp (-E n ω) ∂μ) =
        (∫ ω, Real.exp (-D n ω) ∂μ) :=
    integral_congr_ae (hAeExp n)
  have hLaplaceE :
      Tendsto (fun n : ℕ => ∫ ω, Real.exp (-E n ω) ∂μ)
        atTop (𝓝 (μ.real Set.univ)) := by
    simpa only [hIntegralEq] using hLaplace
  have hTendsto :=
    laplace_large_deficit_probability_tendsto_zero_ws01b
      μ E a ha hE hMeasE hLeftE hOne hExpE hLaplaceE
  simpa only [hSet] using hTendsto
