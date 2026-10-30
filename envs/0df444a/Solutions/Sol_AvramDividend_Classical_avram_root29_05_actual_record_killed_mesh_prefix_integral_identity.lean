-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:44:38.355018+00:00
-- url     : https://prove2.me/submissions/0668bc7a-e13e-4d76-bc21-8a5ee86d516d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_record_increment
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_cell_integral_eq_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical

/-- Integrating the killed sampled payment weight over the first N rational
cells against the actual runningSup Stieltjes regulator gives exact record cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) (n N : ℕ) :
    let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
    (∫⁻ r in Ioc (u 0) (u N),
      (let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
       if ENNReal.ofReal e < τ then
         ENNReal.ofReal (Real.exp (-(q * e))) else 0)
        ∂(dividendMeasure (runningSup X) ω)) =
    ∑ k ∈ Finset.range N,
      (if ENNReal.ofReal (u (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
      ENNReal.ofReal
        (runningSup X (u (k + 1)).toNNReal ω -
          runningSup X (u k).toNNReal ω) := by
  let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let f : ℝ → ℝ≥0∞ := fun r =>
    let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
    if ENNReal.ofReal e < τ then
      ENNReal.ofReal (Real.exp (-(q * e))) else 0
  have hu : Monotone u := by
    intro i j hij
    dsimp [u]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hcell (k : ℕ) :
      (∫⁻ r in Ioc (u k) (u (k + 1)), f r ∂μ) =
      (if ENNReal.ofReal (u (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
        ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
          runningSup X (u k).toNNReal ω) := by
    have hm := runningSup_dividendMeasure_Ioc_eq_record_increment
      X ω (u k) (u (k + 1))
    have hc := avram_root29_05_killed_mesh_cell_integral_eq_mass μ q τ n k
    calc
      _ = (if ENNReal.ofReal (u (k + 1)) < τ then
            ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
          μ (Ioc (u k) (u (k + 1))) := by
            simpa [f, μ, u, Nat.cast_add] using hc
      _ = _ := by rw [hm]
  change (∫⁻ r in Ioc (u 0) (u N), f r ∂μ) =
    ∑ k ∈ Finset.range N,
      (if ENNReal.ofReal (u (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
        ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
          runningSup X (u k).toNNReal ω)
  rw [lintegral_Ioc_partition_fin μ f u hu N]
  exact Finset.sum_congr rfl (fun k _ => hcell k)
