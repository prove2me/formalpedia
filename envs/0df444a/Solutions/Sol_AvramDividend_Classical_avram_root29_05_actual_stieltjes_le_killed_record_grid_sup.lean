-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_actual_stieltjes_le_killed_record_grid_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:50:34.457566+00:00
-- url     : https://prove2.me/submissions/f95b65be-9e70-40c9-a118-e0c0cd3dcc8a

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_fatou_lower_integral
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_positive_time_rational_prefix_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BigOperators Classical

/-- The original pathwise strictly stopped Stieltjes regulator reward is bounded
by the supremum of its actual killed countable sampled record cash prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂(dividendMeasure (runningSup X) ω)) ≤
    ⨆ n : ℕ, ⨆ N : ℕ,
      (let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (u (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
         ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
           runningSup X (u k).toNNReal ω)) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  let f : ℕ → ℝ → ℝ≥0∞ := fun n r =>
    let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
    if ENNReal.ofReal e < τ then
      ENNReal.ofReal (Real.exp (-(q * e))) else 0
  let G : ℕ → ℕ → ℝ≥0∞ := fun n N =>
    let u : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
    ∑ k ∈ Finset.range N,
      (if ENNReal.ofReal (u (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * u (k + 1)))) else 0) *
      ENNReal.ofReal (runningSup X (u (k + 1)).toNNReal ω -
        runningSup X (u k).toNNReal ω)
  have hprefix (n N : ℕ) :
      (∫⁻ r in Ioc (0 : ℝ) ((N : ℝ) / ((n : ℝ) + 1)),
        f n r ∂μ) = G n N := by
    simpa [f, G, μ, Nat.cast_add] using
      (avram_root29_05_actual_record_killed_mesh_prefix_integral_identity
        X ω q τ n N)
  have hpos (n : ℕ) :
      (∫⁻ r : ℝ, if 0 < r then f n r else 0 ∂μ) =
        (∫⁻ r in Ioi (0 : ℝ), f n r ∂μ) := by
    rw [← lintegral_indicator measurableSet_Ioi (f n)]
    apply lintegral_congr
    intro r
    by_cases hr : 0 < r <;> simp [Set.indicator, hr]
  have hgrid (n : ℕ) :
      (∫⁻ r : ℝ, if 0 < r then f n r else 0 ∂μ) =
        ⨆ N : ℕ, G n N := by
    rw [hpos n, avram_root29_05_positive_time_rational_prefix_exhaustion
      μ (f n) n]
    exact iSup_congr (hprefix n)
  have hFatou := avram_root29_05_killed_mesh_fatou_lower_integral μ q τ
  change (∫⁻ r : ℝ,
    if 0 < r then
      if ENNReal.ofReal r < τ then
        ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) ≤ ⨆ n : ℕ, ⨆ N : ℕ, G n N
  calc
    _ ≤ liminf (fun n : ℕ =>
          ∫⁻ r : ℝ, if 0 < r then f n r else 0 ∂μ) atTop := hFatou
    _ = liminf (fun n : ℕ => ⨆ N : ℕ, G n N) atTop := by
      congr 1
      funext n
      exact hgrid n
    _ ≤ ⨆ n : ℕ, ⨆ N : ℕ, G n N := by
      have hb : ∀ᶠ n : ℕ in atTop,
          (⨆ N : ℕ, G n N) ≤ ⨆ n : ℕ, ⨆ N : ℕ, G n N :=
        Eventually.of_forall (fun n => le_iSup (fun j => ⨆ N, G j N) n)
      exact (Filter.liminf_le_liminf hb).trans (by simp)
