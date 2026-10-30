-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_shifted_stieltjes_le_killed_record_grid_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:43:08.784004+00:00
-- url     : https://prove2.me/submissions/ad4df372-f5c3-4161-9a1f-2401827e294e

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_mesh_fatou_lower_integral
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_positive_time_rational_prefix_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_killed_mesh_prefix_integral_identity
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BigOperators Classical

/-- The true shifted future Stieltjes killed reward is at most the supremum
of its finite discounted future-record cash meshes, pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (q : ℝ) (τ : ℝ≥0∞) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) ≤
    ⨆ n : ℕ, ⨆ N : ℕ,
      (let grid : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
       ∑ k ∈ Finset.range N,
         (if ENNReal.ofReal (grid (k + 1)) < τ then
           ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) else 0) *
         ENNReal.ofReal (M (grid (k + 1)).toNNReal -
           M (grid k).toNNReal)) := by
  let M : ℝ≥0 → ℝ := fun v =>
    sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
  let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
  let f : ℕ → ℝ → ℝ≥0∞ := fun n r =>
    let e := ((⌈r * ((n : ℝ) + 1)⌉ : ℤ) : ℝ) / ((n : ℝ) + 1)
    if ENNReal.ofReal e < τ then
      ENNReal.ofReal (Real.exp (-(q * e))) else 0
  let G : ℕ → ℕ → ℝ≥0∞ := fun n N =>
    let grid : ℕ → ℝ := fun j => (j : ℝ) / ((n : ℝ) + 1)
    ∑ k ∈ Finset.range N,
      (if ENNReal.ofReal (grid (k + 1)) < τ then
        ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) else 0) *
      ENNReal.ofReal (M (grid (k + 1)).toNNReal -
        M (grid k).toNNReal)
  have hprefix (n N : ℕ) :
      (∫⁻ r in Ioc (0 : ℝ) ((N : ℝ) / ((n : ℝ) + 1)),
        f n r ∂μ) = G n N := by
    simpa [f, G, μ, M, Nat.cast_add] using
      (avram_root29_05_shifted_killed_mesh_prefix_integral_identity
        X ω age q τ n N)
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
