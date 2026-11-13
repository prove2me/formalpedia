-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_chronological_pair_lintegral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:39:57.242874+00:00
-- url     : https://prove2.me/submissions/2cff2ed1-836f-4aba-a5d3-0ae945ddcaca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_grid_ae_count_bounds
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
import Theorems.Thm_AvramDividend_Classical_avram_a20_ae_eventually_exact_grid_fatou_squeeze
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let S : Ω → Set ℝ≥0 := fun ω => {u : ℝ≥0 |
      0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ∈ B}
    let K : Ω → ℕ := fun ω => ((S ω ×ˢ S ω) ∩
      {p : ℝ≥0 × ℝ≥0 | p.1 < p.2}).ncard
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂P) =
      (((T : ℝ≥0∞) * X.ν B) ^ 2) / 2 := by
  intro S K
  let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc a b ×ˢ B)
  let A : ℕ → Ω → ℝ≥0∞ := fun k ω =>
    ∑ i : Fin k,
      N 0 (((i.val : ℝ≥0) * T) / (k : ℝ≥0)) ω *
      N (((i.val : ℝ≥0) * T) / (k : ℝ≥0))
        ((((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)) ω
  have hν : X.ν B < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hAmeas : ∀ k, Measurable (A k) := by
    intro k
    let s : Fin k → ℝ≥0 := fun i =>
      ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i =>
      (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    simpa only [A, N, s, t] using
      (avram_a20_original_arbitrary_borel_physical_grid_pair_sum_measurable
        X k s t B hB)
  have hPath :
      (∀ᵐ ω ∂P, ∀ k, A k ω ≤ (K ω : ℝ≥0∞)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ k in atTop, A k ω = (K ω : ℝ≥0∞)) := by
    simpa only [S, K, A, N] using
      (avram_a20_original_borel_physical_grid_ae_count_bounds
        X hFinite T hT B hB hNeg)
  have hRate : Tendsto (fun k => ∫⁻ ω, A k ω ∂P) atTop
      (𝓝 ((((T : ℝ≥0∞) * X.ν B) ^ 2) / 2)) := by
    simpa only [A, N] using
      (avram_a20_original_borel_uniform_grid_physical_pair_rate_limit
        X T B hB hν)
  exact avram_a20_ae_eventually_exact_grid_fatou_squeeze
    P A (fun ω => (K ω : ℝ≥0∞))
    ((((T : ℝ≥0∞) * X.ν B) ^ 2) / 2)
    hAmeas hPath.1 hPath.2 hRate
