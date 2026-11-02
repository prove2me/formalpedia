-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_count_grid_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:53:34.117291+00:00
-- url     : https://prove2.me/submissions/ee70ad56-068e-4fa9-aa93-7d8a15ada446

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid) (C : ℕ → Set ℝ)
    (H : ℕ → Ω → ℝ) (K : ℕ → Ω → ℕ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) = K i ω)
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hZ : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (K i ω : ℝ) - (r i : ℝ)))
    (hHm : ∀ i, Measurable (H i))
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hKInt : ∀ i, Integrable (fun ω => (K i ω : ℝ) - (r i : ℝ)) P)
    (n : ℕ) :
    Integrable (fun ω =>
      (∑ i ∈ Finset.range n, H i ω *
        ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
          (r i : ℝ))) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, H i ω *
      ((NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i)).toReal -
        (r i : ℝ))) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, (r i : ℝ) * ∫ ω, (H i ω) ^ 2 ∂P := by
  have hMono : Monotone (fun i : ℕ => 𝓕 (grid i)) :=
    fun _ _ hij => 𝓕.mono (hGrid hij)
  have hFuturePast : ∀ i n, i < n → 𝓕 (grid (i + 1)) ≤ 𝓕 (grid n) :=
    fun _ _ hin => 𝓕.mono (hGrid (Nat.succ_le_of_lt hin))
  have hPrefix : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, H j ω * ((K j ω : ℝ) - (r j : ℝ))) := by
    intro i
    exact (avram_wave4_p1_original_grid_compensated_prefix_strongly_past_measurable
      (fun j => 𝓕 (grid j)) (fun j => 𝓕 (grid (j + 1))) hMono hFuturePast
      H (fun j ω => (K j ω : ℝ) - (r j : ℝ)) hH hZ i).measurable
  exact avram_wave5_02b_actual_source_cell_counts_grid_l2_of_extractors
    X NX hNX grid C H K r Fpath hFpath hRep hKsource
    (fun i => (hH i).measurable) hHm hHSq hKm hKlaw hKInt hPrefix n
