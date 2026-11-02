-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_adapted_finite_rank_grid_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:07:42.666689+00:00
-- url     : https://prove2.me/submissions/9ba93088-bc5a-4166-84bf-44bbd9fb4b8b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_actual_source_finite_rank_grid_l2_of_extractors
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
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
    (grid : ℕ → ℝ≥0) (hGrid : Monotone grid) (C : ℕ → Set ℝ) (s : Finset ι)
    (W : ℕ → ι → Ω → ℝ) (f : ℕ → ι → ℝ → ℝ)
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → ℝ) (r : ℕ → ℝ≥0)
    (Fpath : ℕ → (ℝ≥0 → ℝ) → (ℕ × (ℕ → ℝ)))
    (hFpath : ∀ i, Measurable (Fpath i))
    (hRep : ∀ i ω, Fpath i (fun t : ℝ≥0 =>
      X.X (grid i + t) ω - X.X (grid i) ω) =
        (K i ω, fun n : ℕ => Y i n ω))
    (hKsource : ∀ i ω, (K i ω : ℝ≥0∞) =
      NX ω (Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hKm : ∀ i, Measurable (K i))
    (hKlaw : ∀ i, HasLaw (K i) (poissonMeasure (r i)) P)
    (hYm : ∀ i n, Measurable (Y i n))
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hYL : ∀ i n, HasLaw (Y i n) ρ P)
    (hYi : ∀ i, iIndepFun (Y i) P)
    (hCountMarks : ∀ i,
      IndepFun (K i) (fun ω (n : ℕ) => Y i n ω) P)
    (hWp : ∀ i a, a ∈ s → Measurable[𝓕 (grid i)] (W i a))
    (hWm : ∀ i a, a ∈ s → Measurable (W i a))
    (hW2 : ∀ i a, a ∈ s → Integrable (fun ω => W i a ω ^ 2) P)
    (hfm : ∀ i a, a ∈ s → Measurable (f i a))
    (hfI : ∀ i a, a ∈ s → Integrable (f i a) ρ)
    (hf2 : ∀ i a, a ∈ s → MemLp (f i a) 2 ρ)
    (hFsum : ∀ i a, a ∈ s → ∀ ω,
      (∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) =
          ∑ n ∈ Finset.range (K i ω), f i a (Y i n ω))
    (hZp : ∀ i a, a ∈ s → Measurable[𝓕 (grid (i + 1))] (fun ω =>
      (∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
        (r i : ℝ) * ∫ z, f i a z ∂ρ))
    (m : ℕ) :
    Integrable (fun ω => (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) - (r i : ℝ) * ∫ z, f i a z ∂ρ)) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range m, ∑ a ∈ s,
      W i a ω * ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
        f i a p.2 ∂(NX ω)) - (r i : ℝ) * ∫ z, f i a z ∂ρ)) ^ 2 ∂P) =
      ∑ i ∈ Finset.range m, ∑ a ∈ s, ∑ b ∈ s,
        (∫ ω, W i a ω * W i b ω ∂P) * (r i : ℝ) *
          (∫ z, f i a z * f i b z ∂ρ) := by
  have hCell (i : ℕ) : Measurable[𝓕 (grid (i + 1))] (fun ω =>
      ∑ a ∈ s, W i a ω *
        ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ρ)) := by
    apply Finset.measurable_sum
    intro a ha
    exact ((hWp i a ha).mono (𝓕.mono (hGrid (Nat.le_succ i))) le_rfl).mul
      (hZp i a ha)
  have hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s, W j a ω *
        ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ρ)) := by
    intro i
    apply Finset.measurable_sum
    intro j hj
    exact (hCell j).mono
      (𝓕.mono (hGrid (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))) le_rfl
  have hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s, W j a ω *
        ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ρ)) :=
    fun i => (hPrefixPast i).mono (𝓕.le (grid i)) le_rfl
  exact avram_wave5_02b_actual_source_finite_rank_grid_l2_of_extractors
    X NX hNX grid C s W f K Y r Fpath hFpath hRep hKsource
    hKm hKlaw hYm ρ hYL hYi hCountMarks hWp hWm hW2
    hfm hfI hf2 hFsum hPrefixMeas hPrefixPast m
