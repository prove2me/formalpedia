-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02b_actual_source_finite_rank_grid_l2_of_extractors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:53:28.524385+00:00
-- url     : https://prove2.me/submissions/f274fb31-b4fd-4c8a-8731-95e5f5262f99

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry

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
    (grid : ℕ → ℝ≥0) (C : ℕ → Set ℝ) (s : Finset ι)
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
    (hPrefixMeas : ∀ i, Measurable (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s,
        W j a ω * ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ρ)))
    (hPrefixPast : ∀ i, Measurable[𝓕 (grid i)] (fun ω =>
      ∑ j ∈ Finset.range i, ∑ a ∈ s,
        W j a ω * ((∑ n ∈ Finset.range (K j ω), f j a (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j a z ∂ρ)))
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
  have hPast {E : Type} [MeasurableSpace E] (i : ℕ)
      (U : Ω → E) (hU : Measurable[𝓕 (grid i)] U) :
      IndepFun U (fun ω => (K i ω, fun n : ℕ => Y i n ω)) P := by
    have hi := actual_levy_past_indep_measurable_future_jump_family_ws01b
      X (grid i) U hU (Fpath i) (hFpath i)
    have hrep : (fun ω => Fpath i (fun t : ℝ≥0 =>
        X.X (grid i + t) ω - X.X (grid i) ω)) =
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) := funext (hRep i)
    simpa only [hrep] using hi
  have hWpast : ∀ i a, a ∈ s →
      IndepFun (W i a) (fun ω => (K i ω, fun n : ℕ => Y i n ω)) P :=
    fun i a ha => hPast i _ (hWp i a ha)
  have hSum : ∀ i a, a ∈ s → ∀ b, b ∈ s →
      IndepFun (fun ω => W i a ω + W i b ω)
        (fun ω => (K i ω, fun n : ℕ => Y i n ω)) P :=
    fun i a ha b hb => hPast i _ ((hWp i a ha).add (hWp i b hb))
  have hJoint : ∀ i a, a ∈ s → IndepFun (fun ω =>
      ((∑ j ∈ Finset.range i, ∑ b ∈ s,
        W j b ω * ((∑ n ∈ Finset.range (K j ω), f j b (Y j n ω)) -
          (r j : ℝ) * ∫ z, f j b z ∂ρ)), W i a ω))
      (fun ω => (K i ω, fun n : ℕ => Y i n ω)) P :=
    fun i a ha => hPast i _ ((hPrefixPast i).prodMk (hWp i a ha))
  have hi := avram_wave4_p1_finite_rank_predictable_marked_grid_l2_isometry
    P ρ s W f K Y r hKm hKlaw hYm hYL hYi hCountMarks hWm hW2
    hWpast hSum hfm hfI hf2 hPrefixMeas hJoint m
  have hSumEq (ω : Ω) :
      (∑ i ∈ Finset.range m, ∑ a ∈ s,
        W i a ω * ((∫ p in Set.Ioc (grid i) (grid (i + 1)) ×ˢ C i,
          f i a p.2 ∂(NX ω)) - (r i : ℝ) * ∫ z, f i a z ∂ρ)) =
      (∑ i ∈ Finset.range m, ∑ a ∈ s,
        W i a ω * ((∑ n ∈ Finset.range (K i ω), f i a (Y i n ω)) -
          (r i : ℝ) * ∫ z, f i a z ∂ρ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro a ha
    rw [hFsum i a ha ω]
  simpa only [hSumEq] using hi
