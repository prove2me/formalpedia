-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T18:00:54.513955+00:00
-- url     : https://prove2.me/submissions/2c056579-d706-4b4d-b8bd-affe74f57a0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_original_summable_annulus_finite_tail_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A summable original compensated annulus martingale basis is Cauchy in
physical L² mean square; this is before identifying a stopped integral limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
    let S : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range n, a i * Y i ω
    Summable (fun i => (a i) ^ 2 * r i) →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
        ∀ n m : ℕ, n₀ ≤ n → n₀ ≤ m →
          Integrable (fun ω => (S n ω - S m ω) ^ 2) P ∧
          (∫ ω, (S n ω - S m ω) ^ 2 ∂P) < ε := by
  classical
  let B : ℕ → Set ℝ := fun i =>
    Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
  let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B i)
  let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
  let Y : ℕ → Ω → ℝ := fun i ω => (N i ω).toReal - r i
  let S : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n, a i * Y i ω
  change Summable (fun i => (a i) ^ 2 * r i) →
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
      ∀ n m : ℕ, n₀ ≤ n → n₀ ≤ m →
        Integrable (fun ω => (S n ω - S m ω) ^ 2) P ∧
        (∫ ω, (S n ω - S m ω) ^ 2 ∂P) < ε
  intro hSumm ε hε
  have hTail := avram_mix_inf17_original_summable_annulus_finite_tail_L2
    X T cut hcut a hSumm ε hε
  change ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      Integrable (fun ω =>
        (∑ i ∈ Finset.range k, a (n + i) * Y (n + i) ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        a (n + i) * Y (n + i) ω) ^ 2 ∂P) < ε at hTail
  obtain ⟨n₀, hn₀⟩ := hTail
  have hDiff (n m : ℕ) (hnm : n ≤ m) :
      (fun ω => (S m ω - S n ω) ^ 2) =
        (fun ω =>
          (∑ i ∈ Finset.range (m - n),
            a (n + i) * Y (n + i) ω) ^ 2) := by
    funext ω
    have hadd : n + (m - n) = m := Nat.add_sub_of_le hnm
    have hsum := Finset.sum_range_add (fun i => a i * Y i ω) n (m - n)
    rw [hadd] at hsum
    dsimp [S]
    rw [hsum]
    ring
  refine ⟨n₀, ?_⟩
  intro n m hn hm
  rcases le_total n m with hnm | hmn
  · have hsym : (fun ω => (S n ω - S m ω) ^ 2) =
        (fun ω => (S m ω - S n ω) ^ 2) := by
      funext ω
      ring
    rw [hsym, hDiff n m hnm]
    exact hn₀ n hn (m - n)
  · rw [hDiff m n hmn]
    exact hn₀ m hm (n - m)
