-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf17_original_summable_annulus_finite_tail_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T17:53:20.339143+00:00
-- url     : https://prove2.me/submissions/2c08c32d-31e8-4415-a67a-5794cfb2999d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf17_original_finite_step_annulus_L2_isometry

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Summable compensated annulus step energies have uniformly small physical
finite-tail second moments, for the original negative marked-jump process. -/
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
    Summable (fun i => (a i) ^ 2 * r i) →
      ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
        Integrable (fun ω =>
          (∑ i ∈ Finset.range k, a (n + i) * Y (n + i) ω) ^ 2) P ∧
        (∫ ω, (∑ i ∈ Finset.range k,
          a (n + i) * Y (n + i) ω) ^ 2 ∂P) < ε := by
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
  let f : ℕ → ℝ := fun i => (a i) ^ 2 * r i
  let S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, f i
  change Summable f → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
    ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ,
      Integrable (fun ω =>
        (∑ i ∈ Finset.range k, a (n + i) * Y (n + i) ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ Finset.range k,
        a (n + i) * Y (n + i) ω) ^ 2 ∂P) < ε
  intro hSumm ε hε
  let s : ℝ := ∑' i, f i
  have hlim : Tendsto S atTop (nhds s) := by
    exact hSumm.hasSum.tendsto_sum_nat
  have hopen : Ioo (s - ε / 2) (s + ε / 2) ∈ nhds s := by
    apply Ioo_mem_nhds <;> linarith
  have hevent : ∀ᶠ n : ℕ in atTop,
      s - ε / 2 < S n ∧ S n < s + ε / 2 := by
    filter_upwards [hlim.eventually hopen] with n hn
    exact hn
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨n₀, ?_⟩
  intro n hn k
  have hsmall : (∑ i ∈ Finset.range k, f (n + i)) < ε := by
    have hleft := (hn₀ n hn).1
    have hright := (hn₀ (n + k) (le_trans hn (Nat.le_add_right n k))).2
    have hadd : S (n + k) = S n + ∑ i ∈ Finset.range k, f (n + i) := by
      exact Finset.sum_range_add f n k
    linarith
  have hmono : Monotone (fun i => cut (n + i)) := by
    intro i j hij
    exact hcut (Nat.add_le_add_left hij n)
  have hIso := avram_mix_inf17_original_finite_step_annulus_L2_isometry
    X T (fun i => cut (n + i)) hmono (fun i => a (n + i)) k
  change Integrable (fun ω =>
      (∑ i ∈ Finset.range k, a (n + i) * Y (n + i) ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ Finset.range k,
      a (n + i) * Y (n + i) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range k, f (n + i) at hIso
  refine ⟨hIso.1, ?_⟩
  rw [hIso.2]
  exact hsmall
