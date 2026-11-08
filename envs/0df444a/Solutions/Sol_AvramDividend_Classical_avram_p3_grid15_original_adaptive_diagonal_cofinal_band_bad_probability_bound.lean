-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:26:51.341431+00:00
-- url     : https://prove2.me/submissions/01af6f29-cbf6-42e0-9ac2-a8bd613be9df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Select an adaptive cofinal band for each genuine physical grid row so that
the true prepayment reserve's exceptional probability meets any positive target. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n) :
    ∃ κ : ℕ → ℕ,
      (∀ n, n ≤ κ n) ∧
      ∀ n,
        P ({ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ) < ε n := by
  classical
  have hsmall (n : ℕ) :
      ∃ N : ℕ, ∀ k ≥ N,
        P ({ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a k) (b k)}ᶜ) < ε n := by
    have hlim :=
      avram_p3_grid14_original_prejump_reserve_cofinal_band_bad_measure_zero
        X x D hD C a b hExh n u
    have hεnhds : Iio (ε n) ∈ 𝓝 (0 : ℝ≥0∞) :=
      Iio_mem_nhds (hε n)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually hεnhds)
    exact ⟨N, fun k hk => hN k hk⟩
  choose K hK using hsmall
  refine ⟨fun n => max n (K n), (fun n => le_max_left _ _), ?_⟩
  intro n
  exact hK n (max n (K n)) (le_max_right _ _)
