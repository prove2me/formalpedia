-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid16_original_joint_cofinal_band_and_coefficient_eventual_masks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:14:19.067667+00:00
-- url     : https://prove2.me/submissions/c66147b4-9020-462f-8dab-22fad9b3d23c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_probability_diagonal
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine source-exact joint spatial reserve and rowwise coefficient localisation. -/
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
    (coeff : ℕ → Ω → ℕ → ℝ)
    (hcoeff : ∀ n i, Measurable (fun ω => coeff n ω i))
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ κ K : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, n ≤ κ n) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n ω, ω ∈ s n →
        (∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))) ∧
        (∀ i ∈ Finset.range (n + 1),
          abs (coeff n ω i) ≤ (K n : ℝ))) := by
  classical
  obtain ⟨κ, sR, hκ, hRdef, hRm, heR⟩ :=
    avram_p3_grid16_original_adaptive_measurable_eventually_good_masks
      X x D hD C a b hExh u ε hε hεsum
  obtain ⟨K, hK, _⟩ :=
    avram_bv_residual10_original_rowwise_probability_diagonal
      (P := P) coeff hcoeff ε hε hεlim
  let sC : ℕ → Set Ω := fun n =>
    {ω : Ω | ∀ i ∈ Finset.range (n + 1),
      abs (coeff n ω i) ≤ (K n : ℝ)}
  have hCm (n : ℕ) : MeasurableSet (sC n) := by
    dsimp [sC]
    measurability
  have hbound (n : ℕ) : P ((sC n)ᶜ) ≤ ε n := by
    exact le_of_lt (hK n)
  have hsumC : (∑' n, P ((sC n)ᶜ)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) hεsum
  have hfinC : ∀ᵐ ω ∂P, ({n : ℕ | ω ∈ (sC n)ᶜ}).Finite :=
    MeasureTheory.ae_finite_setOf_mem
      (μ := P) (s := fun n => (sC n)ᶜ) (ne_of_lt hsumC)
  have heC : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ sC n := by
    filter_upwards [hfinC] with ω hω
    obtain ⟨N, hN⟩ := hω.bddAbove
    filter_upwards [Filter.eventually_ge_atTop (N + 1)] with n hn
    by_contra hbad
    have hnBad : n ∈ {n : ℕ | ω ∈ (sC n)ᶜ} := hbad
    have hnLe : n ≤ N := hN hnBad
    omega
  let s : ℕ → Set Ω := fun n => sR n ∩ sC n
  refine ⟨κ, K, s, hκ, ?_, ?_, ?_⟩
  · intro n
    exact (hRm n).inter (hCm n)
  · filter_upwards [heR, heC] with ω hR hC
    filter_upwards [hR, hC] with n hRn hCn
    exact ⟨hRn, hCn⟩
  · intro n ω hn
    change ω ∈ sR n ∧ ω ∈ sC n at hn
    rcases hn with ⟨hR, hC⟩
    constructor
    · simpa only [hRdef n, Set.mem_setOf_eq] using hR
    · simpa only [sC, Set.mem_setOf_eq] using hC
