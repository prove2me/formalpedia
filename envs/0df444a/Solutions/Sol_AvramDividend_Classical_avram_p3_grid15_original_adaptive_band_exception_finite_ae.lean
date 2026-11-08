-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid15_original_adaptive_band_exception_finite_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:34:40.292592+00:00
-- url     : https://prove2.me/submissions/9a2d734f-51ac-408b-9f82-6484e1d6744a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Summable diagonal band escape probability makes the set of bad physical
rows almost surely finite for the original controlled Lévy reserve. -/
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
    (ε : ℕ → ℝ≥0∞) (hε : ∀ n, 0 < ε n)
    (hεsum : (∑' n, ε n) < ⊤) :
    ∃ κ : ℕ → ℕ,
      (∀ n, n ≤ κ n) ∧
      ∀ᵐ ω ∂P, ({n : ℕ | ω ∈ {ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ}).Finite := by
  classical
  obtain ⟨κ, hκ, hsmall⟩ :=
    avram_p3_grid15_original_adaptive_diagonal_cofinal_band_bad_probability_bound
      X x D hD C a b hExh u ε hε
  let bad : ℕ → Set Ω := fun n => {ω : Ω | ∀ i < n + 1,
          (0 < Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∧
            ENNReal.ofReal (Function.leftLim
              (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)) < C) →
          Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i) ∈
            Icc (a (κ n)) (b (κ n))}ᶜ
  have hle (n : ℕ) : P (bad n) ≤ ε n := by
    exact le_of_lt (hsmall n)
  have hsum : (∑' n, P (bad n)) < ⊤ :=
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hεsum
  have hfinite : ∀ᵐ ω ∂P, ({n : ℕ | ω ∈ bad n}).Finite :=
    MeasureTheory.ae_finite_setOf_mem (μ := P) (s := bad) (ne_of_lt hsum)
  refine ⟨κ, hκ, ?_⟩
  simpa only [bad] using hfinite
