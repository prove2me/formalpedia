-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_closed_horizon_discounted_atomic_cash_series_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:52:49.531167+00:00
-- url     : https://prove2.me/submissions/209edd2a-6e52-43f5-9d9b-c691903146c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The exact exhaustive original discounted right-atomic cash series is
bounded by cumulative dividends, while its actual atomless complement
(including singular-continuous payments) is retained in the equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) ≤
        ENNReal.ofReal (rightLimit D T ω)) := by
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  rcases avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
    X x D hD ω T
      (fun s : ℝ => ENNReal.ofReal (Real.exp (-(q * s)))) with
    ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, hFull⟩
  refine ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, hFull, ?_⟩
  have hCash :
      (∫⁻ s : ℝ, ENNReal.ofReal (Real.exp (-(q * s))) ∂
        (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))) ≤
        ENNReal.ofReal (rightLimit D T ω) :=
    avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hD ω T
  calc
    (∑' t : A, μ {(t : ℝ)} *
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) ≤
      (∑' t : A, μ {(t : ℝ)} *
        ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))) +
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse) :=
        le_add_of_nonneg_right bot_le
    _ = (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) := hFull.symm
    _ ≤ ENNReal.ofReal (rightLimit D T ω) := hCash
