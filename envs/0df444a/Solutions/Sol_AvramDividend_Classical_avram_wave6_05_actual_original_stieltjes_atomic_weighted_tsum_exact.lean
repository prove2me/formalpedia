-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_stieltjes_atomic_weighted_tsum_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:04:46.214742+00:00
-- url     : https://prove2.me/submissions/7a430819-8057-4bf2-add3-29497e030edf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- Every actual original dividend Stieltjes atomic lower integral is exactly
the weighted countable right-atom sum, including time-zero and endpoint atoms.
The full integral also contains the unmodified atomless component. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, f s ∂μ) =
        (∫⁻ s, f s ∂μatom) + (∫⁻ s, f s ∂μdiffuse)) ∧
      ((∫⁻ s, f s ∂μatom) =
        ∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) := by
  rcases avram_wave5_04b_actual_dividend_atomic_atomless_full_stieltjes_lintegral_split
    X x D hD ω T f with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, hFull⟩
  refine ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
    hOutside, hNull, hAt, hFull, ?_⟩
  rw [hAtom, MeasureTheory.lintegral_sum_measure]
  simp only [MeasureTheory.lintegral_smul_measure,
    MeasureTheory.lintegral_dirac, smul_eq_mul]
