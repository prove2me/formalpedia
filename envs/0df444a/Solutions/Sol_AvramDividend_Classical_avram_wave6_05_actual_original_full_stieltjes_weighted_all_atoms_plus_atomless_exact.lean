-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:30:27.108951+00:00
-- url     : https://prove2.me/submissions/7c054b58-7789-4d1c-9449-db69416152ea

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- Exact complete original dividend Stieltjes weighted cash identity:
the total includes EVERY countable original right-dividend atom and the
unchanged atomless component, including singular-continuous variation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∫⁻ s, f s ∂μ) =
        (∑' t : A, μ {(t : ℝ)} * f (t : ℝ)) +
        (∫⁻ s, f s ∂μdiffuse) := by
  rcases avram_wave6_05_actual_original_stieltjes_every_nonzero_right_atom_in_countable_support
    X x D hD ω T f with
    ⟨A, μatom, μdiffuse, hCount, hMeas, hSplit, hAtom,
      hOutside, hNull, hAt, hFull, hTsum, hSupport⟩
  refine ⟨A, μdiffuse, hCount, hMeas, hNull, hAt, hSupport, ?_⟩
  rw [hFull, hTsum]
