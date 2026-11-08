-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps10_original_negative_band_count_pgf_of_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:51:53.303716+00:00
-- url     : https://prove2.me/submissions/acfe9429-6d24-41d2-b595-d4ddfbdcad63

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transport an actual negative-band original Lévy count's Poisson law to its
exponential moment. The source count law remains an explicit obligation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ)
    (NB : Ω → ℕ)
    (hcount : ∀ ω, (NB ω : ℝ≥0∞) =
      ((Measure.count.restrict
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 =>
          (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Set.Ioc (0 : ℝ≥0) T ×ˢ B))
    (hNm : Measurable NB)
    (r : ℝ≥0)
    (hLaw : P.map NB = poissonMeasure r)
    (a : ℝ) :
    (∫ ω, a ^ NB ω ∂P) = Real.exp ((r : ℝ) * (a - 1)) := by
  have hf : Measurable (fun n : ℕ => a ^ n) := measurable_of_countable _
  have hmap : (∫ n, a ^ n ∂(P.map NB)) = (∫ ω, a ^ NB ω ∂P) := by
    exact integral_map hNm.aemeasurable hf.aestronglyMeasurable
  rw [← hmap, hLaw]
  exact AvramDividend.Classical.chat06_poisson_count_pgf_general r a
