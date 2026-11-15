-- Prove2me | solution 1 for AvramDividend.Classical.avram_b122_original_negative_cutoff_poisson_counts_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:22:23.569505+00:00
-- url     : https://prove2.me/submissions/2a42afb7-0b5f-401c-b7a3-b636f26bc293

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original negative-mark source Poisson counts increase along cofinal reciprocal cutoffs on physical intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ≤
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((m : ℝ) + 1)))) := by
  have h : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hcut :
      -(1 / ((n : ℝ) + 1)) ≤ -(1 / ((m : ℝ) + 1)) := by
    gcongr
  apply measure_mono
  intro z hz
  exact ⟨hz.1, le_trans hz.2 hcut⟩
