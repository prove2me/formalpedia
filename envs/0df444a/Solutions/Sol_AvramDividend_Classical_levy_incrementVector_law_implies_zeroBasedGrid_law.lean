-- Prove2me | solution 1 for AvramDividend.Classical.levy_incrementVector_law_implies_zeroBasedGrid_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:16:31.850497+00:00
-- url     : https://prove2.me/submissions/32a4d27a-b579-45fd-a030-8928b8a5197b

import Mathlib.Probability.IdentDistrib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_incrementVector_law_implies_gridPositions_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- From stationary increment vectors to finite-dimensional Lévy paths on a zero-based grid. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (n : ℕ)
    (hLaw :
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (s + t (i.val + 1)) ω - X.X (s + t i.val) ω) P =
      Measure.map (fun ω : Ω => fun i : Fin n =>
        X.X (t (i.val + 1)) ω - X.X (t i.val) ω) P) :
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (s + t (i.val + 1)) ω - X.X s ω) P =
    Measure.map (fun ω : Ω => fun i : Fin n =>
      X.X (t (i.val + 1)) ω) P := by
  have h := levy_incrementVector_law_implies_gridPositions_law X s t n hLaw
  simpa [ht0, X.X_zero] using h
