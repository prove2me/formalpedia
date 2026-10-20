-- Prove2me | solution 1 for AvramDividend.Classical.chat03_martingale_sampled_filtration_reindex_corrected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:56:38.324197+00:00
-- url     : https://prove2.me/submissions/8a7de62e-8b48-42d5-b316-3ddd923b3429

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-!
Source-faithful repair of monotone-clock sampling. The discrete sampled
filtration H is supplied explicitly by equality of sigma-algebras, avoiding
inline record field syntax in the published target statement.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {G : Filtration ℝ≥0 mΩ}
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M G P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = G (clock k)) :
    Martingale (fun k ω => M (clock k) ω) H P := by
  constructor
  · intro k
    change StronglyMeasurable[H k] (M (clock k))
    rw [hH k]
    exact hM.stronglyMeasurable (clock k)
  · intro i j hij
    change P[M (clock j) | H i] =ᵐ[P] M (clock i)
    rw [hH i]
    exact hM.condExp_ae_eq (hc hij)