-- Prove2me | solution 1 for AvramDividend.Classical.survived_nextRecord_shifted_lower_exit_not_earlier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T20:21:31.316867+00:00
-- url     : https://prove2.me/submissions/d5cd3a6b-6285-4d1a-b66b-9627066a2599

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_survived_nextRecord_shifted_path_lower_guard

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hε : 0 ≤ ε)
    (u v δ : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b < X.X r ω), (r : ℝ≥0∞)))
    (hv : (v : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + ε < X.X r ω), (r : ℝ≥0∞)))
    (hδ : u + δ = v)
    (hSurvive : (v : ℝ≥0∞) < barrierRuinTime X a ω) :
    (δ : ℝ≥0∞) ≤
      (⨅ (s : ℝ≥0)
        (_ : X.X (u + s) ω - X.X u ω < -a), (s : ℝ≥0∞)) := by
  have hg := survived_nextRecord_shifted_path_lower_guard X ω a b ε ha hb hε u v hu hv hSurvive
  refine le_iInf₂ fun s hs => ?_
  rw [ENNReal.coe_le_coe]
  by_contra hlt
  push_neg at hlt
  have : u + s < v := by rw [← hδ]; exact add_lt_add_right hlt u
  exact absurd (hg s this) (not_le.mpr hs)
