-- Prove2me | solution 1 for AvramDividend.Classical.admissible_of_no_right_dividend_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:29:44.283593+00:00
-- url     : https://prove2.me/submissions/682e13ac-e1fc-4098-bce6-da77d2047837

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hr : ∀ ω (t : ℝ≥0), rightLimit D t ω = D t ω) :
    IsAdmissible X x D := by
  refine ⟨hD, ?_⟩
  intro ω t ht
  rw [hr ω t]
  have hreserve : 0 ≤ riskProcess X x D t ω := by
    rcases ht with hzero | hbefore
    · subst t
      simp only [riskProcess, X.X_zero ω, hD.1 ω]
      linarith
    · by_contra hnegative
      have hneg : riskProcess X x D t ω < 0 := lt_of_not_ge hnegative
      have hruin : ruinTime X x D ω ≤ (t : ℝ≥0∞) := by
        unfold ruinTime
        exact iInf_le_of_le t
          (iInf_le (fun (_ : riskProcess X x D t ω < 0) => (t : ℝ≥0∞)) hneg)
      exact (not_le_of_gt hbefore) hruin
  simpa using hreserve
