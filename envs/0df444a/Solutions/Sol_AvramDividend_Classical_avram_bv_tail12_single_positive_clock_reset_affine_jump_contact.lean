-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_affine_jump_contact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:34:55.30042+00:00
-- url     : https://prove2.me/submissions/23fdb4ea-3a1e-4429-85d4-2c489121570a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source affine jump-contact inequality holds at a single affordable
positive-time reset, including the zero clock and every pre-ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (s : ℝ≥0) (hs : 0 < s) (K : Ω → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω)
    (hK : ∀ ω, 0 ≤ K ω)
    (hreset : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω = x + X.X s ω) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        (fun y : ℝ => if y < 0 then 0 else 1 + y) (riskProcess X x D t ω) -
          (fun y : ℝ => if y < 0 then 0 else 1 + y)
            (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) := by
  intro ω t ht
  by_cases hts : t = s
  · subst t
    have hpre : (s : ℝ≥0∞) < ruinTime X x D ω := by
      rcases ht with hz | hr
      · exact False.elim ((ne_of_gt hs) hz)
      · exact hr
    have hr : rightLimit D s ω = K ω := by
      rw [hright]
      simp
    have hp : D s ω = 0 := by
      rw [hD]
      simp
    have hdiff : rightLimit D s ω - D s ω = K ω := by
      rw [hr, hp]
      ring
    have hrisk : riskProcess X x D s ω = K ω := by
      simp only [riskProcess, hp]
      linarith [hreset ω hpre]
    rw [hdiff, hrisk]
    simp [not_lt.mpr (hK ω)]
  · have hdiff : rightLimit D t ω - D t ω = 0 := by
      rw [hright ω t, hD t ω]
      by_cases hlt : t < s
      · simp [hlt, le_of_lt hlt]
      · have hgt : s < t :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hts)
        simp [hlt, not_le.mpr hgt]
    rw [hdiff]
    simp
