-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_tail12_single_positive_clock_reset_admissible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:24:30.218743+00:00
-- url     : https://prove2.me/submissions/4c801fc3-a8cd-4af9-b6ed-7625971e14cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An affordable positive-clock right dividend step meets the original
admissibility contract when its strategy and right-limit facts hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (s : ℝ≥0) (hs : 0 < s) (K : Ω → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : ∀ t ω, D t ω = if t ≤ s then 0 else K ω)
    (hstrategy : IsDividendStrategy 𝓕 D)
    (hright : ∀ ω t, rightLimit D t ω = if t < s then 0 else K ω)
    (hafford : ∀ ω, (s : ℝ≥0∞) < ruinTime X x D ω →
      K ω ≤ x + X.X s ω) :
    IsAdmissibleLe X x ⊤ D := by
  change IsAdmissible X x D ∧
    ∀ ω (t : ℝ≥0), 0 < t → ENNReal.ofReal (riskProcess X x D t ω) ≤ ⊤
  refine ⟨⟨hstrategy, ?_⟩, ?_⟩
  · intro ω t ht
    by_cases hts : t = s
    · subst t
      have hpre : (s : ℝ≥0∞) < ruinTime X x D ω := by
        rcases ht with hz | hpr
        · exact False.elim ((ne_of_gt hs) hz)
        · exact hpr
      have hr : rightLimit D s ω = K ω := by
        rw [hright]
        simp
      have hp : D s ω = 0 := by rw [hD]; simp
      calc
        rightLimit D s ω - D s ω = K ω := by rw [hr, hp]; ring
        _ ≤ x + X.X s ω := hafford ω hpre
        _ = riskProcess X x D s ω := by simp [riskProcess, hp]
    · have hdiff : rightLimit D t ω - D t ω = 0 := by
        rw [hright ω t, hD t ω]
        by_cases hlt : t < s
        · simp [hlt, le_of_lt hlt]
        · have hgt : s < t :=
            lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hts)
          simp [hlt, not_le.mpr hgt]
      rcases ht with hz | hpr
      · subst t
        have hD0 : D 0 ω = 0 := by
          rw [hD]
          simp [hs.le]
        have hrisk : 0 ≤ riskProcess X x D 0 ω := by
          simpa [riskProcess, hD0, X.X_zero ω] using hx
        simpa only [hdiff] using hrisk
      · have hrisk : 0 ≤ riskProcess X x D t ω :=
          riskProcess_nonneg_before_ruin X x D ω t hpr
        simpa only [hdiff] using hrisk
  · intro ω t ht
    exact le_top
