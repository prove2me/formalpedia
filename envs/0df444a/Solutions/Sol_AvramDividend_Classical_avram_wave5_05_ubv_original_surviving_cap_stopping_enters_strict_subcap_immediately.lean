-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_ubv_original_surviving_cap_stopping_enters_strict_subcap_immediately
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:11:34.59757+00:00
-- url     : https://prove2.me/submissions/8bf66489-8a0a-49ca-9b33-da1bee99701a

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-!
At every surviving cap-contact stopping time, the same original controlled
reserve moves strictly below cap within the survival interval.
-/

/-- Strict post-contact subcap times exist before ruin, including contact at t=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) :
    ∀ᵐ ω ∂P,
      (τ ω : ℝ≥0∞) < ruinTime X x D ω →
      riskProcess X x D (τ ω) ω = c →
      ∀ ε : ℝ≥0, 0 < ε →
        ∃ s : ℝ≥0, 0 < s ∧ s < ε ∧
          ((τ ω + s : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω ∧
          riskProcess X x D (τ ω + s) ω < c := by
  have hDown :=
    avram_wave4_04_ubv_original_levy_finite_stopping_downward_regular_no_grid
      X hBV τ hτ hstop
  filter_upwards [hDown] with ω hω
  intro hSurvive hContact ε hε
  obtain ⟨r, hrT, hrRuin⟩ :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hSurvive
  have hτr : τ ω < r := ENNReal.coe_lt_coe.mp hrT
  have hδ : 0 < r - τ ω := tsub_pos_iff_lt.mpr hτr
  have hMin : 0 < min ε (r - τ ω) := lt_min hε hδ
  obtain ⟨s, hsShort, hXNeg⟩ := hω (min ε (r - τ ω)) hMin
  have hsPos : 0 < s := by
    by_contra hNot
    have hs0 : s = 0 :=
      le_antisymm (le_of_not_gt hNot) (zero_le : (0 : ℝ≥0) ≤ s)
    subst s
    simp at hXNeg
  have hsε : s < ε :=
    lt_of_lt_of_le hsShort (min_le_left ε (r - τ ω))
  have hsδ : s < r - τ ω :=
    lt_of_lt_of_le hsShort (min_le_right ε (r - τ ω))
  have hτs : τ ω + s < r := by
    have hR : r - τ ω + τ ω = r :=
      tsub_add_cancel_of_le (le_of_lt hτr)
    linarith
  have hSurviveS : ((τ ω + s : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω :=
    lt_trans (ENNReal.coe_lt_coe.mpr hτs) hrRuin
  have hDmono : Monotone (fun t : ℝ≥0 => D t ω) := hD.2.1 ω
  have hDle : D (τ ω) ω ≤ D (τ ω + s) ω :=
    hDmono (le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ s))
  have hBelow : riskProcess X x D (τ ω + s) ω < c := by
    dsimp [riskProcess] at hContact ⊢
    linarith
  exact ⟨s, hsPos, hsε, hSurviveS, hBelow⟩
