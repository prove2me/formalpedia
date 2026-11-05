-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_real_truncated_ruin_nnreal_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:47:04.646796+00:00
-- url     : https://prove2.me/submissions/be847280-9394-4e46-9faa-18450b90c5e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite nonnegative real horizon has an actual bounded ruin-stopped
NNReal clock for the original controlled Lévy process, even off integer times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    (∀ ω, τ ω ≤ T) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
  have hBound (ω : Ω) : τ ω ≤ T := by
    dsimp [τ]
    have hMono := ENNReal.toNNReal_mono
      (by simp : (T : ℝ≥0∞) ≠ ⊤)
      (min_le_right (ruinTime X x D ω) (T : ℝ≥0∞))
    simpa using hMono
  have hFunEq :
      (fun ω : Ω => (τ ω : WithTop ℝ≥0)) =
      (fun ω : Ω => min (ruinTime X x D ω) (T : ℝ≥0∞)) := by
    funext ω
    dsimp [τ]
    apply ENNReal.coe_toNNReal
    have hTtop : (T : ℝ≥0∞) < ⊤ := by simp
    exact ne_top_of_lt (lt_of_le_of_lt
      (min_le_right (ruinTime X x D ω) (T : ℝ≥0∞)) hTtop)
  constructor
  · exact hBound
  · rw [hFunEq]
    intro t
    change MeasurableSet[𝓕.rightCont t]
      {ω | min (ruinTime X x D ω) (T : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
    by_cases hTle : (T : ℝ≥0∞) ≤ (t : ℝ≥0∞)
    · have hall :
          {ω | min (ruinTime X x D ω) (T : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
            (Set.univ : Set Ω) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact le_trans (min_le_right _ _) hTle
      rw [hall]
      exact MeasurableSet.univ
    · have hsource :
          {ω | min (ruinTime X x D ω) (T : ℝ≥0∞) ≤ (t : ℝ≥0∞)} =
            {ω | ruinTime X x D ω ≤ (t : ℝ≥0∞)} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · intro h
          rcases min_le_iff.mp h with hσ | hT'
          · exact hσ
          · exact (hTle hT').elim
        · intro hσ
          exact le_trans (min_le_left _ _) hσ
      rw [hsource]
      exact (ruinTime_stopping_rightCont_filtration X x D hD) t
