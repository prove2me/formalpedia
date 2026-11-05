-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:34:01.586117+00:00
-- url     : https://prove2.me/submissions/86c373da-db92-4cf3-8c9e-ef07433aca49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original integer-truncated ruin clock is a bounded NNReal stopping
time, in the exact right-continuous filtration required by P3-B. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    (∀ ω, τ ω ≤ (n : ℝ≥0)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) := by
  let τ : Ω → ℝ≥0 := fun ω =>
    (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  have hBound (ω : Ω) : τ ω ≤ (n : ℝ≥0) := by
    dsimp [τ]
    have hMono := ENNReal.toNNReal_mono
      (by simp : (n : ℝ≥0∞) ≠ ⊤)
      (min_le_right (ruinTime X x D ω) (n : ℝ≥0∞))
    simpa using hMono
  have hFunEq :
      (fun ω : Ω => (τ ω : WithTop ℝ≥0)) =
      (fun ω : Ω => min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
    funext ω
    dsimp [τ]
    apply ENNReal.coe_toNNReal
    have hn : (n : ℝ≥0∞) < ⊤ := by simp
    exact ne_top_of_lt (lt_of_le_of_lt
      (min_le_right (ruinTime X x D ω) (n : ℝ≥0∞)) hn)
  constructor
  · exact hBound
  · rw [hFunEq]
    exact avram_wave5_05_actual_bounded_ruin_clocks_rightCont_stopping
      X x D hD n
