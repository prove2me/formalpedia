-- Prove2me | solution 1 for AvramDividend.Classical.avram_a23_original_negative_band_signed_window_stationary_law_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:32:29.937629+00:00
-- url     : https://prove2.me/submissions/83ce364b-0f13-4278-bb20-79752089981d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a23_uniform_signed_negative_band_window_borel_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a23_original_future_path_borel_functional_stationary_law_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The actual original signed negative-mark window has a time-stationary law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (T s : ℝ≥0) :
    let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
    Measure.map (fun ω : Ω =>
      ∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX ω) P =
    Measure.map (fun ω : Ω =>
      ∫ p in (Ioc 0 T ×ˢ B), p.2 ∂NX ω) P := by
  classical
  let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  obtain ⟨J, hJ, hWindow⟩ :=
    avram_a23_uniform_signed_negative_band_window_borel_20261113
      X n T
  have hStation :=
    avram_a23_original_future_path_borel_functional_stationary_law_20261113
      X s J hJ
  have hLeft : (fun ω : Ω =>
      ∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX ω) =
    (fun ω : Ω => J (fun u : ℝ≥0 =>
      X.X (s + u) ω - X.X s ω)) := by
    funext ω
    exact hWindow s ω
  have hRight : (fun ω : Ω =>
      ∫ p in (Ioc 0 T ×ˢ B), p.2 ∂NX ω) =
    (fun ω : Ω => J (fun u : ℝ≥0 => X.X u ω)) := by
    funext ω
    have hZero := X.X_zero ω
    simpa [NX, B, hZero] using (hWindow 0 ω)
  change Measure.map (fun ω : Ω =>
    ∫ p in (Ioc s (s + T) ×ˢ B), p.2 ∂NX ω) P =
    Measure.map (fun ω : Ω =>
    ∫ p in (Ioc 0 T ×ˢ B), p.2 ∂NX ω) P
  rw [hLeft, hRight]
  exact hStation
