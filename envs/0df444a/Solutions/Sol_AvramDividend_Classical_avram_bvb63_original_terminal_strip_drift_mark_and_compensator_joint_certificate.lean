-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb63_original_terminal_strip_drift_mark_and_compensator_joint_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:58:36.700383+00:00
-- url     : https://prove2.me/submissions/8dc39950-d1c3-4aeb-8013-ec6d7d1d1c26

import Theorems.Thm_AvramDividend_Classical_avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hgrid : ∀ n, (u n (n + 1) : ℝ) =
      T - T / ((n : ℝ) + 2))
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ ε : ℝ, 0 < ε →
      ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0})
        (Ioc (u n (n + 1)) S) = 0 ∧
      (X.ν (Iio (0 : ℝ))).toReal *
        (T / ((n : ℝ) + 2)) < ε ∧
      X.X S ω - X.X (u n (n + 1)) ω =
        ((S : ℝ) - (u n (n + 1) : ℝ)) * X.drift := by
  intro S ε hε
  have hNoJump :=
    avram_bvb56_original_terminal_actual_count_zero_and_intensity_epsilon
      X hBV hFinite T hT u huniform ε hε
  have hDrift :=
    avram_bvb50_original_uniform_final_strip_BV_source_equals_physical_drift_ae
      X hBV hFinite T hT u hgrid huniform
  filter_upwards [hNoJump, hDrift] with ω hNJ hd
  filter_upwards [hNJ, hd] with n hn hdN
  exact ⟨hn.1, hn.2, hdN⟩
