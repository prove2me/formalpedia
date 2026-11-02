-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_ubv_original_prejump_candidate_nonnegative_atomless_allcap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:21:33.006567+00:00
-- url     : https://prove2.me/submissions/c84a422a-33e0-44c7-bc70-ffafe2e9aa69

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [NullSingletonClass μ] :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂μ, 0 < t →
      0 ≤ w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) := by
  have hbook :=
    avram_wave5_ubv_original_all_cap_stopped_terminal_candidate_nonnegative
      X w C hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD
  have heq :=
    avram_wave5_05_original_prejump_equals_book_reserve_atomless_nnreal_clock
      X x D hD.1.1 μ
  filter_upwards [heq] with ω hω
  filter_upwards [hω] with t ht
  intro htpos
  rw [ht htpos]
  exact hbook ω t
