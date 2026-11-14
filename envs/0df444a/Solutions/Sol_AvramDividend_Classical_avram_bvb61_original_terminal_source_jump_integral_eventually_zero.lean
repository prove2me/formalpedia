-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb61_original_terminal_source_jump_integral_eventually_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:39:25.301192+00:00
-- url     : https://prove2.me/submissions/4299b15e-c539-4606-862a-a221a0f75dee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
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
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2))
    (g : ℝ≥0 → Ω → ℝ) :
    let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      (∫ t in Ioc (u n (n + 1)) S, g t ω
        ∂(Measure.count.restrict
          {t : ℝ≥0 | 0 < t ∧
            X.X t ω - Function.leftLim
              (fun s : ℝ≥0 => X.X s ω) t ≠ 0})) = 0  := by
  classical
  intro S
  have hC := avram_bvb51_original_uniform_last_horizon_source_negative_count_zero_ae
    X hBV hFinite T hT u huniform
  filter_upwards [hC] with ω hω
  filter_upwards [hω] with n hn
  have hμ :
      (Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).restrict
        (Ioc (u n (n + 1)) S) = 0 :=
    (Measure.restrict_eq_zero).2 hn
  change (∫ t : ℝ≥0, g t ω ∂
      ((Measure.count.restrict
        {t : ℝ≥0 | 0 < t ∧
          X.X t ω - Function.leftLim
            (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).restrict
        (Ioc (u n (n + 1)) S))) = 0
  rw [hμ]
  simp
