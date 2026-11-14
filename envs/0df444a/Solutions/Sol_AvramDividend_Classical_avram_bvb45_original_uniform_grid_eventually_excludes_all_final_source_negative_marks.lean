-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb45_original_uniform_grid_eventually_excludes_all_final_source_negative_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:42:14.13309+00:00
-- url     : https://prove2.me/submissions/30eecf05-33b6-46dd-9476-4af70c1d9b67

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
import Theorems.Thm_AvramDividend_Classical_avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original mission uniform-grid final strip contains no actual physical
negative Levy mark for all sufficiently fine rows, almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in (atTop : Filter ℕ),
      ∀ t : ℝ≥0, 0 < t →
        (u n (n + 1) : ℝ) < (t : ℝ) →
        (t : ℝ) ≤ T →
        X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0 →
        False := by
  let S : ℝ≥0 := ⟨T,le_of_lt hT⟩
  have hS : 0 < S := by
    exact_mod_cast hT
  have hOriginal :=
    avram_bvb44_original_finiteactivity_ae_last_horizon_no_negative_mark_strip
      X hBV hFinite S hS
  have hEnd :=
    avram_bva78_original_supplied_uniform_endpoint_tendsto_real_horizon
      T hT u huniform
  filter_upwards [hOriginal] with ω hω
  obtain ⟨ε,hε,hGap⟩ := hω
  have hClose : ∀ᶠ n in (atTop : Filter ℕ),
      T - ε < (u n (n + 1) : ℝ) :=
    hEnd.eventually (Ioi_mem_nhds (sub_lt_self T hε))
  filter_upwards [hClose] with n hn
  intro t ht hpost htT hJump
  have htS : t ≤ S := by
    exact_mod_cast htT
  have hBefore := hGap t ht htS hJump
  change (t : ℝ) ≤ T - ε at hBefore
  linarith
