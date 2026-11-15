-- Prove2me | solution 1 for AvramDividend.Classical.avram_b101_original_all_random_krho_clock_finite_jump_support_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:19:21.072247+00:00
-- url     : https://prove2.me/submissions/6ecc9c3b-ebc7-498b-8ea8-5689f33ed2eb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The same conull original-source event controls all actual spatially clipped random stopping clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (κ : ℕ → Ω → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      {u : ℝ≥0 | 0 < u ∧ u ≤ κ k ω ∧
        X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}.Finite := by
  filter_upwards [
    avram_ubv_mixed12_original_finite_activity_jump_time_support_finite_ae
      X hFinite] with ω hω
  intro k
  exact hω (κ k ω)
