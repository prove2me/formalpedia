-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_stieltjes10_original_countable_positive_grid_prejump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:32:48.491056+00:00
-- url     : https://prove2.me/submissions/145218d8-5e2e-48a1-a624-6ac6e329b2ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One common full-measure event supplies the original prepayment reserve
at every strictly positive deterministic grid time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℝ≥0) (hu : ∀ n, 0 < u n) :
    ∀ᵐ ω ∂P, ∀ n,
      Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
          (u n) =
        riskProcess X x D (u n) ω := by
  rw [ae_all_iff]
  intro n
  filter_upwards
    [avram_p3_bv_original_controlled_fixed_horizon_leftLim_eq_ae
      X D hD x (u n) (hu n)] with ω hleft
  rw [← avram_wave4_p2_original_prepost_reserve_same_leftlim
    X x D hD ω (u n) (hu n)]
  exact hleft
