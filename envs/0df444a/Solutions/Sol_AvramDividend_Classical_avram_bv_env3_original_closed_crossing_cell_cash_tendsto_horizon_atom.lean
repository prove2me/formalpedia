-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T20:16:46.795196+00:00
-- url     : https://prove2.me/submissions/56da18a5-9732-4daa-a457-ddae2bc8e717

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A shrinking right-closed physical-grid cell retains exactly its T atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  have hstrict :=
    avram_bv_env3_original_strict_crossing_cell_discounted_cash_tendsto_zero
      D hD ω σ T q hq a ha hlim
  have hconst : Tendsto
      (fun _ : ℕ => ∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds
        (∫⁻ t in paymentTimes σ ∩ {(T : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) :=
    tendsto_const_nhds
  have hplus := hstrict.add hconst
  have hsplit (n : ℕ) :=
    avram_bv_env3_original_last_cell_closed_cash_splits_horizon_atom
      D hD ω σ T q (a n) (hbelow n)
  simpa only [zero_add] using
    hplus.congr' (Filter.Eventually.of_forall fun n => (hsplit n).symm)
