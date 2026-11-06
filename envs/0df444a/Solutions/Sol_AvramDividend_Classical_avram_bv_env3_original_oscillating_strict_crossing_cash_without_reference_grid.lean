-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_oscillating_strict_crossing_cash_without_reference_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:50:47.117644+00:00
-- url     : https://prove2.me/submissions/e6042374-c7d0-4cdd-968f-30f74861906c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every convergent physical-grid endpoint admits the deterministic
    reciprocal reference mesh T - 1/(n+1), so no mesh monotonicity remains. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Tendsto a atTop (nhds (T : ℝ))) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioo (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by
  let b : ℕ → ℝ := fun n => (T : ℝ) - ((n : ℝ) + 1)⁻¹
  have hb_mono : Monotone b := by
    intro i j hij
    have hi : 0 < (i : ℝ) + 1 := by positivity
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hij' : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by linarith
    have hinv := one_div_le_one_div_of_le hi hij'
    simpa only [one_div, b] using (sub_le_sub_left hinv (T : ℝ))
  have hb_below (n : ℕ) : b n < (T : ℝ) := by
    dsimp [b]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hposinv : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hpos
    linarith
  have hb_plus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add
      tendsto_const_nhds
  have hb_inv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hb_plus
  have hb_lim : Tendsto b atTop (nhds (T : ℝ)) := by
    simpa only [sub_zero, b] using
      (tendsto_const_nhds.sub hb_inv :
        Tendsto (fun n : ℕ => (T : ℝ) - ((n : ℝ) + 1)⁻¹)
          atTop (nhds ((T : ℝ) - 0)))
  exact avram_bv_env3_original_oscillating_strict_crossing_cell_cash_tendsto_zero
    D hD ω σ T q hq a ha b hb_mono hb_below hb_lim
