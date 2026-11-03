-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_uniform_horizons_iff_exact_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:41:39.424593+00:00
-- url     : https://prove2.me/submissions/eff459f1-9491-425d-8e2a-b4f2d4a6a58c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_zero_cap_admissible_dividendValue_le_barrier_at_zero
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact complete boundary branch: for a genuine finite-activity
BV source, the same allowance bounds every original admissible zero-cap
Stieltjes payment at every finite horizon iff it bounds the reflected
first-jump value. No altered process or sample space is introduced. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal W) ↔
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W := by
  constructor
  · intro hAll
    apply
      (avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
        X hX hBV hFinite q hq W).mp
    have hBarrier : IsAdmissibleLe X 0 (0 : ℝ≥0∞)
        (barrierStrategy X 0 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (barrierStrategy_admissibleLe_nonnegative_barrier
          X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
    intro n
    exact hAll (barrierStrategy X 0 0) hBarrier n
  · intro hThreshold D hD n
    have hFiniteBound :
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤
        dividendValue X q 0 D := by
      rw [dividendValue_eq_iSup_truncated X q 0 D hD.1]
      exact le_iSup_of_le n le_rfl
    have hComparison :=
      zero_cap_admissible_dividendValue_le_barrier_at_zero
        X hX q hq D hD
    rw [barrierValue_self_eq_barrierSupValue,
      bv_finite_activity_zero_reflected_first_jump_payout
        X hX q hq hBV hFinite] at hComparison
    exact (hFiniteBound.trans hComparison).trans
      (ENNReal.ofReal_le_ofReal hThreshold)
