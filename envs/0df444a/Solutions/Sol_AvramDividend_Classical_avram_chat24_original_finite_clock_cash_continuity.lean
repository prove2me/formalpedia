-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_finite_clock_cash_continuity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:22:07.551107+00:00
-- url     : https://prove2.me/submissions/c5c008ca-1b21-4bce-9a92-41ee67848e29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_chat24_finite_strict_cash_prefix_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original dividend-strategy finite-clock cash continuity from exact strict prefixes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (t T : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t) (hm : Monotone u)
    (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => (∫⁻ y in Ico (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal) atTop
      (nhds (∫⁻ y in paymentTimes (t : ℝ≥0∞) ∩ Iio (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal) := by
  have hPay : paymentTimes (t : ℝ≥0∞) = Ico (0 : ℝ) (t : ℝ) := by
    ext y
    change (0 ≤ y ∧ (y = 0 ∨ ENNReal.ofReal y < (t : ℝ≥0∞))) ↔
      (0 ≤ y ∧ y < (t : ℝ))
    constructor
    · rintro ⟨hy, hzero | hstrict⟩
      · subst y
        exact ⟨le_refl _, by exact_mod_cast ht⟩
      · exact ⟨hy, (ENNReal.ofReal_lt_coe_iff hy).mp hstrict⟩
    · rintro ⟨hy, hstrict⟩
      exact ⟨hy, Or.inr ((ENNReal.ofReal_lt_coe_iff hy).mpr hstrict)⟩
  have hClosed : paymentTimes (t : ℝ≥0∞) ∩ Iic (T : ℝ) =
      Ico (0 : ℝ) (t : ℝ) := by
    rw [hPay]
    apply Set.inter_eq_left.mpr
    intro y hy
    exact hy.2.le.trans (by exact_mod_cast htT)
  have hOpen : paymentTimes (t : ℝ≥0∞) ∩ Iio (T : ℝ) =
      Ico (0 : ℝ) (t : ℝ) := by
    rw [hPay]
    apply Set.inter_eq_left.mpr
    intro y hy
    exact hy.2.trans_le (by exact_mod_cast htT)
  have hI : IntegrableOn (fun y : ℝ => Real.exp (-(q * y)))
      (Ico (0 : ℝ) (t : ℝ)) (dividendMeasure D ω) := by
    simpa only [hClosed] using
      (avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
        D hD ω (t : ℝ≥0∞) T q hq)
  have hfinite :
      (∫⁻ y in Ico (0 : ℝ) (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    have hEq :
        (∫⁻ y in Ico (0 : ℝ) (t : ℝ),
          ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)) =
        (∫⁻ y in Ico (0 : ℝ) (t : ℝ),
          ‖Real.exp (-(q * y))‖ₑ ∂(dividendMeasure D ω)) := by
      apply lintegral_congr
      intro y
      exact (Real.enorm_eq_ofReal (Real.exp_pos _).le).symm
    rw [hEq]
    exact (show (∫⁻ y in Ico (0 : ℝ) (t : ℝ),
      ‖Real.exp (-(q * y))‖ₑ ∂(dividendMeasure D ω)) < ⊤
      from hI.hasFiniteIntegral).ne
  have hCont := avram_chat24_finite_strict_cash_prefix_continuity
    (dividendMeasure D ω) (fun y : ℝ => ENNReal.ofReal (Real.exp (-(q * y))))
    (by fun_prop) (fun n => (u n : ℝ)) (t : ℝ)
    (fun a b hab => by exact_mod_cast hm hab)
    (fun n => by exact_mod_cast hu n)
    ((NNReal.continuous_coe.tendsto t).comp hl) hfinite
  rw [hOpen]
  exact hCont
