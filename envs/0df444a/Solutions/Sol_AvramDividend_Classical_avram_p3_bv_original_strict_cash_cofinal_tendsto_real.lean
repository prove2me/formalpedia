-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_tendsto_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:59:24.153114+00:00
-- url     : https://prove2.me/submissions/9ea61bda-564b-4ab6-b0f8-05f1ad905bf5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_cash_strict_horizon_mono
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cofinal_real_nNReal_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual original stopped Stieltjes cash converges along every monotone
strict cofinal real grid at a nonnegative observation clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    Tendsto (fun n =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal)
      atTop (nhds
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) := by
  let cash : ℝ → ℝ := fun t =>
    (∫⁻ v in paymentTimes (ruinTime X x D ω) ∩ Iio t,
      ENNReal.ofReal (Real.exp (-(q * v))) ∂dividendMeasure D ω).toReal
  have hfin :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
    lt_of_le_of_lt
      (avram_p3_bv_original_strict_cash_rightlimit_bound
        D hD.1.1 ω (ruinTime X x D ω) S q hq)
      ENNReal.ofReal_lt_top
  have hUpper (n : ℕ) : cash (u n) ≤ cash (S : ℝ) := by
    apply ENNReal.toReal_mono (ne_of_lt hfin)
    exact avram_p3_bv_original_cash_strict_horizon_mono
      X x q (u n) (S : ℝ) (hbelow n) D ω
  have hMon : Monotone (fun n : ℕ => cash (u n)) := by
    intro i j hij
    have hjfin :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u j),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) < ⊤ :=
      lt_of_le_of_lt
        (avram_p3_bv_original_cash_strict_horizon_mono
          X x q (u j) (S : ℝ) (hbelow j) D ω) hfin
    apply ENNReal.toReal_mono (ne_of_lt hjfin)
    exact avram_p3_bv_original_cash_strict_horizon_mono
      X x q (u i) (u j) (hmono hij) D ω
  have hBdd : BddAbove (Set.range (fun n : ℕ => cash (u n))) := by
    refine ⟨cash (S : ℝ), ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hUpper n
  have hSup := avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
    X x C D hD q hq S ω u hmono hbelow hcover
  have hT := tendsto_atTop_ciSup hMon hBdd
  change (⨆ n : ℕ, cash (u n)) = cash (S : ℝ) at hSup
  change Tendsto (fun n => cash (u n)) atTop (nhds (cash (S : ℝ)))
  simpa only [hSup] using hT
