-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger30_original_topcap_right_endpoint_cash_without_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:14:09.13286+00:00
-- url     : https://prove2.me/submissions/cfb55a16-af09-476c-a638-84d7fcba313d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_discounted_right_endpoint_cell_upper_error
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Control one original dividend-measure interval using only positive
    pointwise derivative, the exact right-limit increment and discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (A : ℝ) (hpost : 0 ≤ A - rightLimit D b ω)
    (hinc : 0 ≤ rightLimit D b ω - rightLimit D a ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
  have hReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hR : (b : ℝ) - (a : ℝ) ≥ 0 := sub_nonneg.mpr hReal
  have hqd : 0 ≤ q * ((b : ℝ) - (a : ℝ)) := mul_nonneg hq hR
  have hE : 0 ≤ Real.exp (-(q * (b : ℝ))) := (Real.exp_pos _).le
  have hle : A - rightLimit D b ω ≤ A - rightLimit D a ω := by linarith
  have hSec := avram_gledger29_topcap_secant_without_contdiff
    w hw_cont hw_grad (A - rightLimit D b ω)
      (A - rightLimit D a ω) hpost hle
  have hDiff : rightLimit D b ω - rightLimit D a ω ≤
      w (A - rightLimit D a ω) - w (A - rightLimit D b ω) := by
    linarith
  have hMass : dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - rightLimit D b ω)) := by
    rw [dividendMeasure_Ioc_rightLimit D hD ω a b]
    exact ENNReal.ofReal_le_ofReal hDiff
  have hInterval : (0 : ℝ) ≤ (a : ℝ) := a.property
  have hBudget := avram_wave6_08_discounted_right_endpoint_cell_upper_error
    q hq (dividendMeasure D ω) (a : ℝ) (b : ℝ) hInterval hReal
  calc
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal
          (Real.exp (-(q * (b : ℝ))) + q * ((b : ℝ) - (a : ℝ))) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := hBudget
    _ = ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
        ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
      rw [ENNReal.ofReal_add hE hqd, add_mul]
    _ ≤ _ := by
      gcongr <;> exact hMass
