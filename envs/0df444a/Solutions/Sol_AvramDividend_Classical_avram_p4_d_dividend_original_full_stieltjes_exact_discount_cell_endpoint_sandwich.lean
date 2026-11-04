-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_full_stieltjes_exact_discount_cell_endpoint_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:42:14.164748+00:00
-- url     : https://prove2.me/submissions/c30f0bed-a85d-489e-b957-edf328a91af9

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original full Stieltjes discount integral lies between endpoint-weighted cell masses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≤
      (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ∧
    (∫⁻ u in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * u))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by
  apply avram_p4_d_dividend_original_full_stieltjes_cell_weight_lintegral_sandwich
    D hD ω a b
    (ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))))
    (ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))))
    (fun u => ENNReal.ofReal (Real.exp (-(q * u))))
  · intro u hu
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hu.2 hq
    linarith
  · intro u hu
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left (le_of_lt hu.1) hq
    linarith
