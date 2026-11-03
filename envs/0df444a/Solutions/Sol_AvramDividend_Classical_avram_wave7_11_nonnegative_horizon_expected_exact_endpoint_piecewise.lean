-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_nonnegative_horizon_expected_exact_endpoint_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:26:10.237675+00:00
-- url     : https://prove2.me/submissions/65270fce-3bdf-41ba-9bf9-97c36873630e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact all-nonnegative-horizon original expected Stieltjes
    decomposition: at zero the stopped clock already includes the time-zero
    atom; at positive T the original T atom is a separate disjoint term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (min (ruinTime X x D ω) (ENNReal.ofReal T)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) +
    (if T = 0 then 0 else
      (∫⁻ ω, ∫⁻ t in
        (paymentTimes (ruinTime X x D ω) ∩ Iic T) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)) := by
  by_cases hp : 0 < T
  · have hn : T ≠ 0 := ne_of_gt hp
    simpa only [if_neg hn] using
      (avram_wave7_11_original_expected_positive_horizon_exact_endpoint_decomposition
        X x D hD q T hp)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    simp only [if_pos rfl, if_true, add_zero]
    apply lintegral_congr
    intro ω
    calc
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (dividendMeasure D ω) ({0} : Set ℝ) :=
          avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
            D ω (ruinTime X x D ω) q
      _ = (∫⁻ t in paymentTimes
        (min (ruinTime X x D ω) (ENNReal.ofReal (0 : ℝ))) ∩ Iic (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
        (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
          D ω (min (ruinTime X x D ω) (ENNReal.ofReal (0 : ℝ))) q).symm
