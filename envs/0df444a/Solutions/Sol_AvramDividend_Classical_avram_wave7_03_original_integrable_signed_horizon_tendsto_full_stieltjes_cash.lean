-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_integrable_signed_horizon_tendsto_full_stieltjes_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:56:44.846911+00:00
-- url     : https://prove2.me/submissions/a4a08f4d-80eb-49af-aaa0-daf91f5854da

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- For genuine original signed Stieltjes integrability, finite stopped
    payment horizons converge to the full original discounted cash integral. -/
/- Recovered exact original Stieltjes horizon identity after terminal proof-storage failure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    Tendsto (fun n : ℕ =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))
      atTop (𝓝 (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω))) := by
  let A : Set ℝ := paymentTimes (ruinTime X x D ω)
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ := fun t => Real.exp (-(q * t))
  have hInt' : Integrable f (μ.restrict A) := hInt
  have hTail :=
    avram_wave7_03_original_unrestricted_integrable_signed_stieltjes_tail_tendsto_zero
      X x D ω q hInt
  have hEq (n : ℕ) :
      (∫ t in A ∩ Iic (n : ℝ), f t ∂μ) =
      (∫ t in A, f t ∂μ) -
      (∫ t in A ∩ Ioi (n : ℝ), f t ∂μ) := by
    have hSplit :=
      integral_add_compl (μ := μ.restrict A) (f := f)
        (s := Iic (n : ℝ)) measurableSet_Iic hInt'
    have hLeft :
        (∫ t in Iic (n : ℝ), f t ∂(μ.restrict A)) =
        (∫ t in A ∩ Iic (n : ℝ), f t ∂μ) := by
      rw [Measure.restrict_restrict measurableSet_Iic]
      rw [inter_comm (Iic (n : ℝ)) A]
    have hRight :
        (∫ t in (Iic (n : ℝ))ᶜ, f t ∂(μ.restrict A)) =
        (∫ t in A ∩ Ioi (n : ℝ), f t ∂μ) := by
      rw [compl_Iic]
      rw [Measure.restrict_restrict measurableSet_Ioi]
      rw [inter_comm (Ioi (n : ℝ)) A]
    rw [hLeft, hRight] at hSplit
    linarith only [hSplit]
  have hLim :
      Tendsto (fun n : ℕ => (∫ t in A, f t ∂μ) -
        (∫ t in A ∩ Ioi (n : ℝ), f t ∂μ)) atTop
        (𝓝 ((∫ t in A, f t ∂μ) - (0 : ℝ))) :=
    tendsto_const_nhds.sub (by simpa only [A, μ, f] using hTail)
  simpa only [A, μ, f, hEq, sub_zero] using hLim
