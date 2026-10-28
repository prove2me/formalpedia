-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_killed_expectation_filter_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:31:12.436653+00:00
-- url     : https://prove2.me/submissions/bef23e2f-d6d4-4922-979e-f3428f65d552

import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_killed_ennreal_scale_payoff_measurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

/-- Fatou's lemma on the full neighbourhood filter at zero gives lower
semicontinuity of the genuinely killed q-scale expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (W x) ≤
      Filter.liminf (fun t : ℝ≥0 => ∫⁻ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P)
        (𝓝 0) := by
  haveI : IsProbabilityMeasure P := X.isProbability
  let f : ℝ≥0 → Ω → ENNReal := fun t ω =>
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => ENNReal.ofReal
        (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω
  have hmeas (t : ℝ≥0) : Measurable (f t) := by
    simpa only [f] using
      (chat04_killed_ennreal_scale_payoff_measurable X q W hW x t)
  have hpt (ω : Ω) :
      Filter.liminf (fun t : ℝ≥0 => f t ω) (𝓝 0) =
      ENNReal.ofReal (W x) := by
    have hlim :=
      chat04_positive_reserve_killed_scale_tendsto_initial X q W hW x hx ω
    have hlim' : Tendsto (fun t : ℝ≥0 => f t ω)
        (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by
      simpa only [f] using hlim
    exact hlim'.liminf_eq
  have hfatou :
      ENNReal.ofReal (W x) ≤
        Filter.liminf (fun t : ℝ≥0 => ∫⁻ ω, f t ω ∂P) (𝓝 0) := by
    calc
      ENNReal.ofReal (W x) =
          (∫⁻ ω, Filter.liminf (fun t : ℝ≥0 => f t ω) (𝓝 0) ∂P) := by
            simp_rw [hpt]
            simp
      _ ≤ _ := MeasureTheory.lintegral_liminf_le hmeas
  simpa only [f] using hfatou
