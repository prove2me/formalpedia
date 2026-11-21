-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_cash_mesh_L1_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:02:38.973156+00:00
-- url     : https://prove2.me/submissions/c0769b39-bbd6-48a6-a789-97d61c655b19

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    Tendsto (fun m : ℕ => ∫ ω, |E m ω| ∂P)
      Filter.atTop (𝓝 (0 : ℝ)) := by
  change Tendsto
    (fun m : ℕ => ∫ ω, |(fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) m ω| ∂P)
    atTop (𝓝 (0 : ℝ))
  have hEventual :=
    avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
      X hX x C D hD q hq n hn ρ hρstop hρbound hρruin
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [] with m
    have hpos : (0 : ℝ) ≤ ∫ ω, |(fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) m ω| ∂P :=
      integral_nonneg (fun ω => abs_nonneg _)
    exact lt_of_lt_of_le ha hpos
  · intro a ha
    obtain ⟨k, hk⟩ := hEventual (a / 2) (by linarith)
    filter_upwards [eventually_ge_atTop k] with m hm
    exact lt_of_le_of_lt (hk m hm).2 (by linarith)
