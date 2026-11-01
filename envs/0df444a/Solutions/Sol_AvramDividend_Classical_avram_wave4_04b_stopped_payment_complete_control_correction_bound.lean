-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_stopped_payment_complete_control_correction_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:55:32.534593+00:00
-- url     : https://prove2.me/submissions/1056c73c-aa2e-4268-b758-f757794c5ba4

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The complete stopped-window Stieltjes cash reward is dominated by
chronological nonpositive right-payment corrections and the full diffuse
gradient term, including arbitrary singular-continuous dividends. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in paymentTimes τ, ENNReal.ofReal (Real.exp (-q * s)) ∂μ) ≤
      (∑' t : A,
        ENNReal.ofReal
          (w (riskProcess X x D (t : ℝ).toNNReal ω) -
            w (riskProcess X x D (t : ℝ).toNNReal ω -
              (rightLimit D (t : ℝ).toNNReal ω -
                D (t : ℝ).toNNReal ω))) *
        (paymentTimes τ).indicator
          (fun s : ℝ => ENNReal.ofReal (Real.exp (-q * s))) (t : ℝ)) +
      (∫⁻ s in paymentTimes τ,
        ENNReal.ofReal (Real.exp (-q * s)) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
          ∂μdiffuse) := by
  dsimp only
  let μ : Measure ℝ :=
    (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
  let v : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-q * s))
  let f : ℝ → ℝ≥0∞ := (paymentTimes τ).indicator v
  let j : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal
      (w (riskProcess X x D s.toNNReal ω) -
        w (riskProcess X x D s.toNNReal ω -
          (rightLimit D s.toNNReal ω - D s.toNNReal ω)))
  let g : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
  have hSupport : ∀ t : ℝ≥0, f (t : ℝ) ≠ 0 →
      (t : ℝ) ∈ paymentTimes τ := by
    intro t hf
    by_contra hnot
    have hzero : f (t : ℝ) = 0 := by
      simp [f, Set.indicator, hnot]
    exact hf hzero
  have hloc' : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C := by
    intro t ht hf
    exact hloc t ht (hSupport t hf)
  have hjump' : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
    intro t ht hf
    exact hjump t ht (hSupport t hf)
  obtain ⟨A, μatom, μdiffuse, hAcount, hAmeas,
    hdecomp, hnull, hBound⟩ :=
    avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction
      X x D hD w C hw_grad ω T f hloc' hjump'
  have hMeas : MeasurableSet (paymentTimes τ) :=
    paymentTimes_measurable τ
  have hL :
      (∫⁻ s : ℝ, f s ∂μ) =
      (∫⁻ s in paymentTimes τ, v s ∂μ) := by
    change (∫⁻ s : ℝ, (paymentTimes τ).indicator v s ∂μ) =
      (∫⁻ s in paymentTimes τ, v s ∂μ)
    exact lintegral_indicator hMeas v
  have hR :
      (∫⁻ s : ℝ, f s * g s ∂μdiffuse) =
      (∫⁻ s in paymentTimes τ, v s * g s ∂μdiffuse) := by
    calc
      (∫⁻ s : ℝ, f s * g s ∂μdiffuse) =
          (∫⁻ s : ℝ, (paymentTimes τ).indicator
            (fun s => v s * g s) s ∂μdiffuse) := by
        apply lintegral_congr
        intro s
        by_cases hs : s ∈ paymentTimes τ <;> simp [f, Set.indicator, hs]
      _ = (∫⁻ s in paymentTimes τ, v s * g s ∂μdiffuse) :=
        lintegral_indicator hMeas (fun s => v s * g s)
  have hBound' :
      (∫⁻ s : ℝ, f s ∂μ) ≤
      (∑' t : A, j (t : ℝ) * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s * g s ∂μdiffuse) := by
    change (∫⁻ s : ℝ, f s ∂μ) ≤
      (∑' t : A, j (t : ℝ) * f (t : ℝ)) +
      (∫⁻ s : ℝ, f s * g s ∂μdiffuse) at hBound
    exact hBound
  refine ⟨A, μatom, μdiffuse, hAcount, hAmeas, hdecomp, hnull, ?_⟩
  change (∫⁻ s in paymentTimes τ, v s ∂μ) ≤
    (∑' t : A, j (t : ℝ) * f (t : ℝ)) +
      (∫⁻ s in paymentTimes τ, v s * g s ∂μdiffuse)
  calc
    (∫⁻ s in paymentTimes τ, v s ∂μ) =
        (∫⁻ s : ℝ, f s ∂μ) := hL.symm
    _ ≤ (∑' t : A, j (t : ℝ) * f (t : ℝ)) +
        (∫⁻ s : ℝ, f s * g s ∂μdiffuse) := hBound'
    _ = (∑' t : A, j (t : ℝ) * f (t : ℝ)) +
        (∫⁻ s in paymentTimes τ, v s * g s ∂μdiffuse) := by rw [hR]
