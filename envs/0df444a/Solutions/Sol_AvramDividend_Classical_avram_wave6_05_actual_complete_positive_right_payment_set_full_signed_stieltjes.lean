-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_actual_complete_positive_right_payment_set_full_signed_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:51:40.866575+00:00
-- url     : https://prove2.me/submissions/22daa669-f59d-427f-a988-720efc207da5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_interior_gradient_signed_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

noncomputable section

/-- The complete original strictly positive pre-ruin right-payment set on
the closed horizon is automatically countable, and the actual full Stieltjes
diffuse, all positive jump, and initial V corrections have nonpositive sum.
Only real summability and actual atomless interior localisation are assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (B : Set ℝ≥0)
    (hBExact : B = {t : ℝ≥0 | 0 < t ∧
      (t : ℝ≥0∞) < ruinTime X x D ω ∧
      t ≤ T ∧ 0 < rightLimit D t ω - D t ω})
    (hSummable : Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∀ᵐ s ∂μdiffuse.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        0 < (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω) ∧
        ENNReal.ofReal (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω) < C) →
        (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse) +
        (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            w (riskProcess X x D (t : ℝ≥0) ω))) +
        ((rightLimit D 0 ω - D 0 ω) +
          V (riskProcess X x D 0 ω -
            (rightLimit D 0 ω - D 0 ω)) -
          V (riskProcess X x D 0 ω)) ≤ 0) := by
  have hAllCount :=
    avram_wave6_05_actual_original_all_nonzero_right_payment_times_countable_on_closed_horizon
      X x D hD.1.1 ω T
  have hBCount : B.Countable := by
    rw [hBExact]
    refine hAllCount.mono ?_
    intro t ht
    exact ⟨ht.2.2.1, ht.2.2.2⟩
  have hB : ∀ t : B, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω := by
    intro t
    have ht : (t : ℝ≥0) ∈ {r : ℝ≥0 | 0 < r ∧
        (r : ℝ≥0∞) < ruinTime X x D ω ∧
        r ≤ T ∧ 0 < rightLimit D r ω - D r ω} := by
      simpa [hBExact] using t.property
    exact ⟨ht.1, ht.2.1⟩
  have hBWithin : ∀ t : B, (t : ℝ≥0) ≤ T := by
    intro t
    have ht : (t : ℝ≥0) ∈ {r : ℝ≥0 | 0 < r ∧
        (r : ℝ≥0∞) < ruinTime X x D ω ∧
        r ≤ T ∧ 0 < rightLimit D r ω - D r ω} := by
      simpa [hBExact] using t.property
    exact ht.2.2.1
  exact avram_wave6_05_actual_original_full_stieltjes_interior_gradient_signed_bridge
    X x C hC q w V hw_cont hw_smooth hw_grad
    hVtop hVfinite D hD ω T B hBCount hB hBWithin hSummable
