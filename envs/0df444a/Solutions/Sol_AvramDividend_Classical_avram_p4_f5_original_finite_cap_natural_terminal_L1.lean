-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f5_original_finite_cap_natural_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:20:22.196534+00:00
-- url     : https://prove2.me/submissions/b490bdc6-5781-4474-991a-421a12edde8c

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hFinite : C ≠ ⊤) : Integrable Term P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hWcap : ∀ ω, W ω ≤ C.toReal := by
    intro ω
    exact (ENNReal.ofReal_le_iff_le_toReal hFinite).mp
      (AvramDividend.Classical.avram_wave8_08_source_piecewise_stopped_terminal_ofReal_le_cap
        X x C D hD hxc τ W hW ω)
  have hcont : ContinuousOn w (Icc (0 : ℝ) C.toReal) := by
    apply hw_cont.mono
    intro y hy
    exact hy.1
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hBnonneg : 0 ≤ B := by
    exact (norm_nonneg (w 0)).trans (hB 0 ⟨le_refl _, ENNReal.toReal_nonneg⟩)
  have hWbound : ∀ ω, ‖w (W ω)‖ ≤ B := by
    intro ω
    by_cases hneg : W ω < 0
    · simpa [hw_neg (W ω) hneg] using hBnonneg
    · exact hB (W ω) ⟨le_of_not_gt hneg, hWcap ω⟩
  have hTermBound : ∀ᵐ ω ∂P, ‖Term ω‖ ≤ B := by
    apply Filter.Eventually.of_forall
    intro ω
    have hExpNonneg : 0 ≤ Real.exp (-(q * (τ ω : ℝ))) := Real.exp_nonneg _
    have hTimeNonneg : 0 ≤ (τ ω : ℝ) := (τ ω).property
    have hExpLe : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg hq.le hTimeNonneg))
    calc
      ‖Term ω‖ =
          Real.exp (-(q * (τ ω : ℝ))) * ‖w (W ω)‖ := by
            rw [hTerm ω, norm_mul]
            simp only [Real.norm_eq_abs, abs_of_nonneg hExpNonneg]
      _ ≤ 1 * ‖w (W ω)‖ :=
          mul_le_mul_of_nonneg_right hExpLe (norm_nonneg _)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_left (hWbound ω) zero_le_one
      _ = B := one_mul _
  exact Integrable.of_bound hTermMeas B hTermBound
