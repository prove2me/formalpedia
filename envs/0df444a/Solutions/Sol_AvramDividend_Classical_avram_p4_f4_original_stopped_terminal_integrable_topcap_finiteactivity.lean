-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f4_original_stopped_terminal_integrable_topcap_finiteactivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:26:28.494375+00:00
-- url     : https://prove2.me/submissions/b58bf045-df49-4b74-9de6-34eafda44dbc

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_true_ruinbranch_W_le_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_chat25_topcap_candidate_nonnegative_global
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

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
    (hCashI : Integrable Cash P) (hTop : C = ⊤)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) : Integrable Term P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  rcases avram_jp23_original_mixed_topcap_exponential_runningSup_L1_dominator
      X hX hBV hFiniteActivity q hq w C hC hTop hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x (n : ℝ≥0) with
    ⟨θ, K, hθ, hK, hGrowth, hDomI⟩
  have hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    exact hw_smooth.of_le (by norm_num)
  have hwNonneg : ∀ y : ℝ, 0 ≤ w y :=
    avram_chat25_topcap_candidate_nonnegative_global
      C hTop w hw_cont hw0 hw_neg hwC1 hw_grad
  have hτle (ω : Ω) : τ ω ≤ (n : ℝ≥0) := by
    rw [hτeq ω]
    exact ENNReal.toNNReal_mono (by simp) (min_le_right _ _)
  have hWG (ω : Ω) : W ω ≤ x + runningSup X (n : ℝ≥0) ω := by
    rw [hW ω]
    exact avram_f6_original_true_ruinbranch_W_le_runningSup
      X x D hD.1.1 (n : ℝ≥0) (τ ω) (hτle ω) ω
  have hTermNonneg (ω : Ω) : 0 ≤ Term ω := by
    rw [hTerm ω]
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hwNonneg _)
  have hDisc (ω : Ω) : Real.exp (-(q * (τ ω : ℝ))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have ht : 0 ≤ (τ ω : ℝ) := by positivity
    nlinarith [le_of_lt hq]
  have hGrowthAll (y : ℝ) : w y ≤ K * Real.exp (θ * y) := by
    by_cases hy : 0 ≤ y
    · exact hGrowth y hy
    · rw [hw_neg y (lt_of_not_ge hy)]
      exact mul_nonneg hK (le_of_lt (Real.exp_pos _))
  apply Integrable.mono' hDomI hTermMeas
  filter_upwards [] with ω
  have hwUp : w (W ω) ≤ K * Real.exp (θ * W ω) := hGrowthAll _
  have hexp : Real.exp (θ * W ω) ≤
      Real.exp (θ * (x + runningSup X (n : ℝ≥0) ω)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (hWG ω) hθ
  have hterm : Term ω ≤
      K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) ω)) := by
    rw [hTerm ω]
    calc
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω) ≤ w (W ω) := by
        have ha := mul_le_mul_of_nonneg_right (hDisc ω) (hwNonneg (W ω))
        nlinarith
      _ ≤ K * Real.exp (θ * W ω) := hwUp
      _ ≤ K * Real.exp (θ * (x + runningSup X (n : ℝ≥0) ω)) :=
        mul_le_mul_of_nonneg_left hexp hK
  have hBnonneg : 0 ≤ K * Real.exp
      (θ * (x + runningSup X (n : ℝ≥0) ω)) :=
    mul_nonneg hK (le_of_lt (Real.exp_pos _))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hTermNonneg ω),
    abs_of_nonneg hBnonneg] using hterm
