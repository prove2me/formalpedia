-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_finitecap_rightmesh_positiveclock_from_actual_signed_ito
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:35:34.497796+00:00
-- url     : https://prove2.me/submissions/ba2f1caf-b767-4084-85ea-264216747697
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_physical_rightmesh_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_stopped_reward_real_caplinear_cash_exact
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stopped_rightCont_stronglyAdapted
import Theorems.Thm_AvramDividend_Classical_avram_tauceti_original_physical_signed_budget_given_progressivity
import Theorems.Thm_AvramDividend_Classical_avram_original_masked_three_martingales_positiveclock_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn
    w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1
    ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D
    ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop :
    IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes
    (ruinTime X x D ω) ∩ Iic (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas : AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω →
    ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω else
    riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable (F k) P) (hFiniteCap : C ≠ ⊤) :
    ∀ (k m : ℕ),
      let ρ : Ω → ℝ≥0 := fun ω =>
        min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      let V : ℝ → ℝ := fun z =>
        if ENNReal.ofReal z ≤ C then w z
        else w C.toReal + (z - C.toReal)
      let Approx : Ω → ℝ := fun ω =>
        Real.exp (-(q * (ρ ω : ℝ))) *
          V (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
               x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
             else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      (∫⁻ ω in {ω : Ω | ρ ω ≠ 0},
        ENNReal.ofReal (Approx ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω : Ω | ρ ω ≠ 0} := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k m
  let ρ : Ω → ℝ≥0 := fun ω => min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
  let V : ℝ → ℝ := fun z => if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
  let Q : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) * w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Approx : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) * V (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  change (∫⁻ ω in {ω : Ω | ρ ω ≠ 0}, ENNReal.ofReal (Approx ω) ∂P) ≤ ENNReal.ofReal (w x) * P {ω : Ω | ρ ω ≠ 0}
  have hρStop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    avram_f6_original_physical_rightmesh_isStoppingTime τ (σ k) hτstop (hσstop k) ((1 : ℝ≥0) / ((m : ℝ≥0) + 1))
  have hρLe (ω : Ω) : ρ ω ≤ τ ω := min_le_left _ _
  have hρBound (ω : Ω) : ρ ω ≤ (n : ℝ≥0) := by
    have ht : τ ω ≤ (n : ℝ≥0) := by
      rw [hτeq ω]
      have hm : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤ (n : ℝ≥0∞) := min_le_right _ _
      have hnFinite : (n : ℝ≥0∞) ≠ ⊤ := by simp
      simpa using ENNReal.toNNReal_mono hnFinite hm
    exact le_trans (hρLe ω) ht
  have hQI : Integrable Q P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q hq.le w hw_cont hw_neg C hFiniteCap hxc D hD
      n ρ hρStop hρBound Q (by intro ω; rfl)
  have hV (z : ℝ) : V z = (if C = ⊤ then w z else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)) := by
    simp [V, hFiniteCap, ENNReal.ofReal_le_iff_le_toReal hFiniteCap]
  have hApproxQ : Approx = Q := by
    funext ω
    have hs := avram_f6_original_stopped_reward_real_caplinear_cash_exact
      X x C hC hxc w D hD q (fun _ => ρ) (fun _ => Q) (by intro _ _; rfl) 0 ω
    dsimp only at hs
    simpa only [Approx, hV] using hs.symm
  have hQNonneg : ∀ᵐ ω ∂P, 0 ≤ Q ω := Filter.Eventually.of_forall (fun ω =>
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD q ρ Q (by intro η; rfl) ω)
  have hProg : IsStronglyProgressive 𝓕 X.X := tauceti_original_levy_stronglyProgressive X
  have hStopped : ∀ (j : ℕ), StronglyAdapted 𝓕.rightCont
      (stoppedProcess X.X (fun ω => (ρ ω : WithTop ℝ≥0))) := by
    intro j
    exact tauceti_original_levy_stopped_rightCont_stronglyAdapted X (fun ω => (ρ ω : WithTop ℝ≥0)) hρStop
  obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI, hMc0, hMs0, hMl0,
      hG, hR, hSigned⟩ :=
    avram_tauceti_original_physical_signed_budget_given_progressivity
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas
      hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
      (fun _ => ρ) (fun _ => Q)
      (by intro _; exact hρStop) (by intro _ ω; exact hρLe ω)
      (by intro _ ω; rfl) (by intro _; exact hQI) hProg hStopped 0
  have hρmeas : Measurable ρ := measurable_coe_nnreal_ennreal_iff.mp hρStop.measurable'
  have hReal := avram_original_masked_three_martingales_positiveclock_expected_budget
    ρ hρmeas Q hQI (w x) Mc Ms Ml G R hMcI hMsI hMlI hMc0 hMs0 hMl0 hG hR hSigned
  have hwx : 0 ≤ w x :=
    avram_p4_f6_original_hjb_initial_payoff_nonnegative_at_closed_cap
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc
  have hEN := avram_p4_f4_positive_clock_real_to_ennreal_weighted_budget
      (P := P) {ω : Ω | ρ ω ≠ 0} Q (w x) hwx
      hQI hQNonneg hReal
  simpa only [hApproxQ] using hEN
