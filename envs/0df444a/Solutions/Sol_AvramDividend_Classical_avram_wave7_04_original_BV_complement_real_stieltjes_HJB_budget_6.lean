-- Prove2me | solution 6 for AvramDividend.Classical.avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:07:47.47477+00:00
-- url     : https://prove2.me/submissions/7fb3c4a9-ebdb-4d47-9fbe-7f7f46908dc1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Closed dividend cash follows from the original stopped physical source certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      w x := by
  classical
  have hTpos : 0 < T :=
    (avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
      X C hC w hw_cont hw0 hw_smooth hw_grad x hx hxc T hT hEnvelope).2.2.1
  let S : ℝ≥0 := ⟨T, le_of_lt hTpos⟩
  have hStoT : (S : ℝ) = T := rfl
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  have huconv : Tendsto u atTop (𝓝 T) :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hTpos).2
  have hmono : Monotone u := by
    intro a b hab
    dsimp [u]
    have hden : (a : ℝ) + 2 ≤ (b : ℝ) + 2 := by
      have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
      simpa only [add_comm] using (add_le_add_right hcast 2)
    have hdiv : T / ((b : ℝ) + 2) ≤ T / ((a : ℝ) + 2) :=
      div_le_div_of_nonneg_left (le_of_lt hTpos) (by positivity) hden
    linarith
  have hu : ∀ n, 0 ≤ u n := by
    intro n
    dsimp [u]
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hdpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hdiv : T / ((n : ℝ) + 2) ≤ T := by
      apply (div_le_iff₀ hdpos).2
      nlinarith
    linarith
  have hbelow : ∀ n, u n ≤ (S : ℝ) := by
    intro n
    have hgap : 0 < T / ((n : ℝ) + 2) :=
      (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hTpos).1 n |>.1
    change T - T / ((n : ℝ) + 2) ≤ T
    exact sub_le_self T (le_of_lt hgap)
  have hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n := by
    intro s hs
    change s < T at hs
    have hevent : ∀ᶠ n : ℕ in atTop, s < u n :=
      huconv.eventually (eventually_gt_nhds hs)
    exact hevent.exists
  obtain ⟨M, B, Err, hMB, hErrInt, hErrMean, hPhysical⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  have hPhysical' : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) ≤
      w x + ((M n ω + B n ω) + 0) + max (Err n ω) 0 := by
    intro n
    simpa only [u, hStoT, add_zero] using hPhysical n
  have hStrict :=
    avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S
      u hmono hu hbelow hcover
      (fun n ω => M n ω + B n ω) (fun _ _ => 0) Err
      (by simpa using hMB)
      (by intro n; filter_upwards [] with ω; exact le_refl _)
      hErrInt hErrMean (by simpa only [hStoT, add_zero] using hPhysical')
  have hClosed :=
    avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD q (le_of_lt hq) S
      (by exact_mod_cast hTpos) hjump (by simpa [S] using hStrict)
  have hTerminal :=
    (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x D hD T hT hTpos).2
  have hTerminalMean :
      0 ≤ ∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
        else 0) ∂P := by
    change (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0) ∂P) =
      (∫ ω, (if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
      else 0) ∂P) at hTerminal
    rw [hTerminal]
    apply integral_nonneg
    intro ω
    dsimp
    split_ifs <;> positivity
  have hClosed' :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P) +
      (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
       else 0 ∂P) ≤ w x := by
    change
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal ∂P) +
      (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
       else 0 ∂P) ≤ w x at hClosed
    exact hClosed
  linarith
