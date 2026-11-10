-- Prove2me | solution 3 for AvramDividend.Classical.avram_bv_finite734_finite_activity_original_cofinal_prefix_expected_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:31:44.58677+00:00
-- url     : https://prove2.me/submissions/64a2f64b-6902-4153-905d-7b78249538e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_discounted_cash_finite_all_paths
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
import Theorems.Thm_AvramDividend_Classical_avram_a19_discounted_cash_terminal_prefix_budget_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Transfer the signed physical-cell certificate to original cofinal finite-activity prefixes. -/
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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hFinite : C ≠ ⊤) (hactivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∃ u : ℕ → ℝ, Monotone u ∧ (∀ n, 0 ≤ u n) ∧ (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) ∧
      (∀ n,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x) := by
  classical
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  let S : ℝ≥0 := ⟨T, hT⟩
  obtain ⟨M, B, Err, hMB, hErrInt, hErrMean, hPhys⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  obtain ⟨v, hv0, hvmono, hvuniform⟩ := avram_a19_physical_strict_horizon_uniform_grid T hTpos
  let u : ℕ → ℝ := fun n => T - δ n
  have hueq (n : ℕ) : (v n (n + 1) : ℝ) = u n := (hv0 n).2
  have hu_nonneg : ∀ n, 0 ≤ u n := by
    intro n
    rw [← hueq n]
    exact NNReal.coe_nonneg _
  have hu_lt : ∀ n, u n < T := by
    intro n
    exact ((avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
      T hTpos).1 n).2
  have hδanti : Antitone δ := by
    intro i j hij
    have hi : 0 < (i : ℝ) + 2 := by positivity
    have hc : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hd : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by linarith
    exact div_le_div_of_nonneg_left (le_of_lt hTpos) hi hd
  have hu_mono : Monotone u := by
    intro i j hij
    dsimp [u]
    have h := hδanti hij
    linarith
  have hu_cofinal : ∀ s : ℝ, s < T → ∃ n, s < u n := by
    intro s hs
    have ht : Tendsto u atTop (nhds T) := by
      simpa only [u, δ] using
        (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hTpos).2
    have he : ∀ᶠ n in atTop, s < u n :=
      ht.eventually (eventually_gt_nhds hs)
    exact he.exists
  let MC : ℕ → Ω → ℝ := fun n ω => M n ω + B n ω
  let Z : ℕ → Ω → ℝ := fun _ _ => 0
  have hMle : ∀ n, Integrable (MC n) P ∧
      (∫ ω, MC n ω ∂P) ≤ 0 := by
    intro n
    exact hMB n
  have hZneg : ∀ n, ∀ᵐ ω ∂P, Z n ω ≤ 0 := by
    intro n
    filter_upwards [] with ω
    exact le_refl _
  have hPhysical : ∀ n, ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤
      w x + (MC n ω + Z n ω) + max (Err n ω) 0 := by
    intro n
    simpa only [MC, Z, u, δ, S, add_zero] using hPhys n
  have hFull :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ∂P) ≤ w x := by
    exact avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S u hu_mono
      hu_nonneg (fun n => le_of_lt (hu_lt n)) hu_cofinal MC Z Err
      hMle hZneg hErrInt hErrMean hPhysical
  have hFin : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≠ ⊤ := by
    filter_upwards [] with ω
    exact avram_limit2_original_strict_discounted_cash_finite_all_paths
      X q (le_of_lt hq) x D hD.1.1 ω T hT
  have hIT := avram_p3_bv_original_strict_cash_L1
    X x C D hD q (le_of_lt hq) T hT
  have hTerm := (avram_p3_g2_original_BV_strict_terminal_joint_L1_and_source_mean_le
    X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hx hxc D hD
    q hjump S).2.1
  refine ⟨u, hu_mono, hu_nonneg, hu_lt, hu_cofinal, ?_⟩
  intro n
  have hIs := avram_p3_bv_original_strict_cash_L1
    X x C D hD q (le_of_lt hq) (u n) (hu_nonneg n)
  have hStep := avram_a19_discounted_cash_terminal_prefix_budget_mono
    P D (ruinTime X x D) q (u n) T (le_of_lt (hu_lt n))
    (fun ω => if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    hFin hIs hIT hTerm
  exact le_trans hStep hFull
