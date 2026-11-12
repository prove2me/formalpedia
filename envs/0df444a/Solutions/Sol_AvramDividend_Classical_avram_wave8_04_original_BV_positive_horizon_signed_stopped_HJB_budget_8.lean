-- Prove2me | solution 8 for AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_stopped_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:46:00.555259+00:00
-- url     : https://prove2.me/submissions/903c6251-3184-4a5e-b0c8-a03c8ce09d16
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_source_vanishing_mean_physical_cells
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Term : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) +
      (∫ ω, Term ω ∂P) ≤ w x := by
  intro S Term
  let u : ℕ → ℝ := fun n => T - T / ((n : ℝ) + 2)
  let Cash : ℝ → Ω → ℝ := fun r ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio r,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let Term0 : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) else 0
  obtain ⟨M, B, Err, hMB, hErrInt, hErrMean, hPhysical⟩ :=
    avram_p3_grid4_original_source_vanishing_mean_physical_cells
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
  have hcofinal := avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon T hTpos
  have hmono : Monotone u := by
    intro i j hij
    have hden : (i : ℝ) + 2 ≤ (j : ℝ) + 2 := by
      have hc : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    have hfrac : T / ((j : ℝ) + 2) ≤ T / ((i : ℝ) + 2) :=
      div_le_div_of_nonneg_left (le_of_lt hTpos) (by positivity) hden
    dsimp [u]
    linarith
  have hnonneg : ∀ n, 0 ≤ u n := by
    intro n
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hf : T / ((n : ℝ) + 2) ≤ T := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith
    dsimp [u]
    linarith
  have hbelow : ∀ n, u n ≤ (S : ℝ) := by
    intro n
    dsimp [u, S]
    exact le_of_lt (hcofinal.1 n).2
  have hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n := by
    intro s hs
    have ht : Tendsto u atTop (𝓝 T) := hcofinal.2
    have hst : s < T := by
      change s < T at hs
      exact hs
    exact (ht.eventually (isOpen_Ioi.mem_nhds hst)).exists
  have hST : (S : ℝ) = T := rfl
  have hStrict : (∫ ω, Cash (S : ℝ) ω + Term0 ω ∂P) ≤ w x := by
    have hM : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
        (∫ ω, M n ω + B n ω ∂P) ≤ 0 := hMB
    have hB : ∀ (n : ℕ), ∀ᵐ ω ∂P, (0 : ℝ) ≤ 0 := by simp
    have hPhy : ∀ n, ∀ᵐ ω ∂P,
        Cash (u n) ω + Term0 ω ≤
          w x + ((M n ω + B n ω) + 0) + max (Err n ω) 0 := by
      intro n
      simpa only [add_zero, Cash, Term0, u, hST] using hPhysical n
    exact avram_bv_strict6_original_nonintegrable_B_vanishing_error_budget
      X hBV x C D hD w hw_cont hw_neg q (le_of_lt hq) S
      u hmono hnonneg hbelow hcover
      (fun n ω => M n ω + B n ω) (fun _ _ => 0) Err
      hM hB hErrInt hErrMean hPhy
  have hClosed := avram_p3_bv_original_signed_closed_budget_of_strict_prebudget
    X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
    x hx hxc D hD q (le_of_lt hq) S (by exact_mod_cast hTpos) hjump
    (by simpa [Cash, Term0, S] using hStrict)
  simpa only [Term, hST] using hClosed
