-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_any_clock_strict_signed_to_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:27:27.318578+00:00
-- url     : https://prove2.me/submissions/62b1b13b-df3e-44f5-beaf-a139d47d44d6

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_full_atom_mesh_signed_mean_native_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (M B : Ω → ℝ)
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0)
    (hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  have hS0 : S ≠ 0 := ne_of_gt (show 0 < S from hTpos)
  have hMesh : ∀ᵐ ω ∂P, ∀ n : ℕ,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω := by
    filter_upwards [hWitness] with ω hω
    intro n
    have hPath := avram_p3_g2_original_any_clock_full_cash_post_le_strict_or_zero_initial_from_source
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hx hxc D hD (fun _ => S) ω
    simp only [hS0, if_false] at hPath
    simp [S] at hPath
    exact le_trans hPath hω
  exact avram_bv_env3_original_full_atom_mesh_signed_mean_native_ennreal
    X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x hxc
    D hD T hT hTpos M B (fun _ => M) (fun _ => B) hMesh
    (Filter.Eventually.of_forall (fun ω => tendsto_const_nhds))
    (Filter.Eventually.of_forall (fun ω => tendsto_const_nhds))
    hMint hBint hSigned
