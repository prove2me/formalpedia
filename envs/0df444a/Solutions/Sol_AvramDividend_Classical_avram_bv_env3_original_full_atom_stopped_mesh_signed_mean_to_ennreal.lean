-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_original_full_atom_stopped_mesh_signed_mean_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:07:20.726107+00:00
-- url     : https://prove2.me/submissions/63cce61a-5499-4780-bbe8-761f97509891

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_full_atom_mesh_signed_mean_native_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (M B : Ω → ℝ) (Mmesh Bmesh : ℕ → Ω → ℝ)
    (hMesh : ∀ᵐ ω ∂P, ∀ n,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if WithTop.some (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
      else 0) ≤ w x + Mmesh n ω + Bmesh n ω)
    (hMLim : ∀ᵐ ω ∂P, Tendsto (fun n => Mmesh n ω) atTop (nhds (M ω)))
    (hBLim : ∀ᵐ ω ∂P, Tendsto (fun n => Bmesh n ω) atTop (nhds (B ω)))
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x) := by

  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  have hMeshNative : ∀ᵐ ω ∂P, ∀ n,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X ⟨T, hT⟩ ω - rightLimit D ⟨T, hT⟩ ω)
       else 0) ≤ w x + Mmesh n ω + Bmesh n ω := by
    filter_upwards [hMesh] with ω hω
    intro n
    have hClock : ((WithTop.some S : ℝ≥0∞) < ruinTime X x D ω) ↔
        ((S : ℝ≥0∞) < ruinTime X x D ω) :=
      avram_bv_env3_withTop_preorder_vs_ennreal_strict_clock S (ruinTime X x D ω)
    have hIte : (if (WithTop.some S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else (0 : ℝ)) =
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω) else 0) := by
      exact ite_congr (propext hClock) (fun _ => rfl) (fun _ => rfl)
    rw [← hIte]
    exact hω n
  exact avram_bv_env3_original_full_atom_mesh_signed_mean_native_ennreal
    X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad x hxc
    D hD T hT hTpos M B Mmesh Bmesh hMeshNative hMLim hBLim hMint hBint hSigned
