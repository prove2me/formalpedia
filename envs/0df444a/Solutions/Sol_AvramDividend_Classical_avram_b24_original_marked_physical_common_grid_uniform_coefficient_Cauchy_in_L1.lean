-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_marked_physical_common_grid_uniform_coefficient_Cauchy_in_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:10:18.991019+00:00
-- url     : https://prove2.me/submissions/3841bb85-4245-4a2e-b223-db2433b1e263

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (W : ℕ → ℕ → Ω → ℝ)
    (G : ℕ → Ω → ℝ)
    (hG : ∀ m ω, G m ω = ∑ i ∈ S,
      W m i ω * (Jsmall (b i) ω - Jsmall (a i) ω))
    (hGI : ∀ m, Integrable (G m) P)
    (hW : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      ∀ i ∈ S, ∀ ω, ‖W m i ω - W l i ω‖ ≤ ε)
    (V : ℝ) (hV : 0 ≤ V)
    (hVarI : Integrable (fun ω =>
      ∑ i ∈ S, ‖Jsmall (b i) ω - Jsmall (a i) ω‖) P)
    (hVarMean : (∫ ω,
      ∑ i ∈ S, ‖Jsmall (b i) ω - Jsmall (a i) ω‖ ∂P) ≤ V) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / (V + 1)
  have hDen : 0 < V + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hDen
  obtain ⟨N, hN⟩ := hW δ hδ
  refine ⟨N, ?_⟩
  intro m l hm hl
  have hDiff (ω : Ω) :
      (∑ i ∈ S,
        (W m i ω - W l i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) =
      G m ω - G l ω := by
    rw [hG m ω, hG l ω, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hDiffI : Integrable (fun ω =>
      ∑ i ∈ S,
        (W m i ω - W l i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)) P := by
    have hGI' := (hGI m).sub (hGI l)
    convert hGI' using 1
    funext ω
    exact (hDiff ω)
  have hRate :=
    AvramDividend.Classical.avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
      X hFinite Jsmall hJsource S a b (W m) (W l) δ hδ.le
      (fun i hi ω => hN m l hm hl i hi ω) hDiffI hVarI V hV hVarMean
  have hBound : δ * V ≤ ε := by
    have hMul : δ * V ≤ δ * (V + 1) :=
      mul_le_mul_of_nonneg_left (by linarith : V ≤ V + 1) hδ.le
    have hCancel : δ * (V + 1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt hDen)
    exact hMul.trans_eq hCancel
  have hIdent :
      (∫ ω, ‖∑ i ∈ S,
        (W m i ω - W l i ω) *
          (Jsmall (b i) ω - Jsmall (a i) ω)‖ ∂P) =
      (∫ ω, ‖G m ω - G l ω‖ ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hDiff ω]
  rw [hIdent] at hRate
  exact hRate.trans hBound
