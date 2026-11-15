-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_true_original_marked_refining_physical_mesh_gain_L1_Cauchy_from_common_refinement
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:26:48.915413+00:00
-- url     : https://prove2.me/submissions/0b693885-6a89-46bb-9a4f-09d75b807cb6

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
    (G : ℕ → Ω → ℝ)
    (hGI : ∀ n, Integrable (G n) P)
    (S : ℕ → ℕ → Finset ℕ)
    (a b : ℕ → ℕ → ℕ → ℝ≥0)
    (Wleft Wright : ℕ → ℕ → ℕ → Ω → ℝ)
    (hRefine : ∀ m l ω,
      G m ω - G l ω =
        ∑ i ∈ S m l,
          (Wleft m l i ω - Wright m l i ω) *
            (Jsmall (b m l i) ω - Jsmall (a m l i) ω))
    (V : ℝ) (hV : 0 ≤ V)
    (hVarI : ∀ m l, Integrable (fun ω =>
      ∑ i ∈ S m l,
        ‖Jsmall (b m l i) ω - Jsmall (a m l i) ω‖) P)
    (hVarMean : ∀ m l,
      (∫ ω, ∑ i ∈ S m l,
        ‖Jsmall (b m l i) ω - Jsmall (a m l i) ω‖ ∂P) ≤ V)
    (hWeights : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
        ∀ i ∈ S m l, ∀ ω,
          ‖Wleft m l i ω - Wright m l i ω‖ ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ m l, N ≤ m → N ≤ l →
      (∫ ω, ‖G m ω - G l ω‖ ∂P) ≤ ε := by
  intro ε hε
  let δ : ℝ := ε / (V + 1)
  have hDen : 0 < V + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hDen
  obtain ⟨N, hN⟩ := hWeights δ hδ
  refine ⟨N, ?_⟩
  intro m l hm hl
  have hSumI : Integrable (fun ω =>
      ∑ i ∈ S m l,
        (Wleft m l i ω - Wright m l i ω) *
          (Jsmall (b m l i) ω - Jsmall (a m l i) ω)) P := by
    refine ((hGI m).sub (hGI l)).congr ?_
    filter_upwards [] with ω
    exact hRefine m l ω
  have hRate :=
    AvramDividend.Classical.avram_b24_original_intrinsic_marked_mesh_weight_perturbation_L1_variation_bound
      X hFinite Jsmall hJsource
      (S m l) (a m l) (b m l)
      (Wleft m l) (Wright m l) δ hδ.le
      (fun i hi ω => hN m l hm hl i hi ω)
      hSumI (hVarI m l) V hV (hVarMean m l)
  have hId : (∫ ω, ‖∑ i ∈ S m l,
      (Wleft m l i ω - Wright m l i ω) *
        (Jsmall (b m l i) ω - Jsmall (a m l i) ω)‖ ∂P) =
      (∫ ω, ‖G m ω - G l ω‖ ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← hRefine m l ω]
  rw [hId] at hRate
  have hBudget : δ * V ≤ ε := by
    have hStep : δ * V ≤ δ * (V + 1) :=
      mul_le_mul_of_nonneg_left (by linarith : V ≤ V + 1) hδ.le
    have hCancel : δ * (V + 1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt hDen)
    exact hStep.trans_eq hCancel
  exact hRate.trans hBudget
