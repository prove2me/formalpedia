-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_intrinsic_gaussian_last_partial_stopped_mesh_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:06:14.019178+00:00
-- url     : https://prove2.me/submissions/6f3cd000-bf64-4e22-bc98-65f2dd66db60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
import Theorems.Thm_AvramDividend_Classical_avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun j : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X j t ω)
        atTop (𝓝 (R t ω)))
    (n : ℕ) (hn : 0 < n)
    (hSquare : Integrable (fun ω => (R (n : ℝ≥0) ω) ^ 2) P)
    (σ : Ω → ℝ≥0) (a b : ℕ → ℝ≥0)
    (hab : ∀ k, a k ≤ b k ∧ b k ≤ (n : ℝ≥0))
    (hMesh : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → b k - a k ≤ δ)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hWeights : ∀ k ω, ‖W k ω‖ ≤ L)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ k ω, F k ω =
      if a k < σ ω ∧ σ ω ≤ b k then
        W k ω * (R (b k) ω - R (a k) ω)
      else 0)
    (hFm : ∀ k, AEStronglyMeasurable (F k) P) :
    (∀ k, Integrable (F k) P) ∧
    Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨B, hBI, hBbound⟩ :=
    avram_ja18_intrinsic_gaussian_physical_Doob_L2_maximal_transfer
      X hX hFinite R hRsource n hn hSquare
  have hMajI : Integrable (fun ω => 2 * L * |B ω|) P := by
    exact (hBI.abs.const_mul (2 * L))
  have hMajor (k : ℕ) : ∀ᵐ ω ∂P, ‖F k ω‖ ≤ 2 * L * |B ω| := by
    filter_upwards [hBbound] with ω hw
    rw [hF k ω]
    split_ifs with ht
    · have ha : a k ≤ b k := (hab k).1
      have hb : b k ≤ (n : ℝ≥0) := (hab k).2
      have hRa : ‖R (a k) ω‖ ≤ B ω := hw _ (le_trans ha hb)
      have hRb : ‖R (b k) ω‖ ≤ B ω := hw _ hb
      have hsum : ‖R (b k) ω - R (a k) ω‖ ≤ 2 * B ω := by
        calc
          _ ≤ ‖R (b k) ω‖ + ‖R (a k) ω‖ := norm_sub_le _ _
          _ ≤ 2 * B ω := by linarith
      have hnB : 0 ≤ B ω := le_trans (norm_nonneg _) hRb
      calc
        ‖W k ω * (R (b k) ω - R (a k) ω)‖ =
          ‖W k ω‖ * ‖R (b k) ω - R (a k) ω‖ := norm_mul _ _
        _ ≤ L * (2 * B ω) := by gcongr; exact hWeights k ω
        _ = 2 * L * |B ω| := by rw [abs_of_nonneg hnB]; ring
    · simp [hL, mul_nonneg]
  have hFI : ∀ k, Integrable (F k) P := by
    intro k
    exact hMajI.mono' (hFm k) (hMajor k)
  constructor
  · exact hFI
  · apply avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
      X hFinite R hRsource σ (n : ℝ≥0)
      (fun _ => {0}) (fun k _ => a k) (fun k _ => b k)
      (fun k _ => W k) L hL
    · intro k i j hi hj hij
      simp at hi hj
      omega
    · intro k i hi
      simpa using (hab k).1
    · intro k i hi
      simpa using (hab k).2
    · intro k i hi ω
      exact hWeights k ω
    · intro δ hδ
      obtain ⟨K, hK⟩ := hMesh δ hδ
      refine ⟨K, ?_⟩
      intro k hk i hi
      exact hK k hk
    · intro k ω
      rw [hF k ω]
      by_cases h : a k < σ ω ∧ σ ω ≤ b k
      · simp [h]
      · simp [h]
    · exact hMajI
    · exact hFI
    · exact hMajor
