-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_gaussian_ruincontact_L1_from_integrable_compact_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:46:25.359513+00:00
-- url     : https://prove2.me/submissions/ca375dfd-2d6e-4ea0-9427-f89caa0cc60e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
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
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (σ : Ω → ℝ≥0) (T : ℝ≥0)
    (S : ℕ → Finset ℕ) (a b : ℕ → ℕ → ℝ≥0)
    (WG : ℕ → ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hSep : ∀ k i j, i ∈ S k → j ∈ S k → i < j → b k i ≤ a k j)
    (hOrdered : ∀ k i, i ∈ S k → a k i ≤ b k i)
    (hT : ∀ k i, i ∈ S k → b k i ≤ T)
    (hWeights : ∀ k i, i ∈ S k → ∀ ω, ‖WG k i ω‖ ≤ L)
    (hGridSmall : ∀ δ : ℝ≥0, 0 < δ →
      ∃ K : ℕ, ∀ k, K ≤ k → ∀ i ∈ S k, b k i - a k i ≤ δ)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hOsc : ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
      ‖R t ω - R s ω‖ ≤ B ω)
    (hGI : ∀ k, Integrable (fun ω =>
      ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))) P) :
    Tendsto (fun k => ∫ ω,
      ‖((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let H : ℕ → Ω → ℝ := fun k ω =>
    ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
      (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))
  have hAE : ∀ᵐ ω ∂P, Tendsto (fun k => H k ω) atTop (𝓝 (0 : ℝ)) :=
    avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
      X hFinite R hRsource σ T S a b WG L hL hSep hOrdered hT
      hWeights hGridSmall
  have hMajorI : Integrable (fun ω => L * B ω) P :=
    hBI.const_mul L
  have hBound (k : ℕ) : ∀ᵐ ω ∂P, ‖H k ω‖ ≤ L * B ω := by
    filter_upwards [hOsc] with ω hω
    have hBpos : 0 ≤ B ω := by
      have hZero := hω 0 0 (le_refl _)
        (show (0 : ℝ≥0) ≤ T from zero_le)
      simpa only [sub_self, norm_zero] using hZero
    have hCell (i : ℕ) (hi : i ∈ S k) :
        ‖WG k i ω * (R (b k i) ω - R (a k i) ω)‖ ≤ L * B ω := by
      have hWi := hWeights k i hi ω
      have hRi := hω (a k i) (b k i) (hOrdered k i hi) (hT k i hi)
      rw [norm_mul]
      exact mul_le_mul hWi hRi (norm_nonneg _) hL
    exact avram_b24_single_ruincontact_mesh_sum_norm_bound
      (S k) (a k) (b k) (σ ω)
      (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))
      (hSep k) (L * B ω) (mul_nonneg hL hBpos) hCell
  have hLimit :=
    avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
      H (fun ω => L * B ω) hGI hMajorI hBound hAE
  exact hLimit
