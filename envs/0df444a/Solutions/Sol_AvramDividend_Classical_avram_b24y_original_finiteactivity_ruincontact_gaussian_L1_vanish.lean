-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24y_original_finiteactivity_ruincontact_gaussian_L1_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:19:49.072286+00:00
-- url     : https://prove2.me/submissions/03470771-5592-489a-8eb4-a3b9f7223a73

import Mathlib
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun n : ℕ =>
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

    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hFI : ∀ k, Integrable (F k) P)
    (hBound : ∀ k, ∀ᵐ ω ∂P, ‖F k ω‖ ≤ B ω) :
    Filter.Tendsto (fun k => ∫ ω, ‖F k ω‖ ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hAe := avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
    X hFinite R hRsource σ T S a b WG L hL hSep hOrdered hT hWeights hGridSmall
  have hLim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun k => F k ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hAe] with ω hω
    have hFn : (fun k => F k ω) =
      (fun k => ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
        (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω))) := by
      funext k
      exact hFsource k ω
    rw [hFn]
    exact hω
  exact avram_b24_ruincontact_L1_vanish_from_ae_limit_integrable_domination
    F B hFI hBI hBound hLim
