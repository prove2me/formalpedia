-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_weighted_ruincontact_gaussian_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:41:40.571413+00:00
-- url     : https://prove2.me/submissions/e3bf66fc-cbec-4da2-86a5-c5da87de355a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_single_ruincontact_mesh_sum_norm_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_gaussian_global_continuity_compact_time_modulus
import Theorems.Thm_AvramDividend_Classical_avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
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
 :
    ∀ᵐ ω ∂P, Tendsto
      (fun k : ℕ =>
        ((S k).filter (fun i => a k i < σ ω ∧ σ ω ≤ b k i)).sum
          (fun i => WG k i ω * (R (b k i) ω - R (a k i) ω)))
      atTop (𝓝 (0 : ℝ)) := by
  have hMod :=
    AvramDividend.Classical.avram_b24_original_gaussian_global_continuity_compact_time_modulus
      X hFinite R hRsource T
  exact
    AvramDividend.Classical.avram_b24_gaussian_weighted_ruincontact_mesh_ae_vanish_from_modulus
      R σ T S a b WG L hL hSep hOrdered hT hWeights hGridSmall hMod
