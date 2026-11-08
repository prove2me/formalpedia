-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_prejump_row_ae_clipping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:43:43.152034+00:00
-- url     : https://prove2.me/submissions/33aeadd9-1775-4c16-b78c-ba3d6b508a0f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original post-dividend pre-jump reserves at every physical-grid index are
eventually inside deterministic row-dependent bounds almost surely. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (K n : ℝ) := by
  let a : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
      (u n i)
  have hjoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have ha : ∀ n i, Measurable (fun ω => a n ω i) := by
    intro n i
    exact hjoint.comp (measurable_const.prodMk measurable_id)
  simpa only [a] using
    (avram_bv_residual10_original_rowwise_ae_eventual_clipping
      (P := P) a ha ε hεpos hεlim hεsum)
