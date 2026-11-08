-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_prejump_measurable_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:48:30.012406+00:00
-- url     : https://prove2.me/submissions/0afb1441-eba1-4dbe-a494-6d592dec0eea

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_row_ae_clipping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- The original rowwise pre-jump clipping supplies both the measurable
events and their almost-sure eventual exhaustion required by a stopped
positive-error localisation argument. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ K : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n = {ω | ∀ i ∈ Finset.range (n + 1),
        abs (Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
          (u n i)) ≤ (K n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by
  obtain ⟨K, hK⟩ :=
    avram_bv_residual10_original_prejump_row_ae_clipping
      (P := P) X x D hD u ε hεpos hεlim hεsum
  let a : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
      (u n i)
  let s : ℕ → Set Ω := fun n =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a n ω i) ≤ (K n : ℝ)}
  have hjoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have ha : ∀ n i, Measurable (fun ω => a n ω i) := by
    intro n i
    exact hjoint.comp (measurable_const.prodMk measurable_id)
  refine ⟨K, s, (fun n => rfl), ?_, ?_⟩
  · intro n
    exact avram_bv_residual10_finite_coordinate_event_measurable
      n (a n) (ha n) (K n)
  · filter_upwards [hK] with ω hω
    filter_upwards [hω] with n hn
    simpa [s, a] using hn
