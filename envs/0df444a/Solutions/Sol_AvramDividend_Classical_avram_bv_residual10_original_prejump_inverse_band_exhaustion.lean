-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_prejump_inverse_band_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:56:39.62702+00:00
-- url     : https://prove2.me/submissions/67c3a0ff-6044-41c3-9543-5a6a7c57e394

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original pre-jump physical rows can be clipped both in magnitude and
away from the singular zero boundary wherever the reserve is nonzero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤) :
    ∃ N L : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n =
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs (Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i)) ≤ (N n : ℝ)} ∩
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs ((Function.leftLim
            (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
            (u n i))⁻¹) ≤ (L n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) := by
  let Z : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  have hjoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have hZ : ∀ n i, Measurable (fun ω => Z n ω i) := by
    intro n i
    exact hjoint.comp (measurable_const.prodMk measurable_id)
  let Zinv : ℕ → Ω → ℕ → ℝ := fun n ω i => (Z n ω i)⁻¹
  have hZinv : ∀ n i, Measurable (fun ω => Zinv n ω i) := by
    intro n i
    exact (hZ n i).inv
  obtain ⟨N, hN⟩ :=
    avram_bv_residual10_original_rowwise_ae_eventual_clipping
      (P := P) Z hZ ε hεpos hεlim hεsum
  obtain ⟨L, hL⟩ :=
    avram_bv_residual10_original_rowwise_ae_eventual_clipping
      (P := P) Zinv hZinv ε hεpos hεlim hεsum
  let s : ℕ → Set Ω := fun n =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (Z n ω i) ≤ (N n : ℝ)} ∩
    {ω | ∀ i ∈ Finset.range (n + 1), abs (Zinv n ω i) ≤ (L n : ℝ)}
  refine ⟨N, L, s, (fun n => rfl), ?_, ?_⟩
  · intro n
    exact (avram_bv_residual10_finite_coordinate_event_measurable
      n (Z n) (hZ n) (N n)).inter
      (avram_bv_residual10_finite_coordinate_event_measurable
        n (Zinv n) (hZinv n) (L n))
  · filter_upwards [hN, hL] with ω hNω hLω
    filter_upwards [hNω, hLω] with n hNn hLn
    exact ⟨hNn, hLn⟩
