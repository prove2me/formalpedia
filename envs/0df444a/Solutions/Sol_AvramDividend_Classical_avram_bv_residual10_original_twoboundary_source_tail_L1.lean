-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_twoboundary_source_tail_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:21:20.073981+00:00
-- url     : https://prove2.me/submissions/5a241266-c95d-46c1-96e9-bf2eda421094

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_rowwise_ae_eventual_clipping
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_prejump_inverse_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_tail_L1_any_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- On original pre-jump rows, both finite-cap boundaries can be avoided
off negligible measurable events, with an L1-negligible BV source-mass tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (u : ℕ → ℕ → ℝ≥0)
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞)))
    (hεsum : (∑' n, ε n) ≠ ⊤)
    (T : ℝ≥0) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    let Z : ℕ → Ω → ℕ → ℝ := fun n ω i =>
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    ∃ N L U : ℕ → ℕ, ∃ s : ℕ → Set Ω,
      (∀ n, s n =
        ({ω | ∀ i ∈ Finset.range (n + 1), abs (Z n ω i) ≤ (N n : ℝ)} ∩
         {ω | ∀ i ∈ Finset.range (n + 1), abs ((Z n ω i)⁻¹) ≤ (L n : ℝ)}) ∩
        {ω | ∀ i ∈ Finset.range (n + 1),
          abs (((C.toReal : ℝ) - Z n ω i)⁻¹) ≤ (U n : ℝ)}) ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      (∀ n, Integrable (fun ω => if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) P) ∧
      Tendsto (fun n => ∫ ω, if ω ∈ s n then 0 else
        K₀ * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
        atTop (nhds (0 : ℝ)) := by
  dsimp only
  let Z : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  obtain ⟨N, L, s₀, hs₀_def, hs₀_meas, hs₀_eventual⟩ :=
    avram_bv_residual10_original_prejump_inverse_band_exhaustion
      (P := P) X x D hD u ε hεpos hεlim hεsum
  have hjoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD
  have hZ : ∀ n i, Measurable (fun ω => Z n ω i) := by
    intro n i
    exact hjoint.comp (measurable_const.prodMk measurable_id)
  let G : ℕ → Ω → ℕ → ℝ := fun n ω i =>
    ((C.toReal : ℝ) - Z n ω i)⁻¹
  have hG : ∀ n i, Measurable (fun ω => G n ω i) := by
    intro n i
    exact (measurable_const.sub (hZ n i)).inv
  obtain ⟨U, hU⟩ :=
    avram_bv_residual10_original_rowwise_ae_eventual_clipping
      (P := P) G hG ε hεpos hεlim hεsum
  let s : ℕ → Set Ω := fun n =>
    s₀ n ∩ {ω | ∀ i ∈ Finset.range (n + 1), abs (G n ω i) ≤ (U n : ℝ)}
  have hs_def (n : ℕ) : s n =
      ({ω | ∀ i ∈ Finset.range (n + 1), abs (Z n ω i) ≤ (N n : ℝ)} ∩
       {ω | ∀ i ∈ Finset.range (n + 1), abs ((Z n ω i)⁻¹) ≤ (L n : ℝ)}) ∩
      {ω | ∀ i ∈ Finset.range (n + 1),
        abs (((C.toReal : ℝ) - Z n ω i)⁻¹) ≤ (U n : ℝ)} := by
    change s₀ n ∩ {ω | ∀ i ∈ Finset.range (n + 1),
      abs (G n ω i) ≤ (U n : ℝ)} = _
    rw [hs₀_def n]
  have hs_meas (n : ℕ) : MeasurableSet (s n) :=
    (hs₀_meas n).inter
      (avram_bv_residual10_finite_coordinate_event_measurable
        n (G n) (hG n) (U n))
  have hs_eventual : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n := by
    filter_upwards [hs₀_eventual, hU] with ω hω₀ hωU
    filter_upwards [hω₀, hωU] with n hn₀ hnU
    exact ⟨hn₀, hnU⟩
  obtain ⟨h_int, h_lim⟩ :=
    avram_p3_comp8_original_BV_source_tail_L1_any_clock
      X hX hBV T K₀ hK₀ s hs_meas hs_eventual
  exact ⟨N, L, U, s, hs_def, hs_meas, hs_eventual, h_int, h_lim⟩
