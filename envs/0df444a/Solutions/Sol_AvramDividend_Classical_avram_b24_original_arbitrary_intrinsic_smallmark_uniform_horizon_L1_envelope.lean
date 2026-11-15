-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_arbitrary_intrinsic_smallmark_uniform_horizon_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:31:22.301341+00:00
-- url     : https://prove2.me/submissions/dd216800-1e9f-4b03-9c89-17f7f05b5e9b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
import Theorems.Thm_AvramDividend_Classical_avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)
        atTop (𝓝 (Jsmall t ω)))
    (T : ℝ≥0) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
    let B : Ω → ℝ := fun ω => (N ω).toReal +
      (T : ℝ) * ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖
    Integrable B P ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
        ‖Jsmall t ω‖ ≤ B ω := by
  letI : IsProbabilityMeasure P := X.isProbability
  let d : ℝ := ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Ioo (-1 : ℝ) 0)
  let B : Ω → ℝ := fun ω => (N ω).toReal + (T : ℝ) * ‖d‖
  change Integrable B P ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T → ‖Jsmall t ω‖ ≤ B ω
  have hBand : Ioo (-1 : ℝ) 0 ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hz.2
  have hCountI : Integrable (fun ω => (N ω).toReal) P :=
    (AvramDividend.Classical.avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T (Ioo (-1 : ℝ) 0) measurableSet_Ioo hBand).1
  have hBI : Integrable B P :=
    hCountI.add (integrable_const ((T : ℝ) * ‖d‖))
  have hHorizon :=
    AvramDividend.Classical.avram_b24_original_compensated_smallmark_single_finite_horizon_path_representation_ae
      X hFinite Jsmall hJsource
  refine ⟨hBI, ?_⟩
  filter_upwards [hHorizon] with ω hω
  obtain ⟨S, hS, hPath⟩ := hω T
  let z : ℝ≥0 → ℝ := fun u =>
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let Sm : Finset ℝ≥0 := S.filter (fun u => -1 < z u ∧ z u < 0)
  have hSm (u : ℝ≥0) :
      u ∈ Sm ↔ 0 < u ∧ u ≤ T ∧ z u ∈ Ioo (-1 : ℝ) 0 := by
    simp only [Sm, Finset.mem_filter]
    constructor
    · intro hu
      have hs := (hS u).1 hu.1
      exact ⟨hs.1, hs.2.1, hu.2⟩
    · intro hu
      have hne : z u ≠ 0 := ne_of_lt hu.2.2.2
      exact ⟨(hS u).2 ⟨hu.1, hu.2.1, hne⟩, hu.2.2⟩
  have hCountEq : N ω = (Sm.card : ℝ≥0∞) :=
    AvramDividend.Classical.avram_b24_original_smallnegative_physical_mark_count_exact_finite_support_card
      X ω T Sm hSm
  have hNReal : (N ω).toReal = (Sm.card : ℝ) := by
    rw [hCountEq]
    simp
  intro t ht
  have hF : Jsmall t ω =
      (∑ i ∈ S, if decide (i ≤ t) then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0) -
      (t : ℝ) * d := by
    simpa [z, d] using hPath t ht
  have hBound :=
    AvramDividend.Classical.avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
      S z (fun u => decide (u ≤ t)) T t ht d
  change ‖Jsmall t ω‖ ≤ (N ω).toReal + (T : ℝ) * ‖d‖
  rw [hF, hNReal]
  exact hBound
