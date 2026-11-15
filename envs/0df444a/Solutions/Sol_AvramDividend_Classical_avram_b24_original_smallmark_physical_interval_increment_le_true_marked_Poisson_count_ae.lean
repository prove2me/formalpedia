-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_smallmark_physical_interval_increment_le_true_marked_Poisson_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T18:46:59.116972+00:00
-- url     : https://prove2.me/submissions/a7d1ebc1-f768-4508-9ba8-0e051261dd81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_window_finite_marked_times_card
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
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t → t ≤ T →
      ‖Jsmall t ω - Jsmall s ω‖ ≤
      (((Measure.count.restrict {u : ℝ≥0 |
         0 < u ∧ X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
         (fun u : ℝ≥0 => (u, X.X u ω -
           Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
         (Ioc s t ×ˢ Ioo (-1 : ℝ) 0)).toReal +
      ((t : ℝ) - (s : ℝ)) *
        ‖∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν‖ := by
  have hVariation :=
    AvramDividend.Classical.avram_b24_original_finiteactivity_smallmark_increment_true_interval_count_variation_ae
      X hFinite Jsmall hJsource T
  filter_upwards [hVariation] with ω hω
  obtain ⟨S, hS, hBound⟩ := hω
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
  let E : Set ℝ≥0 := {u : ℝ≥0 |
    0 < u ∧ u ≤ T ∧ z u ≠ 0 ∧ z u ∈ Ioo (-1 : ℝ) 0}
  have hE : E = (Sm : Set ℝ≥0) := by
    ext u
    constructor
    · intro hu
      exact (hSm u).2 ⟨hu.1, hu.2.1, hu.2.2.2⟩
    · intro hu
      obtain ⟨hp, hlt, hz⟩ := (hSm u).1 hu
      exact ⟨hp, hlt, ne_of_lt hz.2, hz⟩
  have hFinite : E.Finite := by
    rw [hE]
    exact Sm.finite_toSet
  intro s t hst htT
  have hCount :=
    AvramDividend.Classical.avram_a20_original_borel_window_finite_marked_times_card
      X ω T (Ioo (-1 : ℝ) 0) measurableSet_Ioo s t hst htT hFinite
  have hFin : hFinite.toFinset = Sm := by
    ext u
    simp only [Set.Finite.mem_toFinset, hE, Finset.mem_coe]
  rw [hFin] at hCount
  have hFilter :
      Sm.filter (fun u => s < u ∧ u ≤ t) =
        S.filter (fun u => s < u ∧ u ≤ t ∧ -1 < z u ∧ z u < 0) := by
    ext u
    simp only [Sm, Finset.mem_filter]
    tauto
  rw [hFilter] at hCount
  have hReal := congrArg ENNReal.toReal hCount
  have hBound' := hBound s t hst htT
  change ‖Jsmall t ω - Jsmall s ω‖ ≤
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ z u ≠ 0}).map (fun u => (u, z u)))
        (Ioc s t ×ˢ Ioo (-1 : ℝ) 0)).toReal +
      ((t : ℝ) - (s : ℝ)) *
        ‖∫ u in Ioo (-1 : ℝ) 0, u ∂X.ν‖
  rw [hReal]
  simpa [z] using hBound'
