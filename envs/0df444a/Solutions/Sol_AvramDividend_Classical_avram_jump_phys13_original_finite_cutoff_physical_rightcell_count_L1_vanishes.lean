-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump_phys13_original_finite_cutoff_physical_rightcell_count_L1_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:07:17.457223+00:00
-- url     : https://prove2.me/submissions/a31dd9ce-c257-4caa-bbc7-0cca227df1ed

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cutoff_marked_count_L1_auto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual finite-negative-band source count in the clipped post-stop cell tends to zero in physical L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0) (e : ℕ → Ω → ℝ≥0)
    (hτ : Measurable τ) (he : ∀ k, Measurable (e k))
    (heBound : ∀ k ω, e k ω ≤ T)
    (heTendsto : ∀ ω, Tendsto (fun k => e k ω) atTop (𝓝 (τ ω))) :
    let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
    let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    Tendsto (fun k => ∫ ω,
      ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let B : Set ℝ := Iic (-(1 / ((cut : ℝ) + 1)))
  let J : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let Δ (ω : Ω) (u : ℝ≥0) :=
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let U (ω : Ω) (s t : ℝ≥0) : Set ℝ≥0 :=
    {u | 0 < u ∧ s < u ∧ u ≤ t ∧ Δ ω u ≠ 0 ∧ Δ ω u ∈ B}
  have hCount (ω : Ω) (s t : ℝ≥0) :
      J ω (Ioc s t ×ˢ B) = (U ω s t).encard := by
    simpa [J, U, Δ] using
      avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
        X ω s t B measurableSet_Iic
  let F : ℕ → Ω → ℝ :=
    fun k ω => ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal
  let K : Ω → ℝ :=
    fun ω => ((J ω) (Ioc 0 T ×ˢ B)).toReal
  have hFullFinite (ω : Ω) :
      J ω (Ioc 0 T ×ˢ B) < ⊤ := by
    rw [hCount ω 0 T]
    have hFin := avram_wave7_06_original_negative_band_marked_times_finite
      X ω T cut
    have hU : (U ω 0 T).Finite := by
      apply hFin.subset
      intro u hu
      rcases hu with ⟨_, hu0, huT, _, huB⟩
      exact ⟨hu0, huT, by simpa [B, Δ] using huB⟩
    exact ENat.toENNReal_lt_top.mpr hU.encard_lt_top
  have hFvanish : ∀ k ω,
      {u : ℝ≥0 | τ ω < u ∧ u ≤ e k ω ∧ Δ ω u ≤
        -(1 / ((cut : ℝ) + 1))} = ∅ → F k ω = 0 := by
    intro k ω hVoid
    have hEmpty : U ω (τ ω) (e k ω) = ∅ := by
      ext u
      constructor
      · intro hu
        rcases hu with ⟨_, hτu, hue, _, hB⟩
        have hMem : u ∈ {u : ℝ≥0 | τ ω < u ∧ u ≤ e k ω ∧
          Δ ω u ≤ -(1 / ((cut : ℝ) + 1))} :=
          ⟨hτu, hue, by simpa [B] using hB⟩
        rw [hVoid] at hMem
        exact hMem
      · intro hu
        simp at hu
    change ((J ω) (Ioc (τ ω) (e k ω) ×ˢ B)).toReal = 0
    rw [hCount ω (τ ω) (e k ω), hEmpty]
    simp
  have hFmeas : ∀ k, AEStronglyMeasurable (fun ω => |F k ω|) P := by
    intro k
    have hm :=
      avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
        X cut τ (e k) hτ (he k)
    have hmJ : Measurable (fun ω =>
        J ω (Ioc (τ ω) (e k ω) ×ˢ B)) := by
      simpa [J, B] using hm
    have hReal : Measurable (F k) := by
      change Measurable (fun ω =>
        (J ω (Ioc (τ ω) (e k ω) ×ˢ B)).toReal)
      exact ENNReal.measurable_toReal.comp hmJ
    exact hReal.abs.aestronglyMeasurable
  have hKI : Integrable K P := by
    simpa [K, J, B] using
      avram_p4_f_assembly_original_cutoff_marked_count_L1_auto X T cut
  have hDom : ∀ k, ∀ᵐ ω ∂P, |F k ω| ≤ K ω := by
    intro k
    apply Filter.Eventually.of_forall
    intro ω
    have hSubset : Ioc (τ ω) (e k ω) ×ˢ B ⊆ Ioc 0 T ×ˢ B := by
      rintro ⟨u, z⟩ ⟨hu, hz⟩
      have h0 : (0 : ℝ≥0) ≤ τ ω := zero_le
      exact ⟨⟨lt_of_le_of_lt h0 hu.1,
        le_trans hu.2 (heBound k ω)⟩, hz⟩
    have hMono : J ω (Ioc (τ ω) (e k ω) ×ˢ B) ≤
        J ω (Ioc 0 T ×ˢ B) := measure_mono hSubset
    have hReal := ENNReal.toReal_mono
      (ne_of_lt (hFullFinite ω)) hMono
    simpa [F, K, abs_of_nonneg ENNReal.toReal_nonneg] using hReal
  simpa only [F, B, J, abs_of_nonneg ENNReal.toReal_nonneg] using
    avram_jump_phys13_original_finite_band_rightcell_L1_of_domination
      X T cut τ e heBound heTendsto F (by
        intro k ω
        exact hFvanish k ω) hFmeas K hKI hDom
