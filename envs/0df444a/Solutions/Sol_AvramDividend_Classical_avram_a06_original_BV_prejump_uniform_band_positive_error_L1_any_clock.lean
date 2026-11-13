-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:39:40.160018+00:00
-- url     : https://prove2.me/submissions/23508ba7-e150-46b7-8e8f-f52f39b5a6da

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → Ω → ℝ := fun k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
          ∈ Icc (a k) (b k) then (0 : ℝ)
        else |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|
    (∀ k, Integrable (fun ω => max (Err k ω) 0) P) ∧
    Tendsto (fun k => ∫ ω, max (Err k ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ))  := by
  let Z : Ω → ℕ → ℝ := fun ω i =>
    Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
  let H : Ω → ℝ := fun ω => |X.drift| * (T : ℝ) + |(T : ℝ) * X.drift - X.X T ω|
  let s : ℕ → Set Ω := fun k =>
    {ω | ∀ i < n + 1,
      (0 < Z ω i ∧ ENNReal.ofReal (Z ω i) < C) →
        Z ω i ∈ Icc (a k) (b k)}
  let Err : ℕ → Ω → ℝ := fun k ω =>
    if ω ∈ s k then (0 : ℝ) else H ω
  have hJoint :=
    avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
      X x D hD.1.1
  have hZ (i : ℕ) : Measurable (fun ω => Z ω i) :=
    hJoint.comp (measurable_const.prodMk measurable_id)
  have hs (k : ℕ) : MeasurableSet (s k) := by
    dsimp [s]
    measurability
  have hXt : Measurable (X.X T) := (X.adapted T).mono (𝓕.le T) le_rfl
  have hHm : Measurable H := measurable_const.add (measurable_const.sub hXt).abs
  have hBVsource := avram_p3_comp8_original_BV_source_mass_integrable_any_clock
    X hX hBV T
  have hHI : Integrable H P := hBVsource.1
  have hHnonneg (ω : Ω) : 0 ≤ H ω := hBVsource.2 ω
  have hErrMeas (k : ℕ) : AEStronglyMeasurable (Err k) P := by
    exact (Measurable.ite (hs k) measurable_const hHm).aestronglyMeasurable
  have hEventual (ω : Ω) : ∀ᶠ k : ℕ in atTop, ω ∈ s k := by
    obtain ⟨N, hN⟩ :=
      avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
        C a b hExh n (Z ω)
    apply (eventually_ge_atTop N).mono
    intro k hk i hi hzi
    exact hN k hk i hi hzi
  have hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun k => Err k ω) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with ω
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hEventual ω] with k hk
    simp [Err, hk]
  have hDom (k : ℕ) : ∀ᵐ ω ∂P, ‖Err k ω‖ ≤ H ω := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ s k
    · simp [Err, hω, hHnonneg ω]
    · simpa [Err, hω, Real.norm_eq_abs,
          abs_of_nonneg (hHnonneg ω)] using (le_refl (H ω))
  simpa only [Err, s, Set.mem_setOf_eq, Z, H] using
    (avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
      P Err hErrMeas hErrAE H hHI hDom)
