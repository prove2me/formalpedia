-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja28_original_bounded_mark_raw_first_second_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:49:22.707234+00:00
-- url     : https://prove2.me/submissions/c6e91496-a814-45e6-91d9-be5c6300b8d3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_original_Borel_mark_simple_quantization
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_simple_integral_L2_domination_convergence
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_simple_mark_raw_moments_intensity
import Theorems.Thm_AvramDividend_Classical_avram_a20_bounded_Borel_mark_first_second_integral_limits
import Theorems.Thm_AvramDividend_Classical_avram_a20_dominated_real_simple_mark_two_moment_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (g : ℝ → ℝ),
      Measurable g →
      (∀ z ∈ Ioc (-(1 / ((n : ℝ) + 1)))
        (-(1 / ((m : ℝ) + 1))), |g z| ≤ 1) →
      ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let J : Ω → ℝ := fun ω =>
        ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
      let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
      let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
      Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
        (∫ ω, J ω ∂P) = r ∧
        (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q := by
  classical
  intro n m hnm g hg hgBound t
  let S : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let J : Ω → ℝ := fun ω => ∫ p in (Ioc 0 t ×ˢ S), g p.2 ∂NX ω
  let r : ℝ := (t : ℝ) * (∫ z in S, g z ∂X.ν)
  let q : ℝ := (t : ℝ) * (∫ z in S, (g z) ^ 2 ∂X.ν)
  change Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
    (∫ ω, J ω ∂P) = r ∧
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + q
  have hS : MeasurableSet S := measurableSet_Ioc
  have hNeg : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    have hp : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    change z < 0
    exact lt_of_le_of_lt hz.2 (by linarith)
  have hMass : X.ν S < ⊤ :=
    lt_of_le_of_lt (measure_mono hNeg) (lt_top_iff_ne_top.mpr hFinite)
  have hGBound : ∀ z ∈ S, ‖g z‖ ≤ (1 : ℝ) := by
    intro z hz; simpa only [Real.norm_eq_abs] using hgBound z hz
  obtain ⟨f, hfGlobal, hfLimit⟩ :=
    avram_a20_bounded_original_Borel_mark_simple_quantization g S hg hS hGBound
  have hfBound : ∀ k z, z ∈ S → |f k z| ≤ 1 := by
    intro k z hz; simpa only [Real.norm_eq_abs] using hfGlobal k z
  let F : ℕ → Ω → ℝ := fun k ω => ∫ p in (Ioc 0 t ×ˢ S), f k p.2 ∂NX ω
  let B : Ω → ℝ := fun ω => (NX ω (Ioc 0 t ×ˢ S)).toReal
  let rate : ℕ → ℝ := fun k => (t : ℝ) * (∫ z in S, f k z ∂X.ν)
  let moment : ℕ → ℝ := fun k => (rate k) ^ 2 +
    (t : ℝ) * (∫ z in S, (f k z) ^ 2 ∂X.ν)
  have hDCT := avram_a21_original_bounded_simple_integral_L2_domination_convergence
    X hFinite t S hS hNeg g f hfBound hfLimit
  change Integrable B P ∧ Integrable (fun ω => (B ω) ^ 2) P ∧
    (∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω) ∧
    (∀ᵐ ω ∂P, Tendsto (fun k => F k ω)
      atTop (𝓝 (J ω))) at hDCT
  have hInts := avram_a20_bounded_Borel_mark_first_second_integral_limits
    (X.ν) S hS hMass g f hfBound hfLimit
  have hRate : Tendsto rate atTop (𝓝 r) := by
    simpa only [rate, r] using (tendsto_const_nhds.mul hInts.1)
  have hQ : Tendsto (fun k => (t : ℝ) *
      (∫ z in S, (f k z) ^ 2 ∂X.ν)) atTop (𝓝 q) := by
    simpa only [q] using (tendsto_const_nhds.mul hInts.2)
  have hMoment : Tendsto moment atTop (𝓝 (r ^ 2 + q)) := by
    simpa only [moment] using (hRate.pow 2).add hQ
  have hMom : ∀ k, Integrable (F k) P ∧
      Integrable (fun ω => (F k ω) ^ 2) P ∧
      (∫ ω, F k ω ∂P) = rate k ∧ (∫ ω, (F k ω) ^ 2 ∂P) = moment k := by
    intro k
    have h := avram_a21_original_simple_mark_raw_moments_intensity
      X hFinite t S hS hNeg (f k) (hfBound k)
    change Integrable (F k) P ∧ Integrable (fun ω => (F k ω) ^ 2) P ∧
      (∫ ω, F k ω ∂P) = rate k ∧ (∫ ω, (F k ω) ^ 2 ∂P) = moment k at h
    exact h
  have hFMeas : ∀ k, AEStronglyMeasurable (F k) P := fun k =>
    (hMom k).1.aestronglyMeasurable
  exact avram_a20_dominated_real_simple_mark_two_moment_limit
    F J B rate moment r (r ^ 2 + q)
    hFMeas hDCT.1 hDCT.2.1 hDCT.2.2.1
    hDCT.2.2.2 (fun k => (hMom k).2.2.1)
    (fun k => (hMom k).2.2.2)
    hRate hMoment
