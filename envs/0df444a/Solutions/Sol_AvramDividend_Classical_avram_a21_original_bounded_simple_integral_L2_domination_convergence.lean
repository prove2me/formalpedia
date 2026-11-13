-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_bounded_simple_integral_L2_domination_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:44:23.648671+00:00
-- url     : https://prove2.me/submissions/48e0644c-658e-433f-8870-9fa2d50f19e8

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_real_count_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_integral_ae_count_domination
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ) (hS : MeasurableSet S)
    (hNeg : S ⊆ Iio (0 : ℝ))
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈ S → |f k z| ≤ 1)
    (hfLimit : ∀ z ∈ S,
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
    let B : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ S)).toReal
    Integrable B P ∧ Integrable (fun ω => (B ω) ^ 2) P ∧
      (∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω)
        atTop (𝓝 (J ω))) := by
  classical
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let F : ℕ → Ω → ℝ := fun k ω =>
    ∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω
  let J : Ω → ℝ := fun ω =>
    ∫ p in (Ioc 0 T ×ˢ S), g p.2 ∂NX ω
  let B : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ S)).toReal
  change Integrable B P ∧
    Integrable (fun ω => (B ω) ^ 2) P ∧
    (∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω) ∧
    (∀ᵐ ω ∂P, Tendsto (fun k => F k ω)
      atTop (𝓝 (J ω)))
  have hB : Integrable B P := by
    exact (avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T S hS hNeg).1
  have hBsq : Integrable (fun ω => (B ω) ^ 2) P :=
    avram_a20_original_negative_borel_real_count_square_integrable
      X hFinite T S hS hNeg
  have hBound : ∀ᵐ ω ∂P, ∀ k, ‖F k ω‖ ≤ B ω := by
    apply ae_all_iff.mpr
    intro k
    have hk :=
      avram_a20_original_bounded_mark_integral_ae_count_domination
        X hFinite T S hS hNeg (fun z => f k z)
        (f k).measurable (hfBound k)
    filter_upwards [hk] with ω hω
    simpa only [F, B, Real.norm_eq_abs] using hω.2
  have hLim : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (J ω)) := by
    have hFin :=
      avram_ubv_mixed12_original_finite_activity_negative_counts_all_bounded_ae
        X hFinite
    filter_upwards [hFin] with ω hω
    have hSub : (Ioc 0 T ×ˢ S) ⊆
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) :=
      Set.prod_mono (Subset.rfl) hNeg
    have hMass : NX ω (Ioc 0 T ×ˢ S) < ⊤ :=
      lt_of_le_of_lt (measure_mono hSub) (hω T)
    exact avram_a20_original_bounded_simple_mark_integrals_tendsto
      (NX ω) T S hS hMass g f hfBound hfLimit
  exact ⟨hB, hBsq, hBound, hLim⟩
