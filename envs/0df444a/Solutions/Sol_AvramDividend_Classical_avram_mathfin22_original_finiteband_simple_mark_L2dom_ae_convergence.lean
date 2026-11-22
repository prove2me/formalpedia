-- Prove2me | solution 1 for AvramDividend.Classical.avram_mathfin22_original_finiteband_simple_mark_L2dom_ae_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T13:10:29.999731+00:00
-- url     : https://prove2.me/submissions/8d52501b-66ca-47ec-9c28-3782ba410407

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_bounded_simple_mark_integrals_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_negative_band_count_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
import Theorems.Thm_AvramDividend_Classical_avram_mixed_source13_original_physical_annulus_count_variance_exact
import Theorems.Thm_AvramDividend_Classical_avram_mathfin22_count_to_mark_L2_transfer
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (a b : ℕ) (hab : a ≤ b)
    (g : ℝ → ℝ) (f : ℕ → SimpleFunc ℝ ℝ)
    (hfBound : ∀ k z, z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))) →
      |f k z| ≤ 1)
    (hfLimit : ∀ z ∈
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1))),
      Tendsto (fun k => f k z) atTop (𝓝 (g z))) :
    let B : Set ℝ :=
      Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {s : ℝ≥0 |
        0 < s ∧ X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
        (fun s : ℝ≥0 => (s, X.X s ω -
          Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
    let F : ℕ → Ω → ℝ := fun k ω =>
      ∫ p in (Ioc 0 T ×ˢ B), f k p.2 ∂NX ω
    let J : Ω → ℝ := fun ω =>
      ∫ p in (Ioc 0 T ×ˢ B), g p.2 ∂NX ω
    let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
    Integrable N P ∧ Integrable (fun ω => (N ω)^2) P ∧
      (∀ᵐ ω ∂P, ∀ k, |F k ω| ≤ N ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (J ω)))  := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((a : ℝ) + 1))) (-(1 / ((b : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {s : ℝ≥0 |
      0 < s ∧ X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s ≠ 0}).map
      (fun s : ℝ≥0 => (s, X.X s ω -
        Function.leftLim (fun t : ℝ≥0 => X.X t ω) s)))
  let F : ℕ → Ω → ℝ := fun k ω =>
    ∫ p in (Ioc 0 T ×ˢ B), f k p.2 ∂NX ω
  let J : Ω → ℝ := fun ω =>
    ∫ p in (Ioc 0 T ×ˢ B), g p.2 ∂NX ω
  let N : Ω → ℝ := fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal
  change Integrable N P ∧ Integrable (fun ω => (N ω)^2) P ∧
    (∀ᵐ ω ∂P, ∀ k, |F k ω| ≤ N ω) ∧
    (∀ᵐ ω ∂P, Tendsto (fun k => F k ω) atTop (𝓝 (J ω)))
  have hNI : Integrable N P := by
    simpa [N, B, NX] using
      (avram_workerB_original_reciprocal_band_count_L1_Campbell_20261122
        X T a b).1
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hNcenter : Integrable (fun ω => (N ω - r)^2) P := by
    simpa [N, r, B, NX] using
      (avram_mixed_source13_original_physical_annulus_count_variance_exact
        X T a b hab).1
  have hN2 : Integrable (fun ω => (N ω)^2) P := by
    apply avram_mathfin22_count_to_mark_L2_transfer P N N r 0
      hNI hNI hNcenter
    apply Filter.Eventually.of_forall
    intro ω
    have hn : 0 ≤ N ω := ENNReal.toReal_nonneg
    simpa [abs_of_nonneg hn] using (le_refl (N ω))
  have hBm : MeasurableSet B := measurableSet_Ioc
  have hMass (ω : Ω) : NX ω (Ioc 0 T ×ˢ B) < ⊤ := by
    have hSub : (Ioc 0 T ×ˢ B) ⊆
        (Ioc 0 T ×ˢ Iic (-(1 / ((b : ℝ) + 1)))) := by
      exact Set.prod_mono (Subset.rfl) (fun z hz => hz.2)
    have hCount :=
      avram_wave7_06_original_separated_negative_band_count_finite_every_path
        X ω T b
    exact lt_of_le_of_lt (measure_mono hSub) (by simpa [NX] using hCount)
  have hBound : ∀ᵐ ω ∂P, ∀ k, |F k ω| ≤ N ω := by
    apply Filter.Eventually.of_forall
    intro ω k
    have h :=
      (avram_a20_original_bounded_mark_finite_cell_integral_norm_bound
        (NX ω) T B hBm (fun z => f k z)
        (f k).measurable (hMass ω)
        (fun z hz => hfBound k z hz)).2
    simpa [F, N] using h
  have hLimit : ∀ᵐ ω ∂P,
      Tendsto (fun k => F k ω) atTop (𝓝 (J ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    exact avram_a20_original_bounded_simple_mark_integrals_tendsto
      (NX ω) T B hBm (hMass ω) g f hfBound hfLimit
  exact ⟨hNI, hN2, hBound, hLimit⟩
