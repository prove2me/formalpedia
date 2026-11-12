-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:19:31.248711+00:00
-- url     : https://prove2.me/submissions/70c8ed2b-3161-4aa7-be91-243871f68764

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja29_original_negative_borel_cell_centred_L2_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine finite Borel mark-simple compensated source sum has an
integrable square, independently of any same-window exact covariance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (cut : ℕ)
    (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hSep : ∀ i ∈ Finset.range K,
      B i ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal))
    Integrable (fun ω => (F ω) ^ 2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let F : Ω → ℝ := fun ω =>
    ∑ i ∈ Finset.range K,
      c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
        (((t : ℝ≥0∞) * X.ν (B i)).toReal))
  change Integrable (fun ω => (F ω) ^ 2) P
  have hTerms : ∀ i ∈ Finset.range K,
      MemLp (fun ω : Ω =>
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal))) 2 P := by
    intro i hi
    have hMeas : Measurable (fun ω : Ω =>
        (NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal)) := by
      have hc := avram_ja31_original_borel_mark_count_filtration_measurable
        X t (B i) (hB i hi)
      exact ((ENNReal.measurable_toReal.comp hc).sub_const _).mono
        (𝓕.le t) le_rfl
    have hSq : Integrable (fun ω : Ω =>
        ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal)) ^ 2) P := by
      simpa only [NX] using
        (avram_ja29_original_negative_borel_cell_centred_L2_integrable
          X t cut (B i) (hB i hi) (hSep i hi)).2.2
    have hiL2 : MemLp (fun ω : Ω =>
        (NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal)) 2 P :=
      (memLp_two_iff_integrable_sq hMeas.aestronglyMeasurable).2 hSq
    exact hiL2.const_mul (c i)
  have hAll : MemLp F 2 P := by
    simpa only [F] using (memLp_finset_sum (Finset.range K) hTerms)
  exact (memLp_two_iff_integrable_sq hAll.aestronglyMeasurable).1 hAll
