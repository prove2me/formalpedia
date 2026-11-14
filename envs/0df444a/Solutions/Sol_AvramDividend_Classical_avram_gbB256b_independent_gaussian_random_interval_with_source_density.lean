-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB256b_independent_gaussian_random_interval_with_source_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:52:59.801234+00:00
-- url     : https://prove2.me/submissions/849ab3dd-e70a-4222-8985-4edbc827c457

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB253_gaussian_pdf_uniform_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

private theorem gaussian_event_bound_local
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v) (s : Set ℝ) :
    ProbabilityTheory.gaussianReal mu v s ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) * volume s := by
  rw [ProbabilityTheory.gaussianReal_apply mu (ne_of_gt hv) s]
  calc
    _ ≤ ∫⁻ y in s, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) ∂volume := by
      apply lintegral_mono
      intro y
      change ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal mu v y) ≤ _
      exact ENNReal.ofReal_le_ofReal
        (AvramDividend.Classical.avram_gbB253_gaussian_pdf_uniform_envelope mu v hv y)
    _ = _ := by
      exact setLIntegral_const s (ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹))


private theorem gaussian_small_interval_local
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v) (a epsilon : ℝ) (hEps : 0 ≤ epsilon) :
    ProbabilityTheory.gaussianReal mu v (Set.Icc a (a + epsilon)) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) * ENNReal.ofReal epsilon := by
  have h := gaussian_event_bound_local mu v hv (Set.Icc a (a + epsilon))
  simpa only [Real.volume_Icc, add_sub_cancel_left] using h


theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C Z : Ω → ℝ) (hC : Measurable C) (hZ : Measurable Z)
    (mu : ℝ) (v : ℝ≥0) (hv : 0 < v)
    (hLaw : Measure.map Z P = gaussianReal mu v)
    (hInd : IndepFun C Z P)
    (epsilon : ℝ) (hEps : 0 ≤ epsilon) :
    P {ω | C ω ≤ Z ω ∧ Z ω ≤ C ω + epsilon} ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
        ENNReal.ofReal epsilon := by
  let S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2 ∧ p.2 ≤ p.1 + epsilon}
  have hS : MeasurableSet S := by
    exact (measurableSet_le measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.add_const epsilon))
  have hMap : P {ω | C ω ≤ Z ω ∧ Z ω ≤ C ω + epsilon} =
      ((Measure.map C P).prod (gaussianReal mu v)) S := by
    calc
      P {ω | C ω ≤ Z ω ∧ Z ω ≤ C ω + epsilon} =
          (Measure.map (fun ω => (C ω, Z ω)) P) S := by
            rw [Measure.map_apply (hC.prodMk hZ) hS]
            rfl
      _ = _ := by
        rw [IndepFun.map_prod_eq_prod_map_map hC.aemeasurable hZ.aemeasurable hInd, hLaw]
  rw [hMap, Measure.prod_apply hS]
  calc
    (∫⁻ c, (gaussianReal mu v) (Prod.mk c ⁻¹' S) ∂(Measure.map C P)) ≤
        ∫⁻ c, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
          ENNReal.ofReal epsilon ∂(Measure.map C P) := by
      apply lintegral_mono
      intro c
      have heq : (Prod.mk c ⁻¹' S) = Set.Icc c (c + epsilon) := by
        ext z
        simp only [S, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
      change (gaussianReal mu v) (Prod.mk c ⁻¹' S) ≤
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹) *
          ENNReal.ofReal epsilon
      rw [heq]
      exact gaussian_small_interval_local mu v hv c epsilon hEps
    _ = _ := by
      rw [lintegral_const]
      simp [Measure.map_apply hC MeasurableSet.univ]
