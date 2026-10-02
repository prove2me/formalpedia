-- Prove2me | solution 1 for DualSSD.Duality.secondPerformance_eq_expectedShortfall
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:55:40.012366+00:00
-- url     : https://prove2.me/submissions/a0d02ca8-ab7f-41ca-8dde-8befaf8f458e

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

set_option autoImplicit false

open MeasureTheory in
theorem dssd_shift (c : ℝ) (f : ℝ → ℝ) (S : Set ℝ) :
    ∫ u in S, f u = ∫ t in (fun t : ℝ => t + c) ⁻¹' S, f (t + c) := by
  have A : MeasurableEmbedding (fun t : ℝ => t + c) :=
    (Homeomorph.addRight c).isClosedEmbedding.measurableEmbedding
  have h := A.setIntegral_map (μ := volume) f S
  rw [map_add_right_eq_self] at h
  exact h

open MeasureTheory Filter in
/-- Layer cake: the second performance function is the expected shortfall `E (η - X)⁺`. -/
theorem dssd_perf_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Integrable X μ) (x : ℝ) :
    DualSSD.Shared.secondPerformance μ X x = ∫ ω, max (x - X ω) 0 ∂μ := by
  have hi : Integrable (fun ω => max (x - X ω) 0) μ := ((integrable_const x).sub hX).pos_part
  rw [DualSSD.Shared.secondPerformance,
    hi.integral_eq_integral_meas_le (Eventually.of_forall fun ω => le_max_right _ _),
    dssd_shift x (DualSSD.Shared.distFun μ X) (Set.Iic x), Set.preimage_add_const_Iic, sub_self]
  have h2 := integral_comp_neg_Ioi (0 : ℝ) (fun s => DualSSD.Shared.distFun μ X (s + x))
  rw [neg_zero] at h2
  rw [← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [DualSSD.Shared.distFun, measureReal_def]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, le_max_iff]
  have ht' : 0 < t := ht
  constructor
  · intro h; left; linarith
  · rintro (h | h)
    · linarith
    · linarith


open MeasureTheory in
theorem dssd_map_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X P) (η : ℝ) :
    ∫ ξ in Set.Iic η, (η - ξ) ∂(P.map X) = ∫ ω, max (η - X ω) 0 ∂P := by
  rw [← integral_indicator measurableSet_Iic]
  have hf : (Set.Iic η).indicator (fun ξ : ℝ => η - ξ) = fun ξ => max (η - ξ) 0 := by
    funext ξ
    by_cases h : ξ ≤ η
    · rw [Set.indicator_of_mem (show ξ ∈ Set.Iic η from h)]
      exact (max_eq_left (by linarith)).symm
    · rw [Set.indicator_of_notMem (show ξ ∉ Set.Iic η from h)]
      exact (max_eq_right (by linarith [not_le.mp h])).symm
  rw [hf, integral_map hX]
  exact (Continuous.aestronglyMeasurable (by fun_prop))

open MeasureTheory DualSSD in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) (η : ℝ) :
    Shared.secondPerformance P X η = ∫ ξ in Set.Iic η, (η - ξ) ∂(P.map X) ∧
      Shared.secondPerformance P X η = ∫ ω, max (η - X ω) 0 ∂P := by
  have h2 := dssd_perf_eq P X hX η
  exact ⟨h2.trans (dssd_map_eq P X hX.aemeasurable η).symm, h2⟩
