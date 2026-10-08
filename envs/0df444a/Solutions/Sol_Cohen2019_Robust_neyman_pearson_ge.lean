-- Prove2me | solution 1 for Cohen2019.Robust.neyman_pearson_ge
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:49:11.933972+00:00
-- url     : https://prove2.me/submissions/bb10ffc5-3c9e-4f8d-94ec-3eb5af7dee23

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem np_aux_dad4344a {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (μX μY : α → ENNReal)
    (hμX : Measurable μX) (hμY : Measurable μY)
    (hμX1 : ∫⁻ z, μX z ∂ν = 1) (hμY1 : ∫⁻ z, μY z ∂ν = 1)
    (h : α → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (t : ℝ) (ht : 0 < t)
    (hX : ∫ z, h z ∂(ν.withDensity μX)
      ≤ (ν.withDensity μX {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal) :
    ∫ z, h z ∂(ν.withDensity μY)
      ≤ (ν.withDensity μY {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal := by
  set S := {z | ENNReal.ofReal t * μX z ≤ μY z} with hS
  have hSm : MeasurableSet S := measurableSet_le (measurable_const.mul hμX) hμY
  have : IsFiniteMeasure (ν.withDensity μX) := isFiniteMeasure_withDensity (by rw [hμX1]; simp)
  have : IsFiniteMeasure (ν.withDensity μY) := isFiniteMeasure_withDensity (by rw [hμY1]; simp)
  have hXf : ∀ᵐ z ∂ν, μX z < ⊤ := ae_lt_top hμX (by rw [hμX1]; simp)
  have hYf : ∀ᵐ z ∂ν, μY z < ⊤ := ae_lt_top hμY (by rw [hμY1]; simp)
  set f : α → ℝ := fun z => h z - S.indicator 1 z with hf
  have hfm : Measurable f := hh.sub (measurable_const.indicator hSm)
  have hfb : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    simp only [hf, Set.indicator, Pi.one_apply]
    obtain ⟨h0, h1⟩ := hh01 z
    split_ifs <;> rw [Real.norm_eq_abs, abs_le] <;> constructor <;> linarith
  have hfi : ∀ (P : Measure α) [IsFiniteMeasure P], Integrable f P := fun P _ =>
    Integrable.of_bound hfm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hfb)
  have hhi : ∀ (P : Measure α) [IsFiniteMeasure P], Integrable h P := fun P _ =>
    Integrable.of_bound hh.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hh01 z])
  have key : ∀ (P : Measure α) [IsFiniteMeasure P],
      ∫ z, f z ∂P = ∫ z, h z ∂P - (P S).toReal := by
    intro P _
    simp only [hf]
    have hi : Integrable (S.indicator (1 : α → ℝ)) P := (integrable_const (1:ℝ)).indicator hSm
    rw [integral_sub (hhi P) hi, integral_indicator_one hSm, measureReal_def]
  have eY := integral_withDensity_eq_integral_toReal_smul hμY hYf f
  have eX := integral_withDensity_eq_integral_toReal_smul hμX hXf f
  have iY := (integrable_withDensity_iff_integrable_smul' hμY hYf).1 (hfi (ν.withDensity μY))
  have iX := (integrable_withDensity_iff_integrable_smul' hμX hXf).1 (hfi (ν.withDensity μX))
  have pw : ∀ᵐ z ∂ν, (μY z).toReal • f z ≤ t * ((μX z).toReal • f z) := by
    filter_upwards [hXf, hYf] with z hx hy
    simp only [smul_eq_mul, ← mul_assoc]
    by_cases hz : z ∈ S
    · have hle : t * (μX z).toReal ≤ (μY z).toReal := by
        have := ENNReal.toReal_mono hy.ne hz
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le] at this
      have hf0 : f z ≤ 0 := by
        simp only [hf, Set.indicator_of_mem hz, Pi.one_apply]; linarith [hh01 z]
      exact mul_le_mul_of_nonpos_right hle hf0
    · have hlt : (μY z).toReal ≤ t * (μX z).toReal := by
        have hz' : μY z < ENNReal.ofReal t * μX z := lt_of_not_ge hz
        have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne) hz'.le
        rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le] at this
      have hf0 : 0 ≤ f z := by
        simp only [hf, Set.indicator_of_notMem hz]; simp [(hh01 z).1]
      exact mul_le_mul_of_nonneg_right hlt hf0
  have ineq : ∫ z, f z ∂(ν.withDensity μY) ≤ t * ∫ z, f z ∂(ν.withDensity μX) := by
    rw [eY, eX, ← integral_const_mul]
    exact integral_mono_ae iY (iX.const_mul t) pw
  rw [key, key] at ineq
  have : t * (∫ z, h z ∂(ν.withDensity μX) - (ν.withDensity μX S).toReal) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht.le (by linarith)
  linarith

open MeasureTheory ProbabilityTheory in
theorem solution {d : ℕ} (μX μY : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hμX : Measurable μX) (hμY : Measurable μY)
    (hμX1 : ∫⁻ z, μX z = 1) (hμY1 : ∫⁻ z, μY z = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (t : ℝ) (ht : 0 < t)
    (hX : ∫ z, h z ∂(volume.withDensity μX)
      ≤ (volume.withDensity μX {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal) :
    ∫ z, h z ∂(volume.withDensity μY)
      ≤ (volume.withDensity μY {z | ENNReal.ofReal t * μX z ≤ μY z}).toReal := by
  exact np_aux_dad4344a volume μX μY hμX hμY hμX1 hμY1 h hh hh01 t ht hX
