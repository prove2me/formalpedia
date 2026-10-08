-- Prove2me | solution 1 for Cohen2019.Robust.neyman_pearson_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:25:21.602883+00:00
-- url     : https://prove2.me/submissions/b544d744-6cb2-4409-a46c-53b5d3c6d3a0

import Mathlib

open MeasureTheory ProbabilityTheory in
theorem solution {d : ℕ} (μX μY : EuclideanSpace ℝ (Fin d) → ENNReal)
    (hμX : Measurable μX) (hμY : Measurable μY)
    (hμX1 : ∫⁻ z, μX z = 1) (hμY1 : ∫⁻ z, μY z = 1)
    (h : EuclideanSpace ℝ (Fin d) → ℝ) (hh : Measurable h) (hh01 : ∀ z, 0 ≤ h z ∧ h z ≤ 1)
    (t : ℝ) (ht : 0 < t)
    (hX : (volume.withDensity μX {z | μY z ≤ ENNReal.ofReal t * μX z}).toReal
      ≤ ∫ z, h z ∂(volume.withDensity μX)) :
    (volume.withDensity μY {z | μY z ≤ ENNReal.ofReal t * μX z}).toReal
      ≤ ∫ z, h z ∂(volume.withDensity μY) := by
  set S := {z | μY z ≤ ENNReal.ofReal t * μX z} with hSdef
  have hS : MeasurableSet S := measurableSet_le hμY (hμX.const_mul _)
  have hXfin : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), μX z < ⊤ :=
    ae_lt_top hμX (by rw [hμX1]; exact ENNReal.one_ne_top)
  have hYfin : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), μY z < ⊤ :=
    ae_lt_top hμY (by rw [hμY1]; exact ENNReal.one_ne_top)
  have e1 : ∀ m : EuclideanSpace ℝ (Fin d) → ENNReal, Measurable m →
      (∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), m z < ⊤) →
      (volume.withDensity m S).toReal = ∫ z, (m z).toReal * S.indicator 1 z := by
    intro m hm hfin
    have := integral_indicator_one (μ := volume.withDensity m) hS
    rw [measureReal_def] at this
    rw [← this, integral_withDensity_eq_integral_toReal_smul hm hfin]
    simp only [smul_eq_mul]
  rw [e1 μX hμX hXfin, integral_withDensity_eq_integral_toReal_smul hμX hXfin] at hX
  rw [e1 μY hμY hYfin, integral_withDensity_eq_integral_toReal_smul hμY hYfin]
  simp only [smul_eq_mul] at hX ⊢
  have IX : Integrable (fun z => (μX z).toReal) :=
    integrable_toReal_of_lintegral_ne_top hμX.aemeasurable (by rw [hμX1]; simp)
  have IY : Integrable (fun z => (μY z).toReal) :=
    integrable_toReal_of_lintegral_ne_top hμY.aemeasurable (by rw [hμY1]; simp)
  have hIm : Measurable (S.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ)) :=
    measurable_const.indicator hS
  have hIb : ∀ z, ‖S.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ) z‖ ≤ 1 := by
    intro z; by_cases hz : z ∈ S <;> simp [hz]
  have hhb : ∀ z, ‖h z‖ ≤ 1 := by
    intro z; rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hh01 z]
  have int1 : ∀ m : EuclideanSpace ℝ (Fin d) → ℝ, Integrable m →
      Integrable (fun z => m z * S.indicator 1 z) := fun m hm =>
    hm.mul_bdd hIm.aestronglyMeasurable (ae_of_all _ hIb)
  have int2 : ∀ m : EuclideanSpace ℝ (Fin d) → ℝ, Integrable m →
      Integrable (fun z => m z * h z) := fun m hm =>
    hm.mul_bdd hh.aestronglyMeasurable (ae_of_all _ hhb)
  have hX' : 0 ≤ ∫ z, (μX z).toReal * (h z - S.indicator 1 z) := by
    simp only [mul_sub]
    rw [integral_sub (int2 _ IX) (int1 _ IX)]; linarith
  have hDb : ∀ z, ‖h z - S.indicator (1 : EuclideanSpace ℝ (Fin d) → ℝ) z‖ ≤ 1 := by
    intro z
    rw [Real.norm_eq_abs, abs_le]
    have := hh01 z
    by_cases hz : z ∈ S
    · simp only [Set.indicator_of_mem hz, Pi.one_apply]; constructor <;> linarith
    · simp only [Set.indicator_of_notMem hz, sub_zero]; constructor <;> linarith
  have key : t * ∫ z, (μX z).toReal * (h z - S.indicator 1 z)
      ≤ ∫ z, (μY z).toReal * (h z - S.indicator 1 z) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact ((IX.mul_bdd (hh.sub hIm).aestronglyMeasurable (ae_of_all _ hDb))).const_mul t
    · exact IY.mul_bdd (hh.sub hIm).aestronglyMeasurable (ae_of_all _ hDb)
    · filter_upwards [hXfin, hYfin] with z hx hy
      have hft : (ENNReal.ofReal t * μX z).toReal = t * (μX z).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal ht.le]
      by_cases hz : z ∈ S
      · have hle : (μY z).toReal ≤ t * (μX z).toReal := by
          rw [← hft]
          exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx.ne) hz
        simp only [Set.indicator_of_mem hz, Pi.one_apply]
        have := hh01 z
        nlinarith
      · have hlt : t * (μX z).toReal < (μY z).toReal := by
          rw [← hft]
          exact ENNReal.toReal_strict_mono hy.ne (not_le.mp hz)
        simp only [Set.indicator_of_notMem hz, sub_zero]
        have := hh01 z
        nlinarith
  have : 0 ≤ ∫ z, (μY z).toReal * (h z - S.indicator 1 z) := by
    nlinarith [mul_nonneg ht.le hX']
  simp only [mul_sub] at this
  rw [integral_sub (int2 _ IY) (int1 _ IY)] at this
  linarith
