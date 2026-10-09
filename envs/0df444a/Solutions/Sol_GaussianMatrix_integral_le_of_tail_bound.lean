-- Prove2me | solution 1 for GaussianMatrix.integral_le_of_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @tc
-- created : 2026-10-09T03:58:08.607049+00:00
-- url     : https://prove2.me/submissions/3f5529db-6fe7-43d8-a483-ec150be8c85e

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

open GaussianMatrix

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : AEMeasurable f μ) (hnn : 0 ≤ᵐ[μ] f)
    (C m : ℝ) (hC : 0 < C) (hm : 1 < m)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (C * t ^ (-m))) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ C ^ (1 / m) * m / (m - 1) := by
  set a : ℝ := C ^ (1 / m) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hC _
  have hm1 : 0 < m - 1 := by linarith
  -- `C * a ^ (1 - m) = a`
  have hCa : C * a ^ (-m + 1) = a := by
    rw [ha_def, ← Real.rpow_mul hC.le]
    have : 1 / m * (-m + 1) = 1 / m - 1 := by field_simp; ring
    rw [this, Real.rpow_sub_one hC.ne']
    field_simp
  -- the tail integral over `(a, ∞)`
  have hint : IntegrableOn (fun t : ℝ => C * t ^ (-m)) (Set.Ioi a) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul C
  have hval : ∫ t in Set.Ioi a, C * t ^ (-m) = a / (m - 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha]
    have hne : -m + 1 ≠ 0 := by linarith
    rw [show C * (-a ^ (-m + 1) / (-m + 1)) = (C * a ^ (-m + 1)) / (m - 1) by
      field_simp; ring, hCa]
  have hlow : ∫⁻ t in Set.Ioc 0 a, μ {x | t < f x} ≤ ENNReal.ofReal a := by
    calc ∫⁻ t in Set.Ioc 0 a, μ {x | t < f x} ≤ ∫⁻ _ in Set.Ioc 0 a, 1 :=
          lintegral_mono fun t => prob_le_one
      _ = ENNReal.ofReal a := by
          rw [setLIntegral_const, one_mul, Real.volume_Ioc, sub_zero]
  have hhigh : ∫⁻ t in Set.Ioi a, μ {x | t < f x} ≤ ENNReal.ofReal (a / (m - 1)) := by
    calc ∫⁻ t in Set.Ioi a, μ {x | t < f x}
        ≤ ∫⁻ t in Set.Ioi a, ENNReal.ofReal (C * t ^ (-m)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => htail t ?_
          exact lt_trans ha ht
      _ = ENNReal.ofReal (∫ t in Set.Ioi a, C * t ^ (-m)) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint]
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact mul_nonneg hC.le (Real.rpow_nonneg (lt_trans ha ht).le _)
      _ = ENNReal.ofReal (a / (m - 1)) := by rw [hval]
  have hbound : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (a * m / (m - 1)) := by
    rw [lintegral_eq_lintegral_meas_lt μ hnn hf, ← Set.Ioc_union_Ioi_eq_Ioi ha.le,
      lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same]
    calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal (a / (m - 1)) := add_le_add hlow hhigh
      _ = ENNReal.ofReal (a * m / (m - 1)) := by
          rw [← ENNReal.ofReal_add ha.le (div_nonneg ha.le hm1.le)]
          congr 1
          field_simp
          ring
  have hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ < ⊤ := lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (div_nonneg (mul_nonneg ha.le (by linarith)) hm1.le) hbound
