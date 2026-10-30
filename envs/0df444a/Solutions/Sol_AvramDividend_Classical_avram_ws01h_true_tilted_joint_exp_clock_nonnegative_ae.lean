-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_true_tilted_joint_exp_clock_nonnegative_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:53:50.957493+00:00
-- url     : https://prove2.me/submissions/8c678206-346c-4f75-bb02-bd9cc06e78cc

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_exp_clock_nonnegative_ae

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- True product Exp(p) clocks remain nonnegative almost everywhere after
ANY terminal path-dependent nonnegative Esscher likelihood weighting. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (p : ℝ) (hp : 0 < p) (D : Ω × ℝ → ℝ≥0∞) :
    ∀ᵐ z : Ω × ℝ ∂((P.prod (expMeasure p)).withDensity D),
      0 ≤ z.2 := by
  letI : IsProbabilityMeasure (expMeasure p) :=
    isProbabilityMeasure_expMeasure hp
  have hNeg : expMeasure p (Iio (0 : ℝ)) = 0 := by
    have h := (ae_iff).1 (avram_ws01h_true_exp_clock_nonnegative_ae p hp)
    have hset : Iio (0 : ℝ) = {r : ℝ | ¬ 0 ≤ r} := by
      ext r
      simp only [Set.mem_Iio, Set.mem_setOf_eq, not_le]
    rw [hset]
    exact h
  have hset : {z : Ω × ℝ | z.2 < 0} =
      (Set.univ : Set Ω) ×ˢ (Iio (0 : ℝ)) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ,
      true_and, Set.mem_Iio]
  have hProd :
      (P.prod (expMeasure p)) {z : Ω × ℝ | z.2 < 0} = 0 := by
    rw [hset, Measure.prod_prod]
    simp only [hNeg, mul_zero]
  have hAC : (P.prod (expMeasure p)).withDensity D ≪
      P.prod (expMeasure p) :=
        withDensity_absolutelyContinuous (P.prod (expMeasure p)) D
  apply (ae_iff).2
  change ((P.prod (expMeasure p)).withDensity D)
    {z : Ω × ℝ | ¬ 0 ≤ z.2} = 0
  have hbad : {z : Ω × ℝ | ¬ 0 ≤ z.2} =
      {z : Ω × ℝ | z.2 < 0} := by
    ext z
    simp only [Set.mem_setOf_eq, not_le]
  rw [hbad]
  exact hAC hProd
