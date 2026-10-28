-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:03:21.02628+00:00
-- url     : https://prove2.me/submissions/5062d4d0-f36a-42f0-893c-6830599df1f3

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_residual_clock_freshPath_rectangle

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map
      (fun z : Ω × Θ =>
        ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    (Measure.map (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}])).prod
    (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by
  haveI : IsProbabilityMeasure ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) :=
    cond_isProbabilityMeasure hPos
  have hJ := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hm1 : Measurable (fun z : Ω × Θ => fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact (hJ.comp (((hτ.comp measurable_fst).add_const s).prodMk measurable_fst)).sub
      (hJ.comp ((hτ.comp measurable_fst).prodMk measurable_fst))
  have hm2 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact hJ.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun z : Ω × Θ => (e z.2 : ℝ) - (τ z.1 : ℝ)) := by fun_prop
  have hind := AvramDividend.Classical.avram_ws01e_b_levy_conditional_residual_clock_shiftedPath_indepFun
    X τ hτ hStop Q e he hPos
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hm1.aemeasurable] at hind
  rw [hind]
  congr 1
  ext B hB
  rw [Measure.map_apply hm1 hB, Measure.map_apply hm2 hB]
  have h := AvramDividend.Classical.avram_ws01e_b_levy_residual_clock_freshPath_rectangle
    X τ hτ hStop Q e he univ MeasurableSet.univ B hB
  have h1 : {z : Ω × Θ | ((e z.2 : ℝ) - (τ z.1 : ℝ)) ∈ (univ : Set ℝ)} = univ := by
    ext z; simp
  rw [h1, measure_univ, one_mul] at h
  refine Eq.trans ?_ (Eq.trans h ?_)
  · congr 1; ext z; simp
  · rfl
