-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_stationary_path_clock_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:25:44.826085+00:00
-- url     : https://prove2.me/submissions/3b05aab2-8468-42a7-85c3-3a8544c9e9f9

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_shifted_path_residual_clock_factor
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw

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
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (t : ℝ≥0) (B : Set (ℝ≥0 → ℝ)) (hB : MeasurableSet B) :
    (P.prod Q) {z : Ω × Θ | τ z.1 + t < e z.2 ∧
       (fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1) ∈ B} =
      factor t * (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} *
        P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by
  rw [AvramDividend.Classical.avram_ws01e_b_levy_shifted_path_residual_clock_factor X τ hτ hStop Q e he
    discount hd hTail factor hShift t B hB]
  congr 1
  have hJ := AvramDividend.Classical.chat04_levy_joint_time_state_measurable X
  have hm1 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact (hJ.comp ((hτ.add_const s).prodMk measurable_id)).sub
      (hJ.comp (hτ.prodMk measurable_id))
  have hm2 : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) := by
    refine measurable_pi_lambda _ (fun s => ?_)
    exact hJ.comp (measurable_const.prodMk measurable_id)
  have hlaw := AvramDividend.Classical.levy_finiteStopping_shiftedFuturePath_sameLaw X τ hStop
  have := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ B) hlaw
  rw [Measure.map_apply hm1 hB, Measure.map_apply hm2 hB] at this
  exact this
