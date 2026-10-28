-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_levy_shifted_path_residual_clock_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T22:01:43.180132+00:00
-- url     : https://prove2.me/submissions/44f992e8-bd56-4396-83fc-1b9e322b3b7d

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_residual_clock_survival_shift

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
        P {ω : Ω |
          (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) ∈ B} := by
  have hJ := chat04_levy_joint_time_state_measurable X
  have hY : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) := by
    rw [measurable_pi_iff]
    intro s
    exact (hJ.comp ((hτ.add_const s).prodMk measurable_id)).sub (hJ.comp (hτ.prodMk measurable_id))
  exact avram_ws01e_b_residual_clock_survival_shift P Q τ hτ _ hY
    (levy_finiteStopping_clock_indep_shiftedPath X τ hStop) e he discount hd hTail factor hShift t B hB
