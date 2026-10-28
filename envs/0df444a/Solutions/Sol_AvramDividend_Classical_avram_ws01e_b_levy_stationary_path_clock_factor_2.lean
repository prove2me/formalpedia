-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_b_levy_stationary_path_clock_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T23:26:29.63056+00:00
-- url     : https://prove2.me/submissions/4bd2a631-8070-4132-b4ba-b07d9318fa24

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_shifted_path_residual_clock_factor
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_shiftedFuturePath_sameLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Finite stopping-time Lévy regeneration identifies the post-stop path
with the original Lévy path law, while an independent residual clock
contributes only its exact memoryless survival factor. -/
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
  have hJ := chat04_levy_joint_time_state_measurable X
  have hY : Measurable (fun ω : Ω => fun s : ℝ≥0 =>
      X.X (τ ω + s) ω - X.X (τ ω) ω) := by
    rw [measurable_pi_iff]
    intro s
    exact (hJ.comp ((hτ.add_const s).prodMk measurable_id)).sub
      (hJ.comp (hτ.prodMk measurable_id))
  have hX : Measurable (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) := by
    rw [measurable_pi_iff]
    intro s
    exact hJ.comp (measurable_const.prodMk measurable_id)
  have hLaw := levy_finiteStopping_shiftedFuturePath_sameLaw X τ hStop
  have hBPath :
      P {ω : Ω | (fun s : ℝ≥0 => X.X (τ ω + s) ω - X.X (τ ω) ω) ∈ B} =
      P {ω : Ω | (fun s : ℝ≥0 => X.X s ω) ∈ B} := by
    calc
      _ = (Measure.map (fun ω : Ω => fun s : ℝ≥0 =>
            X.X (τ ω + s) ω - X.X (τ ω) ω) P) B := by
          rw [Measure.map_apply hY hB]
          rfl
      _ = (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) B :=
          congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ B) hLaw
      _ = _ := by
          rw [Measure.map_apply hX hB]
          rfl
  rw [avram_ws01e_b_levy_shifted_path_residual_clock_factor
    X τ hτ hStop Q e he discount hd hTail factor hShift t B hB, hBPath]
