-- Prove2me | solution 1 for AvramDividend.Classical.ripple_LevyStochCalc_progressive_joint_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:02:49.705924+00:00
-- url     : https://prove2.me/submissions/9cd8c093-73eb-4e34-9264-e2704489278c

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Progressive
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (Fr : Filtration ℝ mΩ) (H : Ω → ℝ → ℝ)
    (hp : LevyStochCalc.Probability.ProgressivelyMeasurable Fr H) :
    Measurable (Function.uncurry H) := by
  have hseq (n : ℕ) :
      StronglyMeasurable (fun p : Ω × ℝ =>
        (Iic (n : ℝ)).indicator (H p.1) p.2) := by
    exact (hp (n : ℝ)).mono
      (sup_le_sup (MeasurableSpace.comap_mono (Fr.le (n : ℝ))) le_rfl)
  have ht (p : Ω × ℝ) :
      Tendsto (fun n : ℕ =>
        (Iic (n : ℝ)).indicator (H p.1) p.2)
        atTop (𝓝 (H p.1 p.2)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt p.2
    apply tendsto_atTop_of_eventually_const (i₀ := N)
    intro n hn
    have hle : p.2 ≤ (n : ℝ) :=
      le_trans (le_of_lt hN) (by exact_mod_cast hn)
    exact Set.indicator_of_mem (Set.mem_Iic.mpr hle) _
  have hlim : Tendsto
      (fun n : ℕ => fun p : Ω × ℝ =>
        (Iic (n : ℝ)).indicator (H p.1) p.2)
      atTop (nhds (Function.uncurry H)) :=
    tendsto_pi_nhds.mpr ht
  exact (stronglyMeasurable_of_tendsto atTop hseq hlim).measurable
