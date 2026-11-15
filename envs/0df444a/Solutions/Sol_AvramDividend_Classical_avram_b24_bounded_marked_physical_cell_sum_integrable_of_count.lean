-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_bounded_marked_physical_cell_sum_integrable_of_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:35:57.048859+00:00
-- url     : https://prove2.me/submissions/4d8c150e-582c-487b-963c-5e442cb60262

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (marked : Ω → Finset ℕ)
    (hCount : Integrable (fun ω => ((marked ω).card : ℝ)) P)
    (W : ℕ → Ω → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ i ω, |W i ω| ≤ L)
    (hMeas : AEStronglyMeasurable
      (fun ω => ∑ i ∈ marked ω, W i ω) P) :
    Integrable (fun ω => ∑ i ∈ marked ω, W i ω) P := by
  have hBound (ω : Ω) :
      ‖∑ i ∈ marked ω, W i ω‖ ≤ L * ((marked ω).card : ℝ) := by
    calc
      ‖∑ i ∈ marked ω, W i ω‖
        ≤ ∑ i ∈ marked ω, ‖W i ω‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ marked ω, L := by
        apply Finset.sum_le_sum
        intro i hi
        simpa only [Real.norm_eq_abs] using hW i ω
      _ = L * ((marked ω).card : ℝ) := by
        simp [mul_comm]
  exact Integrable.mono' (hCount.const_mul L) hMeas
    (Filter.Eventually.of_forall hBound)
