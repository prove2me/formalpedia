-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_predictable_conditionally_centered_physical_grid_L2_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T10:20:49.229925+00:00
-- url     : https://prove2.me/submissions/8d701ff5-90b9-4bd1-ba0c-1bfbb212eb71

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

/-- A genuine finite physical grid with conditional centred increments
and past-predictable weights has the full diagonal L2 isometry. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ j, m j ≤ mΩ)
    (H V Z : ℕ → Ω → ℝ)
    (hZ : ∀ i ω, Z i ω = H i ω * V i ω)
    (hVInt : ∀ j ∈ Finset.range n, Integrable (V j) P)
    (hCond : ∀ j ∈ Finset.range n,
      P[V j | m j] =ᵐ[P] (fun _ => 0))
    (hPair : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      Integrable (fun ω => Z i ω * Z j ω) P)
    (hPast : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i < j →
      StronglyMeasurable[m j] (fun ω => Z i ω * H j ω)) :
    (∫ ω, (∑ i ∈ Finset.range n, Z i ω)^2 ∂P) =
      ∑ i ∈ Finset.range n, ∫ ω, (Z i ω)^2 ∂P := by
  have hCross : ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n,
      i ≠ j → (∫ ω, Z i ω * Z j ω ∂P) = 0 := by
    intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hZero :=
        avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
          (m j) (hm j) (fun ω => Z i ω * H j ω) (V j)
          (hPast i hi j hj hij) ?_ (hVInt j hj) (hCond j hj)
      · convert hZero using 1
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZ j ω]
        ring
      · convert hPair i hi j hj using 1
        funext ω
        rw [hZ j ω]
        ring
    · have hZero :=
        avram_pj_original_past_coefficient_future_fullmark_condExp_zero_cross
          (m i) (hm i) (fun ω => Z j ω * H i ω) (V i)
          (hPast j hj i hi hji) ?_ (hVInt i hi) (hCond i hi)
      · calc
          (∫ ω, Z i ω * Z j ω ∂P) =
              ∫ ω, Z j ω * Z i ω ∂P := by
                apply integral_congr_ae
                filter_upwards [] with ω
                ring
          _ = 0 := by
            convert hZero using 1
            apply integral_congr_ae
            filter_upwards [] with ω
            rw [hZ i ω]
            ring
      · convert hPair j hj i hi using 1
        funext ω
        rw [hZ i ω]
        ring
  exact avram_pj_original_marked_grid_pairwise_L2_orthogonality_yields_full_sum_energy
    P (Finset.range n) Z hPair hCross
