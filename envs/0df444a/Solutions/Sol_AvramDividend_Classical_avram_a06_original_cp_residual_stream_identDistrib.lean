-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_residual_stream_identDistrib
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:13:46.794062+00:00
-- url     : https://prove2.me/submissions/ab1b6f5f-bfb4-4f9e-8f6f-15fd988909c0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_jumpCount_zero_at_origin
import Theorems.Thm_AvramDividend_Classical_avram_a06_threshold_residual_strict_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_future_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_future_right_tail
import Theorems.Thm_AvramDividend_Classical_avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
import Theorems.Thm_AvramDividend_Classical_avram_a06_joint_pair_reassemble_identDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Reconstruct the entire original interarrival stream after a fixed physical clock. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) :
    IdentDistrib
      (fun ω (j : ℕ) =>
        if j = 0 then
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
          ((s : ℝ) - ∑ i ∈ Finset.range
            (LevyFoundations.jumpCount
              (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω)
        else
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + j) ω)
      (fun ω j => τ j ω) P P := by
  let N : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ → ℕ :=
    fun ω u => LevyFoundations.jumpCount (fun i => LevyFoundations.arrival τ i ω) u
  let R := fun ω => τ (N ω (s : ℝ)) ω -
    ((s : ℝ) - ∑ i ∈ Finset.range (N ω (s : ℝ)), τ i ω)
  let F := fun ω (j : ℕ) => τ (N ω (s : ℝ) + 1 + j) ω
  let U := fun ω => τ 0 ω
  let G := fun ω (j : ℕ) => τ (1 + j) ω
  have hThreshold :
      ∀ᵐ ω ∂P, ∀ u k,
        k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u := by
    simpa only [N] using
      (AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae P τ Y hd)
  have hRpos : ∀ᵐ ω ∂P, 0 < R ω := by
    simpa only [R] using
      (AvramDividend.Classical.avram_a06_threshold_residual_strict_positive_ae
        P τ N hThreshold (s : ℝ))
  have hZero : ∀ᵐ ω ∂P, N ω 0 = 0 := by
    simpa only [N] using
      (AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin P τ Y hd)
  have hUpos : ∀ᵐ ω ∂P, 0 < U ω := by
    have hPosZero :=
      AvramDividend.Classical.avram_a06_threshold_residual_strict_positive_ae
        P τ N hThreshold (0 : ℝ)
    filter_upwards [hPosZero, hZero] with ω hp hz
    simpa [U, hz] using hp
  have hRF : AEMeasurable (fun ω => (R ω, F ω)) P := by
    exact (AvramDividend.Classical.avram_a06_original_cp_residual_future_measurable
      P τ Y hd s).aemeasurable
  have hUG : AEMeasurable (fun ω => (U ω, G ω)) P := by
    have hG : Measurable G := by
      rw [measurable_pi_iff]
      intro j
      exact hd.measurable_interarrival (1 + j)
    exact ((hd.measurable_interarrival 0).prodMk hG).aemeasurable
  have hRect (t : ℝ) (ht : 0 ≤ t) (B : Set (ℕ → ℝ))
      (hB : MeasurableSet B) :
      P {ω | t < R ω ∧ F ω ∈ B} =
      P {ω | t < U ω ∧ G ω ∈ B} := by
    exact AvramDividend.Classical.avram_a06_original_cp_residual_future_right_tail
      P τ Y hd s t ht B hB
  have hPair := AvramDividend.Classical.avram_a06_generic_joint_law_of_strict_positive_right_ray_rectangles
    P R U F G hRF hUG hRpos hUpos hRect
  have hStream := AvramDividend.Classical.avram_a06_joint_pair_reassemble_identDistrib
    P R U F G hPair
  have hLeft :
      (fun ω (j : ℕ) => if j = 0 then R ω else F ω (j - 1)) =
      (fun ω (j : ℕ) => if j = 0 then R ω else τ (N ω (s : ℝ) + j) ω) := by
    funext ω j
    cases j with
    | zero => rfl
    | succ k => simp [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  have hRight :
      (fun ω (j : ℕ) => if j = 0 then U ω else G ω (j - 1)) =
      (fun ω j => τ j ω) := by
    funext ω j
    cases j with
    | zero => rfl
    | succ k => simp [G, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [hLeft, hRight] at hStream
  simpa only [R, N] using hStream
