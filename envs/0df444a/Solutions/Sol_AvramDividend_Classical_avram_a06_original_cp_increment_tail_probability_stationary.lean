-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_increment_tail_probability_stationary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:05:55.189818+00:00
-- url     : https://prove2.me/submissions/00204c06-8e99-4038-bfe1-91186f919167

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_increment_suffix_threshold_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_stream_identDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

/-- Transport original renewal-count increment tail events through the full residual stream law. -/
theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) (m : ℕ) :
    P {ω | m < LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ) -
      LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (s : ℝ)} =
    P {ω | m < LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (k : ℝ) -
      LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)} := by
  let N : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ → ℕ :=
    fun ω u => LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) u
  let W : ℝ≥0 → ((ℕ → ℝ) × (ℕ → ℝ)) → (ℕ → ℝ) :=
    fun c ω j =>
      if j = 0 then τ (N ω (c : ℝ)) ω -
          ((c : ℝ) - ∑ i ∈ Finset.range (N ω (c : ℝ)), τ i ω)
      else τ (N ω (c : ℝ) + j) ω
  let H : (ℕ → ℝ) → ℝ :=
    fun a => ∑ i ∈ Finset.range (m + 1), a i
  have hH : Measurable H := by
    exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)
  have hThreshold :
      ∀ᵐ ω ∂P, ∀ u j,
        j < N ω u ↔ (∑ i ∈ Finset.range (j + 1), τ i ω) ≤ u := by
    simpa only [N] using
      (AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae P τ Y hd)
  have hPrefix (c : ℝ≥0) (ω) :
      H (W c ω) =
      (τ (N ω (c : ℝ)) ω -
        ((c : ℝ) - ∑ i ∈ Finset.range (N ω (c : ℝ)), τ i ω)) +
      (∑ j ∈ Finset.range m, τ (N ω (c : ℝ) + 1 + j) ω) := by
    change (∑ i ∈ Finset.range (m + 1), W c ω i) = _
    rw [Finset.sum_range_succ']
    simp [W, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_comm]
  have hEvent (c : ℝ≥0) :
      P {ω | m < N ω ((c + k : ℝ≥0) : ℝ) - N ω (c : ℝ)} =
      P {ω | H (W c ω) ≤ (k : ℝ)} := by
    have hInc :=
      AvramDividend.Classical.avram_a06_count_increment_suffix_threshold_ae
        P τ N hThreshold (c : ℝ)
    apply measure_congr
    filter_upwards [hInc] with ω hw
    apply propext
    change (m < N ω ((c + k : ℝ≥0) : ℝ) - N ω (c : ℝ)) ↔
      (H (W c ω) ≤ (k : ℝ))
    simpa only [NNReal.coe_add, hPrefix c ω] using (hw (k : ℝ) m)
  have hLaw (c : ℝ≥0) :
      IdentDistrib (fun ω => H (W c ω))
        (fun ω => H (fun j => τ j ω)) P P := by
    have hFull :=
      AvramDividend.Classical.avram_a06_original_cp_residual_stream_identDistrib
        P τ Y hd c
    have hComp := ProbabilityTheory.IdentDistrib.comp hFull hH
    exact hComp
  have hSumProb (c : ℝ≥0) :
      P {ω | H (W c ω) ≤ (k : ℝ)} =
      P {ω | H (fun j => τ j ω) ≤ (k : ℝ)} := by
    have h := hLaw c
    have hMaps := congrArg
      (fun μ : Measure ℝ => μ (Iic (k : ℝ))) h.map_eq
    rw [Measure.map_apply_of_aemeasurable h.aemeasurable_fst measurableSet_Iic,
      Measure.map_apply_of_aemeasurable h.aemeasurable_snd measurableSet_Iic] at hMaps
    simpa only [Set.preimage, Set.mem_Iic] using hMaps
  change P {ω | m < N ω (s + k : ℝ) - N ω (s : ℝ)} =
    P {ω | m < N ω (k : ℝ) - N ω 0}
  calc
    P {ω | m < N ω (s + k : ℝ) - N ω (s : ℝ)} =
        P {ω | H (W s ω) ≤ (k : ℝ)} := hEvent s
    _ = P {ω | H (fun j => τ j ω) ≤ (k : ℝ)} := hSumProb s
    _ = P {ω | H (W 0 ω) ≤ (k : ℝ)} := (hSumProb 0).symm
    _ = P {ω | m < N ω ((0 + k : ℝ≥0) : ℝ) - N ω (0 : ℝ)} :=
      (hEvent 0).symm
    _ = P {ω | m < N ω (k : ℝ) - N ω 0} := by simp
