-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_original_cp_residual_future_right_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:39:53.931442+00:00
-- url     : https://prove2.me/submissions/86d7cbae-ef68-4158-8b45-b172f548488e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_threshold_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_jumpCount_zero_at_origin
import Theorems.Thm_AvramDividend_Classical_avram_a06_renewal_residual_future_from_ae_threshold
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_interarrival_survival
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_deterministic_suffix_full_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) (t : ℝ) (ht : 0 ≤ t)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
    P {ω | t < τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
      ((s : ℝ) - ∑ i ∈ Finset.range
        (LevyFoundations.jumpCount
          (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω) ∧
      (fun j : ℕ => τ (LevyFoundations.jumpCount
        (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + 1 + j) ω) ∈ B} =
    P {ω | t < τ 0 ω ∧ (fun j : ℕ => τ (1 + j) ω) ∈ B} := by
  let N : ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ → ℕ :=
    fun ω u => LevyFoundations.jumpCount (fun j => LevyFoundations.arrival τ j ω) u
  let μ : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))
  have hτ (n : ℕ) : Measurable (τ n) := hd.measurable_interarrival n
  have hiid : iIndepFun τ P := by
    have h' := hd.indep.precomp (g := Sum.inl) Sum.inl_injective
    simpa [Function.comp] using h'
  have hTailLaw (n : ℕ) :
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P :=
    AvramDividend.Classical.avram_a06_original_cp_deterministic_suffix_full_law P τ Y hd (n + 1)
  have hThreshold :
      ∀ᵐ ω ∂P, ∀ u k,
        k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u := by
    simpa only [N] using
      (AvramDividend.Classical.avram_a06_original_cp_count_threshold_ae P τ Y hd)
  have hN (u : ℝ) : Measurable (fun ω => N ω u) := by
    exact AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public τ hτ u
  have hSurv (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)) :=
    AvramDividend.Classical.avram_a06_original_cp_interarrival_survival P τ Y hd n u hu
  have hJoint (u : ℝ) (hu : 0 ≤ u) :
      P {ω | t < τ (N ω u) ω -
        (u - ∑ i ∈ Finset.range (N ω u), τ i ω) ∧
        (fun j : ℕ => τ (N ω u + 1 + j) ω) ∈ B} =
        ENNReal.ofReal (Real.exp (-t)) * μ B :=
    AvramDividend.Classical.avram_a06_renewal_residual_future_from_ae_threshold
      τ hτ hiid N hThreshold u hu (hN _) t ht μ hTailLaw B hB hSurv
  have hZero : ∀ᵐ ω ∂P, N ω 0 = 0 := by
    simpa only [N] using
      (AvramDividend.Classical.avram_a06_original_cp_jumpCount_zero_at_origin P τ Y hd)
  have hZeroEvent :
      P {ω | t < τ (N ω 0) ω -
        (0 - ∑ i ∈ Finset.range (N ω 0), τ i ω) ∧
        (fun j : ℕ => τ (N ω 0 + 1 + j) ω) ∈ B} =
      P {ω | t < τ 0 ω ∧ (fun j : ℕ => τ (1 + j) ω) ∈ B} := by
    apply measure_congr
    filter_upwards [hZero] with ω hw
    apply propext
    change
      (t < τ (N ω 0) ω -
        (0 - ∑ i ∈ Finset.range (N ω 0), τ i ω) ∧
        (fun j : ℕ => τ (N ω 0 + 1 + j) ω) ∈ B) ↔
      (t < τ 0 ω ∧ (fun j : ℕ => τ (1 + j) ω) ∈ B)
    simp [hw]
  change
    P {ω | t < τ (N ω (s : ℝ)) ω -
      ((s : ℝ) - ∑ i ∈ Finset.range (N ω (s : ℝ)), τ i ω) ∧
      (fun j : ℕ => τ (N ω (s : ℝ) + 1 + j) ω) ∈ B} =
    P {ω | t < τ 0 ω ∧ (fun j : ℕ => τ (1 + j) ω) ∈ B}
  have hs : (0 : ℝ) ≤ (s : ℝ) := by exact s.property
  exact (hJoint (s : ℝ) hs).trans ((hJoint 0 (by norm_num)).symm.trans hZeroEvent)
