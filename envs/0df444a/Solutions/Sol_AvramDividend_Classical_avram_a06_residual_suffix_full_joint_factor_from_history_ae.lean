-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_residual_suffix_full_joint_factor_from_history_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:46:47.243496+00:00
-- url     : https://prove2.me/submissions/427ce773-76f0-4ad9-aa7d-d2c25962be60

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_random_index_coordinate_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a06_threshold_residual_strict_positive_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_history_prefix_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_countwise_iid_residual_future_joint_ae
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
import Theorems.Thm_AvramDividend_Classical_avram_a06_full_joint_factor_of_positive_tail_rectangles

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Lift a.e. renewal countwise tail factorisation to every measurable joint event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (D : Set (ℝ × (ℕ → ℝ))) (hD : MeasurableSet D) :
    P {ω | ω ∈ H ∧
      (τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω),
        (fun j : ℕ => τ (N ω clock + 1 + j) ω)) ∈ D} =
      P H * P {ω |
        (τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω),
          (fun j : ℕ => τ (N ω clock + 1 + j) ω)) ∈ D} := by
  let Rn (n : ℕ) (ω : Ω) :=
    τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)
  let R (ω : Ω) := Rn (N ω clock) ω
  let F (ω : Ω) (j : ℕ) := τ (N ω clock + 1 + j) ω
  let μ : Measure (ℕ → ℝ) := infinitePi (fun _ : ℕ => expMeasure 1)
  have hRn : ∀ n, Measurable (Rn n) := by
    intro n
    exact (hτ n).sub (measurable_const.sub
      (Finset.measurable_sum _ fun i _ => hτ i))
  have hR : Measurable R := by
    exact AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
      Rn hRn (fun ω => N ω clock) hN
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro j
    exact AvramDividend.Classical.avram_a06_random_index_coordinate_measurable
      (fun n ω => τ (n + 1 + j) ω)
      (fun n => hτ (n + 1 + j))
      (fun ω => N ω clock) hN
  have hPos : ∀ᵐ ω ∂P, 0 < R ω := by
    simpa only [R, Rn] using
      (AvramDividend.Classical.avram_a06_threshold_residual_strict_positive_ae
        P τ N hThresholdAE clock)
  have hLaw (n : ℕ) :
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P :=
    AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
      τ hτ hiid (expMeasure 1) hExp n
  have hTailLaw (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)) :=
    AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
      (τ n) (hExp n) u hu
  have hJoint (E : Set Ω) (hE : MeasurableSet E)
      (hEpast : MeasurableSet[
        MeasurableSpace.comap
          (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
          (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] E)
      (u : ℝ) (hu : 0 ≤ u)
      (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
      P {ω | ω ∈ E ∧ u < R ω ∧ F ω ∈ B} =
        (P E * ENNReal.ofReal (Real.exp (-u))) * μ B := by
    have hRep (n : ℕ) :=
      AvramDividend.Classical.avram_a06_count_history_prefix_representation_ae
        P (fun ω i => τ i ω)
        (fun ω i => if i < n then τ i ω else 0)
        N clock n hThresholdAE (fun ω i => rfl) E hEpast
    simpa only [R, Rn, F] using
      (AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
        τ hτ hiid N hThresholdAE clock hclock hN
        E hE hRep u hu μ hLaw B hB hTailLaw)
  have hTail (u : ℝ) (hu : 0 ≤ u)
      (B : Set (ℕ → ℝ)) (hB : MeasurableSet B) :
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
        P H * P {ω | u < R ω ∧ F ω ∈ B} := by
    have hAll := hJoint Set.univ MeasurableSet.univ MeasurableSet.univ u hu B hB
    have hMarg : P {ω | u < R ω ∧ F ω ∈ B} =
        ENNReal.ofReal (Real.exp (-u)) * μ B := by
      simpa only [Set.mem_univ, true_and, measure_univ, one_mul] using hAll
    calc
      P {ω | ω ∈ H ∧ u < R ω ∧ F ω ∈ B} =
          (P H * ENNReal.ofReal (Real.exp (-u))) * μ B :=
        hJoint H hH hHpast u hu B hB
      _ = P H * (ENNReal.ofReal (Real.exp (-u)) * μ B) := mul_assoc _ _ _
      _ = P H * P {ω | u < R ω ∧ F ω ∈ B} := by rw [hMarg]
  simpa only [R, Rn, F] using
    (AvramDividend.Classical.avram_a06_full_joint_factor_of_positive_tail_rectangles
      R hR F hF H hH hPos hTail D hD)
