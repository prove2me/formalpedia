-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_positive_future_count_factor_from_ae_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:38:02.66719+00:00
-- url     : https://prove2.me/submissions/24b302a2-c6f7-4137-afc6-4315ac62a0fb

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_all_atom_suffix_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_residual_suffix_full_joint_factor_from_history_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Deduce positive future-count independence from the full residual/suffix law. -/
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
    (t : ℝ) (ht : 0 ≤ t) (k : ℕ) (hk : 0 < k) :
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = k} =
      P H * P {ω | N ω (clock + t) - N ω clock = k} := by
  let residual (ω : Ω) : ℝ :=
    τ (N ω clock) ω -
      (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)
  let tail (ω : Ω) (j : ℕ) : ℝ := τ (N ω clock + 1 + j) ω
  let C : Set (ℝ × (ℕ → ℝ)) :=
    {p | p.1 + (∑ j ∈ Finset.range (k - 1), p.2 j) ≤ t ∧
      t < p.1 + (∑ j ∈ Finset.range k, p.2 j)}
  have hSum (m : ℕ) :
      Measurable (fun p : ℝ × (ℕ → ℝ) =>
        ∑ j ∈ Finset.range m, p.2 j) :=
    Finset.measurable_sum _ (fun j _ =>
      (measurable_pi_apply j).comp measurable_snd)
  have hC : MeasurableSet C := by
    have ha : Measurable (fun p : ℝ × (ℕ → ℝ) =>
        p.1 + ∑ j ∈ Finset.range (k - 1), p.2 j) :=
      measurable_fst.add (hSum (k - 1))
    have hb : Measurable (fun p : ℝ × (ℕ → ℝ) =>
        p.1 + ∑ j ∈ Finset.range k, p.2 j) :=
      measurable_fst.add (hSum k)
    exact (ha measurableSet_Iic).inter (hb measurableSet_Ioi)
  have hAtom :=
    AvramDividend.Classical.avram_a06_increment_all_atom_suffix_cylinder_ae
      P τ N hThresholdAE clock
  have hAE : ∀ᵐ ω ∂P,
      (N ω (clock + t) - N ω clock = k) ↔
      (residual ω, tail ω) ∈ C := by
    filter_upwards [hAtom] with ω hω
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    simpa only [if_neg hk0, residual, tail, C, Set.mem_setOf_eq]
      using (hω t k)
  have hLeft :
      {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = k} =ᵐ[P]
      {ω | ω ∈ H ∧ (residual ω, tail ω) ∈ C} := by
    filter_upwards [hAE] with ω hω
    exact propext (and_congr_right (fun _ => hω))
  have hRight :
      {ω | N ω (clock + t) - N ω clock = k} =ᵐ[P]
      {ω | (residual ω, tail ω) ∈ C} := by
    filter_upwards [hAE] with ω hω
    exact propext hω
  have hJoint :=
    AvramDividend.Classical.avram_a06_residual_suffix_full_joint_factor_from_history_ae
      τ hτ hiid hExp N hThresholdAE clock hclock hN H hH hHpast C hC
  calc
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = k} =
        P {ω | ω ∈ H ∧ (residual ω, tail ω) ∈ C} :=
      measure_congr hLeft
    _ = P H * P {ω | (residual ω, tail ω) ∈ C} := hJoint
    _ = P H * P {ω | N ω (clock + t) - N ω clock = k} := by
      rw [← measure_congr hRight]
