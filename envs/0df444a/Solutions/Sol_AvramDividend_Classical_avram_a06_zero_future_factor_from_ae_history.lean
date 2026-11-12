-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_zero_future_factor_from_ae_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:54:50.807782+00:00
-- url     : https://prove2.me/submissions/9e6ed569-fde5-4ba0-b46b-8f4fa2e5cd51

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_history_prefix_representation_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_countwise_iid_residual_future_joint_ae
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_haslaw_survival
import Theorems.Thm_AvramDividend_Classical_chat06_iid_shifted_suffix_common_infinite_product_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Zero future renewals are independent of every measurable past-count history event. -/
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
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =
      P H * ENNReal.ofReal (Real.exp (-t)) := by
  have hRep (n : ℕ) :
      ∃ Q : Set (ℕ → ℝ), MeasurableSet Q ∧
        (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
          (fun ω : Ω =>
            (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
            N ω clock = n) := by
    exact AvramDividend.Classical.avram_a06_count_history_prefix_representation_ae
      P (fun ω i => τ i ω)
      (fun ω i => if i < n then τ i ω else 0)
      N clock n hThresholdAE (by intro ω i; rfl) H hHpast
  have hZero :=
    AvramDividend.Classical.avram_a06_increment_zero_atom_suffix_cylinder_ae
      P τ N hThresholdAE clock
  have hAlmost :
      {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =ᵐ[P]
        {ω | ω ∈ H ∧ t < τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)} := by
    filter_upwards [hZero] with ω hz
    exact propext (and_congr_right (fun _ => hz t))
  rw [measure_congr hAlmost]
  have hFull :=
    AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
      τ hτ hiid N hThresholdAE clock hclock hN H hH hRep t ht
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ)))
      (fun n =>
        AvramDividend.Classical.chat06_iid_shifted_suffix_common_infinite_product_law
          τ hτ hiid (expMeasure 1) hExp n)
      Set.univ MeasurableSet.univ
      (fun n u hu =>
        AvramDividend.Classical.chat06_unit_exponential_haslaw_survival
          (τ n) (hExp n) u hu)
  have hLaw : HasLaw (fun ω (j : ℕ) => τ j ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P :=
    hiid.hasLaw_infinitePi hExp
      ((aemeasurable_pi_iff).2 (fun j => (hExp j).aemeasurable))
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) :=
    (hLaw.isProbabilityMeasure_iff).mp inferInstance
  have hPiMass :
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) Set.univ = 1 :=
    measure_univ
  simpa [hPiMass] using hFull
