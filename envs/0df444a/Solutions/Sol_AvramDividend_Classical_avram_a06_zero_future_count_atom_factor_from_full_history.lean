-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_zero_future_count_atom_factor_from_full_history
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:37:18.029723+00:00
-- url     : https://prove2.me/submissions/c0020d27-de75-45e1-ad0f-0d8cdcb13aef

import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.HasLaw
import Theorems.Thm_AvramDividend_Classical_chat06_unit_exponential_full_count_history_independent_future_suffix
import Theorems.Thm_AvramDividend_Classical_avram_a06_increment_zero_atom_suffix_cylinder_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Measure ProbabilityTheory Set Finset
open scoped ENNReal
noncomputable section

/-- Zero future original-count increment is independent of the full observed count history. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hExp : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (H : Set Ω)
    (hHpast : MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =
      P H * ENNReal.ofReal (Real.exp (-t)) := by
  have hThreshAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u :=
    Filter.Eventually.of_forall hThreshold
  have hZero :=
    AvramDividend.Classical.avram_a06_increment_zero_atom_suffix_cylinder_ae
      P τ N hThreshAE clock
  have hAlmost :
      {ω | ω ∈ H ∧ N ω (clock + t) - N ω clock = 0} =ᵐ[P]
        {ω | ω ∈ H ∧ t < τ (N ω clock) ω -
          (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω)} := by
    filter_upwards [hZero] with ω hz
    exact propext (and_congr_right (fun _ => hz t))
  rw [measure_congr hAlmost]
  have hFull :=
    AvramDividend.Classical.chat06_unit_exponential_full_count_history_independent_future_suffix
      τ hτ hiid hExp N hThreshold clock hclock H hHpast
      t ht Set.univ MeasurableSet.univ
  have hLaw : HasLaw (fun ω (j : ℕ) => τ j ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P :=
    hiid.hasLaw_infinitePi hExp
      ((aemeasurable_pi_iff).2 (fun j => (hExp j).aemeasurable))
  haveI : IsProbabilityMeasure
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) :=
    (hLaw.isProbabilityMeasure_iff).mp inferInstance
  have hPiMass : (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) Set.univ = 1 :=
    measure_univ
  simpa [hPiMass] using hFull
