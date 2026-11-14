-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:12:13.541591+00:00
-- url     : https://prove2.me/submissions/1301138e-d279-469a-a011-61c8973dddda

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

/-- A physical Gaussian raw squared large-tail sum is dominated by the
integrable centred source squares plus the raw-centred cross-energy. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (hA : ∀ i, MeasurableSet {ω : Ω | A i ω})
    (Z : ℕ → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (d η : ℝ)
    (hEI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0) P)
    (hAI : Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        |(Z i ω + d)^2 - (Z i ω)^2| else 0) P) :
    Integrable (fun ω =>
      ∑ i ∈ S, if A i ω then
        (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) else 0) P := by
  classical
  let T : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if A i ω then
      (if η ≤ |Z i ω + d| then (Z i ω + d)^2 else 0) else 0
  let E : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if A i ω then (Z i ω)^2 else 0
  let B : Ω → ℝ := fun ω =>
    ∑ i ∈ S, if A i ω then |(Z i ω + d)^2 - (Z i ω)^2| else 0
  have hm : Measurable T := by
    dsimp [T]
    apply Finset.measurable_sum
    intro i hi
    have hc : MeasurableSet {ω : Ω | η ≤ |Z i ω + d|} :=
      measurableSet_Ici.preimage ((hZ i).add_const d).norm
    have hz : Measurable (fun ω => (Z i ω + d)^2) := by
      fun_prop
    exact Measurable.ite (hA i)
      (Measurable.ite hc hz measurable_const) measurable_const
  have hpoint (ω : Ω) : 0 ≤ T ω ∧ T ω ≤ E ω + B ω :=
    avram_ga_a192_masked_Gaussian_raw_large_square_le_centered_energy_plus_cross
      S A Z d η ω
  have hDom : Integrable (fun ω => E ω + B ω) P := hEI.add hAI
  have hInt : Integrable T P := by
    apply hDom.mono' hm.aestronglyMeasurable
    filter_upwards [] with ω
    have hp := hpoint ω
    have he : 0 ≤ E ω := by
      dsimp [E]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    have hb : 0 ≤ B ω := by
      dsimp [B]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    have hnn : 0 ≤ E ω + B ω := add_nonneg he hb
    simpa only [Real.norm_eq_abs,abs_of_nonneg hp.1,
      abs_of_nonneg hnn] using hp.2
  exact hInt
