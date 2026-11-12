-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_fixed_count_residual_future_joint_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:33:03.683193+00:00
-- url     : https://prove2.me/submissions/ae0c8a35-f654-4dfc-b033-388f6318a383

import Theorems.Thm_AvramDividend_Classical_chat06_exact_count_cylinder_from_arrival_threshold
import Theorems.Thm_AvramDividend_Classical_avram_a06_count_residual_cylinder_ae
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- A joint full-measure renewal threshold is enough for fixed-count residual factorisation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (Q : Set (ℕ → ℝ)) (hQ : MeasurableSet Q)
    (t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | (Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ Q ∧ N ω clock = n} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let sum (z : ℕ → ℝ) := ∑ i ∈ Finset.range n, z i
  let age (z : ℕ → ℝ) := max (clock - sum z) 0
  let D : Set (ℕ → ℝ) := {z | z ∈ Q ∧ sum z ≤ clock}
  have hSumMeas : Measurable sum := Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hAge : Measurable age := (measurable_const.sub hSumMeas).max measurable_const
  have hD : MeasurableSet D := hQ.inter (hSumMeas measurableSet_Iic)
  have hPrefix (ω : Ω) : sum (Z ω) = ∑ i ∈ Finset.range n, τ i ω := by
    unfold sum
    rw [hZ]; apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hDSet (u : ℝ) :
      {ω : Ω | Z ω ∈ D ∧ age (Z ω) + u < τ n ω} =
        {ω : Ω | Z ω ∈ Q ∧
          (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
    ext ω
    change
      ((Z ω ∈ Q ∧ sum (Z ω) ≤ clock) ∧
        max (clock - sum (Z ω)) 0 + u < τ n ω) ↔
      (Z ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω)
    rw [hPrefix ω, Finset.sum_range_succ]
    constructor
    · rintro ⟨⟨hq, hl⟩, hsurv⟩
      rw [max_eq_left (sub_nonneg.mpr hl)] at hsurv
      exact ⟨hq, hl, by linarith⟩
    · rintro ⟨hq, hl, hsurv⟩
      refine ⟨⟨hq, hl⟩, ?_⟩
      rw [max_eq_left (sub_nonneg.mpr hl)]; linarith
  have hEvent (u : ℝ) (hu : 0 ≤ u) :
      {ω : Ω | Z ω ∈ Q ∧ N ω clock = n ∧
        u < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)} =ᵐ[P]
      {ω : Ω | Z ω ∈ D ∧ age (Z ω) + u < τ n ω} := by
    rw [hDSet u]
    exact AvramDividend.Classical.avram_a06_count_residual_cylinder_ae
      P τ N hThresholdAE clock hclock n
      {ω | Z ω ∈ Q} u hu
  have hBase :
      {ω : Ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} =ᵐ[P]
      {ω : Ω | Z ω ∈ Q ∧ N ω clock = n} := by
    have hZero := hDSet (0 : ℝ)
    simp only [add_zero] at hZero
    rw [hZero]; filter_upwards [hThresholdAE] with ω hThreshold
    have hCyl :=
      AvramDividend.Classical.chat06_exact_count_cylinder_from_arrival_threshold
        (fun i => τ i ω) (N ω) hThreshold clock hclock n
    apply propext
    change (Z ω ∈ Q ∧
      (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock < ∑ i ∈ Finset.range (n + 1), τ i ω) ↔
      (Z ω ∈ Q ∧ N ω clock = n)
    exact and_congr_right (fun _ => hCyl.symm)
  have hJoint :=
    AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
      τ hτ hiid n Z hZ age hAge D B hD hB μ hLaw
      (Filter.Eventually.of_forall (fun z => le_max_right _ _)) hTail t ht
  have hJointAE :
      {ω : Ω | (Z ω ∈ Q ∧ N ω clock = n ∧
        t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =ᵐ[P]
      {ω : Ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} := by
    filter_upwards [hEvent t ht] with ω hω
    exact congrArg (fun p : Prop => p ∧ (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) hω
  calc
    P {ω | (Z ω ∈ Q ∧ N ω clock = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} := measure_congr hJointAE
    _ = (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := hJoint
    _ = (P {ω | Z ω ∈ Q ∧ N ω clock = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
        rw [measure_congr hBase]
