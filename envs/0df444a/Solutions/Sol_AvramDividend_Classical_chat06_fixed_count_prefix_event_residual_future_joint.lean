-- Prove2me | solution 1 for AvramDividend.Classical.chat06_fixed_count_prefix_event_residual_future_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:48:10.210122+00:00
-- url     : https://prove2.me/submissions/a64cad7f-11fa-4771-a3af-f07e98beb22f

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_indexed_iid_past_residual_full_future_joint_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- For every measurable event of the complete earlier waiting-time
prefix, the count-cylinder exponential residual and whole-future
suffix factor jointly against that prefix event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (Z : Ω → (ℕ → ℝ))
    (hZ : Z = fun ω i => if h : i < n then τ i ω else 0)
    (N : Ω → ℕ) (clock t : ℝ) (ht : 0 ≤ t)
    (Q : Set (ℕ → ℝ)) (hQ : MeasurableSet Q)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount :
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | Z ω ∈ Q ∧ N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | Z ω ∈ Q ∧ N ω = n} *
        ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let sum (z : ℕ → ℝ) := ∑ i ∈ Finset.range n, z i
  let age (z : ℕ → ℝ) := max (clock - sum z) 0
  let D : Set (ℕ → ℝ) := {z | z ∈ Q ∧ sum z ≤ clock}
  have hSum : Measurable sum :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hAge : Measurable age :=
    (measurable_const.sub hSum).max measurable_const
  have hD : MeasurableSet D :=
    hQ.inter (hSum measurableSet_Iic)
  have hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z :=
    Filter.Eventually.of_forall (fun z => le_max_right _ _)
  have hPrefixSum (ω : Ω) :
      sum (Z ω) = ∑ i ∈ Finset.range n, τ i ω := by
    unfold sum
    rw [hZ]
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hEvent (u : ℝ) :
      {ω | Z ω ∈ D ∧ age (Z ω) + u < τ n ω} =
        {ω | Z ω ∈ Q ∧
          (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
    ext ω
    have hs := hPrefixSum ω
    have hn : (∑ i ∈ Finset.range (n + 1), τ i ω) =
        (∑ i ∈ Finset.range n, τ i ω) + τ n ω :=
      Finset.sum_range_succ (fun i => τ i ω) n
    change ((Z ω ∈ Q ∧ sum (Z ω) ≤ clock) ∧
      max (clock - sum (Z ω)) 0 + u < τ n ω) ↔
      (Z ω ∈ Q ∧ (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω)
    rw [hs, hn]
    constructor
    · rintro ⟨⟨hq, hd⟩, hr⟩
      rw [max_eq_left (sub_nonneg.mpr hd)] at hr
      exact ⟨hq, hd, by linarith⟩
    · rintro ⟨hq, hd, hr⟩
      refine ⟨⟨hq, hd⟩, ?_⟩
      rw [max_eq_left (sub_nonneg.mpr hd)]
      linarith
  have hAE :
      (fun ω : Ω =>
        Z ω ∈ Q ∧ N ω = n ∧
          t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
          (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) =ᵐ[P]
      (fun ω : Ω =>
        ((Z ω ∈ Q ∧
          (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω)) ∧
          (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) := by
    filter_upwards [hCount] with ω hω
    apply propext
    change (Z ω ∈ Q ∧ N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) ↔
      ((Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B)
    rw [hω, Finset.sum_range_succ]
    constructor
    · rintro ⟨hq, ⟨hl, hu⟩, hr, hb⟩
      exact ⟨⟨hq, hl, by linarith⟩, hb⟩
    · rintro ⟨⟨hq, hl, hr⟩, hb⟩
      exact ⟨hq, ⟨hl, by linarith⟩, by linarith, hb⟩
  have hJoint :=
    AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
      τ hτ hiid n Z hZ age hAge D B hD hB μ hLaw
      hNonneg hTail t ht
  have h0 := hEvent 0
  simp only [add_zero] at h0
  have hBaseAE :
      (fun ω : Ω => Z ω ∈ Q ∧ N ω = n) =ᵐ[P]
      (fun ω : Ω => Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock < ∑ i ∈ Finset.range (n + 1), τ i ω) := by
    filter_upwards [hCount] with ω hw
    simpa only [hw]
  have hBase :
      P {ω | Z ω ∈ Q ∧ N ω = n} =
      P {ω | Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock < ∑ i ∈ Finset.range (n + 1), τ i ω} :=
    measure_congr hBaseAE
  calc
    P {ω | Z ω ∈ Q ∧ N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      P {ω | ((Z ω ∈ Q ∧
        (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B)} :=
      measure_congr hAE
    _ = P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} := by
      change P ({ω | Z ω ∈ Q ∧
          (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} ∩
          {ω | (fun j : ℕ => τ (n + 1 + j) ω) ∈ B}) =
        P ({ω | Z ω ∈ D ∧ age (Z ω) + t < τ n ω} ∩
          {ω | (fun j : ℕ => τ (n + 1 + j) ω) ∈ B})
      rw [hEvent t]
    _ = (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := hJoint
    _ = (P {ω | Z ω ∈ Q ∧ N ω = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
      rw [h0, ← hBase]
