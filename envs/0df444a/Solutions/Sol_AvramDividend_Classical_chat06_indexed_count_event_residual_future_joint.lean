-- Prove2me | solution 1 for AvramDividend.Classical.chat06_indexed_count_event_residual_future_joint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:32:36.967154+00:00
-- url     : https://prove2.me/submissions/638b784b-e692-4f4d-88db-9534cb871941

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


/-- Joint exponential residual and complete post-claim suffix law
on a concrete fixed-clock count-selection event. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ)
    (N : Ω → ℕ) (clock t : ℝ) (ht : 0 ≤ t)
    (μ : Measure (ℕ → ℝ))
    (hLaw : HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u)))
    (hCount :
      (fun ω : Ω => N ω = n) =ᵐ[P]
        (fun ω => (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock < ∑ i ∈ Finset.range (n + 1), τ i ω)) :
    P {ω | N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      (P {ω | N ω = n} * ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let Z : Ω → (ℕ → ℝ) :=
    fun ω i => if h : i < n then τ i ω else 0
  let sum (z : ℕ → ℝ) := ∑ i ∈ Finset.range n, z i
  let age (z : ℕ → ℝ) := max (clock - sum z) 0
  let D : Set (ℕ → ℝ) := {z | sum z ≤ clock}
  have hSum : Measurable sum :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hAge : Measurable age :=
    (measurable_const.sub hSum).max measurable_const
  have hD : MeasurableSet D := hSum measurableSet_Iic
  have hNonneg : ∀ᵐ z ∂(P.map Z), 0 ≤ age z :=
    Filter.Eventually.of_forall (fun z => le_max_right _ _)
  have hPrefixSum (ω : Ω) :
      sum (Z ω) = ∑ i ∈ Finset.range n, τ i ω := by
    unfold sum Z
    apply Finset.sum_congr rfl
    intro i hi
    simp [Finset.mem_range.mp hi]
  have hEvent (u : ℝ) :
      {ω | Z ω ∈ D ∧ age (Z ω) + u < τ n ω} =
        {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω} := by
    ext ω
    have hs := hPrefixSum ω
    have hn : (∑ i ∈ Finset.range (n + 1), τ i ω) =
        (∑ i ∈ Finset.range n, τ i ω) + τ n ω :=
      Finset.sum_range_succ (fun i => τ i ω) n
    change (sum (Z ω) ≤ clock ∧
      max (clock - sum (Z ω)) 0 + u < τ n ω) ↔
      ((∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + u < ∑ i ∈ Finset.range (n + 1), τ i ω)
    rw [hs, hn]
    constructor
    · rintro ⟨hd, hr⟩
      rw [max_eq_left (sub_nonneg.mpr hd)] at hr
      exact ⟨hd, by linarith⟩
    · rintro ⟨hd, hr⟩
      refine ⟨hd, ?_⟩
      rw [max_eq_left (sub_nonneg.mpr hd)]
      linarith
  have hAE :
      (fun ω : Ω =>
        N ω = n ∧
          t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
          (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) =ᵐ[P]
      (fun ω : Ω =>
        ((∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω) ∧
          (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) := by
    filter_upwards [hCount] with ω hω
    apply propext
    change (N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B) ↔
      (((∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B)
    rw [hω, Finset.sum_range_succ]
    constructor
    · rintro ⟨⟨hl, hu⟩, hr, hb⟩
      exact ⟨⟨hl, by linarith⟩, hb⟩
    · rintro ⟨⟨hl, hr⟩, hb⟩
      exact ⟨⟨hl, by linarith⟩, by linarith, hb⟩
  have hJoint :=
    AvramDividend.Classical.chat06_indexed_iid_past_residual_full_future_joint_law
      τ hτ hiid n Z rfl age hAge D B hD hB μ hLaw
      hNonneg hTail t ht
  have h0 := hEvent 0
  simp only [add_zero] at h0
  calc
    P {ω | N ω = n ∧
      t < τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω) ∧
      (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} =
      P {ω | ((∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
        clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} :=
      measure_congr hAE
    _ = P {ω | (Z ω ∈ D ∧ age (Z ω) + t < τ n ω) ∧
        (fun j : ℕ => τ (n + 1 + j) ω) ∈ B} := by
      change P ({ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
          clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} ∩
          {ω | (fun j : ℕ => τ (n + 1 + j) ω) ∈ B}) =
        P ({ω | Z ω ∈ D ∧ age (Z ω) + t < τ n ω} ∩
          {ω | (fun j : ℕ => τ (n + 1 + j) ω) ∈ B})
      rw [hEvent t]
    _ = (P {ω | Z ω ∈ D ∧ age (Z ω) < τ n ω} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := hJoint
    _ = (P {ω | N ω = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
      have hBase :
          P {ω | N ω = n} =
          P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
            clock < ∑ i ∈ Finset.range (n + 1), τ i ω} :=
        measure_congr hCount
      rw [h0, ← hBase]
