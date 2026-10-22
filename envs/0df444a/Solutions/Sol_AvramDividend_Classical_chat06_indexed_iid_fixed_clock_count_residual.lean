-- Prove2me | solution 1 for AvramDividend.Classical.chat06_indexed_iid_fixed_clock_count_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:16:43.264995+00:00
-- url     : https://prove2.me/submissions/3cf0b238-f726-4eee-9346-ef43dd5f2a4e

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_independent_past_event_exponential_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace AvramChat06

/-- The fixed-clock event of exactly n arrivals has exponential
residual survival. The age is the clock minus the preceding arrival,
clipped at zero outside the count event. -/
theorem indexed_iid_fixed_clock_count_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) (clock t : ℝ)
    (ht : 0 ≤ t)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} =
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock < ∑ i ∈ Finset.range (n + 1), τ i ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
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
      constructor
      · exact hd
      · linarith
    · rintro ⟨hd, hr⟩
      constructor
      · exact hd
      · rw [max_eq_left (sub_nonneg.mpr hd)]
        linarith
  have hZMeas : Measurable Z := by
    unfold Z
    apply measurable_pi_lambda
    intro i
    by_cases hi : i < n
    · simpa [hi] using hτ i
    · simp [hi]
  have hInd : IndepFun Z (τ n) P := by
    have hSuffix :=
      AvramDividend.Classical.chat06_masked_iid_prefix_full_suffix_independence
        τ hτ hiid n
    have h0 := hSuffix.comp measurable_id
      (measurable_pi_apply (0 : ℕ))
    have hZeq : Z = (fun ω i => if h : i < n then τ i ω else 0) := rfl
    rw [hZeq]
    simpa [Function.comp_def] using h0
  have hResidual :=
    AvramDividend.Classical.chat06_independent_past_event_exponential_residual
      Z (τ n) age hZMeas (hτ n) hAge hInd D hD
      hNonneg hTail t ht
  have hEvent0 := hEvent 0
  simp only [add_zero] at hEvent0
  rw [hEvent t, hEvent0] at hResidual
  exact hResidual

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P) (n : ℕ) (clock t : ℝ)
    (ht : 0 ≤ t)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock + t < ∑ i ∈ Finset.range (n + 1), τ i ω} =
    P {ω | (∑ i ∈ Finset.range n, τ i ω) ≤ clock ∧
      clock < ∑ i ∈ Finset.range (n + 1), τ i ω} *
        ENNReal.ofReal (Real.exp (-t)) := by
  exact indexed_iid_fixed_clock_count_residual
    τ hτ hiid n clock t ht hTail
