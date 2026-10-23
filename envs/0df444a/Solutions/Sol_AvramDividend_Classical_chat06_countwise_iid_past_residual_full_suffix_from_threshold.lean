-- Prove2me | solution 1 for AvramDividend.Classical.chat06_countwise_iid_past_residual_full_suffix_from_threshold
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:22:09.283307+00:00
-- url     : https://prove2.me/submissions/8732ce06-3632-400a-b38b-0aa630b21f4f

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_prefix_representation_implies_past_independence
import Theorems.Thm_AvramDividend_Classical_chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- A countwise measurable representation of the observed past gives
joint independence of its events from exponential residual survival
and the whole selected future IID waiting-time suffix. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThreshold : ∀ ω u k,
      k < N ω u ↔ (∑ i ∈ Finset.range (k + 1), τ i ω) ≤ u)
    (clock : ℝ) (hclock : 0 ≤ clock)
    (hN : Measurable (fun ω => N ω clock))
    (H : Set Ω) (hH : MeasurableSet H)
    (hRep : ∀ n : ℕ, ∃ Q : Set (ℕ → ℝ),
      MeasurableSet Q ∧
      (fun ω : Ω => ω ∈ H ∧ N ω clock = n) =ᵐ[P]
        (fun ω : Ω =>
          (fun i : ℕ => if i < n then τ i ω else 0) ∈ Q ∧
          N ω clock = n))
    (t : ℝ) (ht : 0 ≤ t) (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n, HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (B : Set (ℕ → ℝ)) (hB : MeasurableSet B)
    (hTail : ∀ n (u : ℝ), 0 ≤ u →
      P {ω | u < τ n ω} = ENNReal.ofReal (Real.exp (-u))) :
    P {ω | ω ∈ H ∧
      t < τ (N ω clock) ω -
        (clock - ∑ i ∈ Finset.range (N ω clock), τ i ω) ∧
      (fun j : ℕ => τ (N ω clock + 1 + j) ω) ∈ B} =
      (P H * ENNReal.ofReal (Real.exp (-t))) * μ B := by
  let Z (n : ℕ) (ω : Ω) (i : ℕ) : ℝ :=
    if i < n then τ i ω else 0
  let F (n : ℕ) (ω : Ω) : ℝ :=
    τ n ω - (clock - ∑ i ∈ Finset.range n, τ i ω)
  let G (n : ℕ) (ω : Ω) (j : ℕ) : ℝ :=
    τ (n + 1 + j) ω
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    exact (hτ n).sub
      (measurable_const.sub
        (Finset.measurable_sum _ fun i _ => hτ i))
  have hGm : ∀ n, Measurable (G n) := by
    intro n
    exact measurable_pi_iff.mpr (fun j => hτ (n + 1 + j))
  have hFactor (n : ℕ) (Q : Set (ℕ → ℝ))
      (hQ : MeasurableSet Q) :
      P {ω | Z n ω ∈ Q ∧ N ω clock = n ∧
        t < F n ω ∧ G n ω ∈ B} =
        (P {ω | Z n ω ∈ Q ∧ N ω clock = n} *
          ENNReal.ofReal (Real.exp (-t))) * μ B := by
    have hFixed :=
      AvramDividend.Classical.chat06_iid_fixed_count_prefix_event_residual_future_joint_from_threshold
        τ hτ hiid n N hThreshold clock hclock (Z n) rfl Q hQ
        t ht μ (hLaw n) B hB (hTail n)
    simpa only [F, G, and_assoc] using hFixed
  have hJoint :=
    AvramDividend.Classical.chat06_countwise_prefix_representation_implies_past_independence
      (fun ω => N ω clock) hN Z H hH F hFm G hGm
      B hB t (ENNReal.ofReal (Real.exp (-t))) (μ B)
      hRep hFactor
  simpa only [F, G, Nat.add_assoc] using hJoint
