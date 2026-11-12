-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_countwise_iid_residual_future_joint_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:47:29.113735+00:00
-- url     : https://prove2.me/submissions/761a3ba6-b43d-4649-b78a-12e6abaa3156

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_countwise_prefix_representation_implies_past_independence
import Theorems.Thm_AvramDividend_Classical_avram_a06_fixed_count_residual_future_joint_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

/-- Sum the a.e fixed-count residual factorisations over the observed count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℝ → ℕ)
    (hThresholdAE : ∀ᵐ ω ∂P, ∀ u k,
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
      AvramDividend.Classical.avram_a06_fixed_count_residual_future_joint_ae
        τ hτ hiid n N hThresholdAE clock hclock (Z n) rfl Q hQ
        t ht μ (hLaw n) B hB (hTail n)
    simpa only [F, G, and_assoc] using hFixed
  have hJoint :=
    AvramDividend.Classical.chat06_countwise_prefix_representation_implies_past_independence
      (fun ω => N ω clock) hN Z H hH F hFm G hGm
      B hB t (ENNReal.ofReal (Real.exp (-t))) (μ B)
      hRep hFactor
  simpa only [F, G, Nat.add_assoc] using hJoint
