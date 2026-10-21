-- Prove2me | solution 1 for AvramDividend.Classical.chat06_post_next_claim_exp_wait_full_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:34:16.7017+00:00
-- url     : https://prove2.me/submissions/1a01944d-7ab9-4241-b400-91394ae4fd90

import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Theorems.Thm_AvramDividend_Classical_chat06_stopped_future_full_joint_law_ae_selection
import Theorems.Thm_AvramDividend_Classical_chat06_masked_iid_prefix_full_suffix_independence
import Theorems.Thm_AvramDividend_Classical_chat06_all_count_events_past_cylinders

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvramChat06

/-- Complete joint law of the iid waits strictly after the next
claim, at a random clock time. Selection of claim index N uses only
the waiting prefix up to and including the selected interarrival.
The residual wait from the clock time to that next claim remains
a separate, unsolved memorylessness obligation. -/
theorem post_next_claim_suffix_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (N : Ω → ℕ) (hN : Measurable N)
    (μ : Measure (ℕ → ℝ))
    (hLaw : ∀ n : ℕ,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω) μ P)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    HasLaw (fun ω (j : ℕ) => τ (N ω + 1 + j) ω) μ P := by
  let past : ℕ → Ω → (ℕ → ℝ) :=
    fun n ω i => if h : i < n + 1 then τ i ω else 0
  let future : ℕ → Ω → (ℕ → ℝ) :=
    fun n ω j => τ (n + 1 + j) ω
  have hFuture : ∀ n, Measurable (future n) := by
    intro n
    apply measurable_pi_lambda
    intro j
    exact hτ (n + 1 + j)
  have hInd : ∀ n, IndepFun (past n) (future n) P := by
    intro n
    simpa only [past, future] using
      (AvramDividend.Classical.chat06_masked_iid_prefix_full_suffix_independence
        τ hτ hiid (n + 1))
  have hStop : ∀ k : ℕ, ∃ S : Set (ℕ → ℝ),
      MeasurableSet S ∧
      (fun ω : Ω => N ω = k) =ᵐ[P]
        (fun ω : Ω => past k ω ∈ S) := by
    simpa only [past, dite_eq_ite] using
      (AvramDividend.Classical.chat06_all_count_events_past_cylinders
        τ N hZero hSucc)
  have hResult :
      HasLaw (fun ω => future (N ω) ω) μ P :=
    AvramDividend.Classical.chat06_stopped_future_full_joint_law_ae_selection
      N hN past future hFuture hInd μ hLaw hStop
  exact hResult


/-- The full unused Exp(1) waiting-time sequence strictly after
the first future claim has the original infinite product law,
without assuming a separate common-law hypothesis for every
deterministic waiting suffix. This does not include the
remaining portion of the currently straddling wait. -/
theorem post_next_claim_suffix_exp_product_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hτlaw : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℕ) (hN : Measurable N)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    HasLaw (fun ω (j : ℕ) => τ (N ω + 1 + j) ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by
  have hLaw : ∀ n : ℕ,
      HasLaw (fun ω (j : ℕ) => τ (n + 1 + j) ω)
        (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by
    intro n
    have hinj : (fun j : ℕ => n + 1 + j).Injective :=
      fun a b h => Nat.add_left_cancel h
    have htail : iIndepFun (fun j => τ (n + 1 + j)) P :=
      iIndepFun.precomp hinj hiid
    have hm : Measurable (fun ω (j : ℕ) => τ (n + 1 + j) ω) :=
      measurable_pi_lambda _ fun j => hτ (n + 1 + j)
    exact htail.hasLaw_infinitePi (fun j => hτlaw (n + 1 + j))
      hm.aemeasurable
  exact post_next_claim_suffix_hasLaw τ hτ hiid N hN
    (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ)))
    hLaw hZero hSucc

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (τ : ℕ → Ω → ℝ) (hτ : ∀ i, Measurable (τ i))
    (hiid : iIndepFun τ P)
    (hτlaw : ∀ i, HasLaw (τ i) (expMeasure 1) P)
    (N : Ω → ℕ) (hN : Measurable N)
    (hZero : ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = 0) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < 1 then τ i ω else 0) ∈ S))
    (hSucc : ∀ n : ℕ, ∃ S : Set (ℕ → ℝ), MeasurableSet S ∧
      (fun ω : Ω => N ω = n + 1) =ᵐ[P]
      (fun ω : Ω =>
        (fun i : ℕ => if i < n + 2 then τ i ω else 0) ∈ S)) :
    HasLaw (fun ω (j : ℕ) => τ (N ω + 1 + j) ω)
      (Measure.infinitePi (fun _ : ℕ => expMeasure (1 : ℝ))) P := by
  exact post_next_claim_suffix_exp_product_law
    τ hτ hiid hτlaw N hN hZero hSucc
