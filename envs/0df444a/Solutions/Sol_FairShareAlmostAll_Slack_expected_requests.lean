-- Prove2me | solution 1 for FairShareAlmostAll.Slack.expected_requests
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:13:17.648803+00:00
-- url     : https://prove2.me/submissions/9faba21c-b47e-4b95-8455-ef60740f0a55

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

open FairShareAlmostAll.Slack

namespace ExpectedRequestsAux

/-- Linearity: the expected weight of `P ∩ T` is the marginal-weighted sum over `T`. -/
theorem expectation_sum_inter {m : ℕ} (Q : FiniteLaw (Finset (Fin m))) (T : Finset (Fin m))
    (c : Fin m → ℝ) :
    expectation Q (fun P => ∑ g ∈ P ∩ T, c g) =
      ∑ g ∈ T, c g * probability Q (fun P => g ∈ P) := by
  classical
  unfold expectation
  calc ∑ P, Q.weight P * ∑ g ∈ P ∩ T, c g
      = ∑ P, ∑ g ∈ T, (if g ∈ P then Q.weight P * c g else 0) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [show P ∩ T = T.filter (· ∈ P) by ext; simp [and_comm], Finset.mul_sum,
          Finset.sum_filter]
    _ = ∑ g ∈ T, ∑ P, (if g ∈ P then Q.weight P * c g else 0) := Finset.sum_comm
    _ = ∑ g ∈ T, c g * probability Q (fun P => g ∈ P) := by
        apply Finset.sum_congr rfl
        intro g _
        unfold probability
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P _
        split_ifs <;> ring

/-- With nonnegative weights and marginals at most `a`, the expected weight of `P ∩ T` is at most
`a` times the weight of `T`. -/
theorem expectation_sum_inter_le {m : ℕ} (Q : FiniteLaw (Finset (Fin m))) (T : Finset (Fin m))
    (c : Fin m → ℝ) (hc : ∀ g, 0 ≤ c g) (a : ℝ)
    (hQ : ∀ g, probability Q (fun P => g ∈ P) ≤ a) :
    expectation Q (fun P => ∑ g ∈ P ∩ T, c g) ≤ a * ∑ g ∈ T, c g := by
  rw [expectation_sum_inter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  rw [mul_comm a]
  exact mul_le_mul_of_nonneg_left (hQ g) (hc g)

theorem expectation_const_mul {α : Type} [Fintype α] (Q : FiniteLaw α) (k : ℝ) (f : α → ℝ) :
    expectation Q (fun x => k * f x) = k * expectation Q f := by
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_div {α : Type} [Fintype α] (Q : FiniteLaw α) (k : ℝ) (f : α → ℝ) :
    expectation Q (fun x => f x / k) = expectation Q f / k := by
  unfold expectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_zero {α : Type} [Fintype α] (Q : FiniteLaw α) :
    expectation Q (fun _ => (0 : ℝ)) = 0 := by
  unfold expectation
  simp

end ExpectedRequestsAux

open ExpectedRequestsAux in
theorem solution {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) (a : ℝ) (ha : 0 ≤ a)
    (Q : FiniteLaw (Finset (Fin m)))
    (hQ : ∀ g, probability Q (fun P => g ∈ P) ≤ a) :
    expectation Q (tailFraction X q i) ≤ a ∧
    ∀ j ∈ Finset.Icc 2 (bucketCount q m),
      expectation Q (request X q j i) ≤ a * (bucket q m j).card := by
  classical
  have htarget : 0 < target X i := by
    unfold active at hi
    exact (Finset.mem_filter.mp hi).2
  have hcap : ∀ g, 0 ≤ capped X i g := by
    intro g
    unfold capped
    exact le_min (div_nonneg (X.value_nonneg i g) htarget.le) zero_le_one
  have htail : expectation Q (tailFraction X q i) ≤ a := by
    by_cases hK : 0 < cappedValue X i (tail X q i)
    · have hfun : tailFraction X q i = fun P =>
          (∑ g ∈ P ∩ tail X q i, capped X i g) / cappedValue X i (tail X q i) := by
        funext P
        unfold tailFraction
        rw [if_pos hK]
        rfl
      rw [hfun, expectation_div, div_le_iff₀ hK]
      have := expectation_sum_inter_le Q (tail X q i) (capped X i) hcap a hQ
      exact this
    · have hfun : tailFraction X q i = fun _ => 0 := by
        funext P
        unfold tailFraction
        rw [if_neg hK]
      rw [hfun, expectation_zero]
      exact ha
  refine ⟨htail, ?_⟩
  intro j _
  by_cases hj : j ≤ cutoff X q i
  · have hfun : request X q j i = fun P => ∑ g ∈ P ∩ bucket q m j, (fun _ => (1 : ℝ)) g := by
      funext P
      unfold request
      rw [if_pos hj]
      simp
    rw [hfun]
    have := expectation_sum_inter_le Q (bucket q m j) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) a hQ
    simpa using this
  · have hfun : request X q j i = fun P => ((bucket q m j).card : ℝ) * tailFraction X q i P := by
      funext P
      unfold request
      rw [if_neg hj]
    rw [hfun, expectation_const_mul, mul_comm a]
    exact mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
