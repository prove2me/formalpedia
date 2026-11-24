-- Prove2me | solution 1 for FairShareAlmostAll.Slack.capping_preserves_target
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:36:31.069214+00:00
-- url     : https://prove2.me/submissions/ff265323-96c4-43ad-9480-30cb9ad2431f

import Mathlib
import Definitions.Def_AnyPriceShare_Bidding_Basic
import Definitions.Def_FairShareAlmostAll_Slack_FiniteAllocation
import Definitions.Def_FairShareAlmostAll_Slack_Instance
import Definitions.Def_FairShareAlmostAll_Slack_Buckets

open FairShareAlmostAll.Slack

namespace CappingAux

/-- Linearity: the expected weight of a random bundle is the marginal-weighted sum. -/
theorem expectation_sum {m : ℕ} (Q : FiniteLaw (Finset (Fin m))) (c : Fin m → ℝ) :
    expectation Q (fun P => ∑ g ∈ P, c g) =
      ∑ g, c g * probability Q (fun P => g ∈ P) := by
  classical
  unfold expectation
  calc ∑ P, Q.weight P * ∑ g ∈ P, c g
      = ∑ P, ∑ g, (if g ∈ P then Q.weight P * c g else 0) := by
        apply Finset.sum_congr rfl
        intro P _
        rw [show P = Finset.univ.filter (· ∈ P) by ext; simp, Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro g _
        simp
    _ = ∑ g, ∑ P, (if g ∈ P then Q.weight P * c g else 0) := Finset.sum_comm
    _ = ∑ g, c g * probability Q (fun P => g ∈ P) := by
        apply Finset.sum_congr rfl
        intro g _
        unfold probability
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro P _
        split_ifs <;> ring

end CappingAux

open CappingAux in
theorem solution {n m : ℕ} (X : Instance n m) (q : ℕ) (h : ConstructionAssumptions X q)
    (i : Fin n) (hi : i ∈ active X) (D : FiniteLaw (Finset (Fin m)))
    (hD : certificate (X.value i) (X.entitlement i) (target X i) D) :
    (∀ P, 0 < D.weight P → 1 ≤ cappedValue X i P) ∧
      1 / X.entitlement i ≤ cappedValue X i Finset.univ := by
  classical
  have hτ : 0 < target X i := by
    unfold active at hi
    exact (Finset.mem_filter.mp hi).2
  have hcap : ∀ g, 0 ≤ capped X i g := by
    intro g
    unfold capped
    exact le_min (div_nonneg (X.value_nonneg i g) hτ.le) zero_le_one
  have hcv : ∀ P, cappedValue X i P = ∑ g ∈ P, capped X i g := fun P => rfl
  have part1 : ∀ P, 0 < D.weight P → 1 ≤ cappedValue X i P := by
    intro P hP
    have hval := hD.1 P hP
    rw [hcv]
    by_cases hbig : ∃ g ∈ P, 1 ≤ X.value i g / target X i
    · obtain ⟨g, hg, hg1⟩ := hbig
      have : capped X i g = 1 := by unfold capped; exact min_eq_right hg1
      calc (1 : ℝ) = capped X i g := this.symm
        _ ≤ ∑ g ∈ P, capped X i g :=
          Finset.single_le_sum (fun g _ => hcap g) hg
    · push_neg at hbig
      have heq : ∑ g ∈ P, capped X i g = (∑ g ∈ P, X.value i g) / target X i := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro g hg
        unfold capped
        exact min_eq_left (hbig g hg).le
      rw [heq, le_div_iff₀ hτ, one_mul]
      exact hval
  refine ⟨part1, ?_⟩
  have hb := X.entitlement_pos i
  have hexp : expectation D (fun P => ∑ g ∈ P, capped X i g) ≤
      X.entitlement i * cappedValue X i Finset.univ := by
    rw [expectation_sum, hcv, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro g _
    rw [mul_comm (X.entitlement i)]
    exact mul_le_mul_of_nonneg_left (hD.2 g) (hcap g)
  have hone : 1 ≤ expectation D (fun P => ∑ g ∈ P, capped X i g) := by
    unfold expectation
    rw [← D.total]
    apply Finset.sum_le_sum
    intro P _
    rcases (D.nonneg P).lt_or_eq with hP | hP
    · have := part1 P hP
      rw [hcv] at this
      nlinarith
    · rw [← hP]
      simp
  rw [div_le_iff₀ hb]
  linarith
