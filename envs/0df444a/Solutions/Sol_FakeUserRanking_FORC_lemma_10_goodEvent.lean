-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_10_goodEvent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:22:15.665838+00:00
-- url     : https://prove2.me/submissions/11941edd-e21c-458f-b7c2-88ec1542f457

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_lemma_10_pair

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolLemma10GoodEvent

open Classical in
lemma expect_double_sum {n L T : ℕ} (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (E : (Fin T → Step n L) → Prop) :
    expect inst P A T
      (fun τ => (if E τ then 1 else 0) *
        ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
          ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) =
    ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
      expect inst P A T
        (fun τ => (if E τ then 1 else 0) *
          ∑ t : Fin T, (if feedbackEvent A τ t j i then 1 else 0)) := by
  unfold expect
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro τ _
  apply Finset.sum_congr rfl; intro t _
  ring

end SolLemma10GoodEvent

open Classical in
theorem solution :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
              ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by
  obtain ⟨C, hC⟩ := lemma_10_pair
  refine ⟨C, fun n T F hn hT inst hμ P hP tb htb fb => ?_⟩
  rw [SolLemma10GoodEvent.expect_double_sum]
  calc (∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
          expect inst P (forc n T tb fb) T
            (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
              ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)))
      ≤ ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            (Real.log ((n : ℝ) * T) / gap inst j i)) := by
        apply Finset.sum_le_sum; intro j _
        apply Finset.sum_le_sum; intro i hi
        have hji : j < i := Finset.mem_Ioi.mp hi
        have hgap : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
        have hgap0 : gap inst j i ≠ 0 := hgap.ne'
        have hpair := hC n T F hn hT inst hμ P hP tb htb fb j i hji
        calc gap inst j i *
              expect inst P (forc n T tb fb) T
                (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
                  ∑ t : Fin T, (if feedbackEvent (forc n T tb fb) τ t j i then 1 else 0))
            ≤ gap inst j i * (C * (((n : ℝ) ^ 2 * F + Real.log T) *
                (Real.log ((n : ℝ) * T) / gap inst j i ^ 2))) :=
              mul_le_mul_of_nonneg_left hpair hgap.le
          _ = C * (((n : ℝ) ^ 2 * F + Real.log T) *
                (Real.log ((n : ℝ) * T) / gap inst j i)) := by
              field_simp
    _ = C * (((n : ℝ) ^ 2 * F + Real.log T) *
          ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by
        simp only [Finset.mul_sum]
