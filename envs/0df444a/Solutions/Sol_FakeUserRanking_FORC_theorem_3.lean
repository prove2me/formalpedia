-- Prove2me | solution 1 for FakeUserRanking.FORC.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:33:16.337889+00:00
-- url     : https://prove2.me/submissions/ee2756a7-a7f2-4632-9dbe-bea36f2c0305
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent
import Theorems.Thm_FakeUserRanking_FORC_lemma_1
import Theorems.Thm_FakeUserRanking_FORC_lemma_9
import Theorems.Thm_FakeUserRanking_FORC_lemma_8_goodEvent_bound

open FakeUserRanking.FORC

namespace SolThm3

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma levelW_sum (L : ℕ) (hL : 1 ≤ L) : ∑ k : Fin L, levelW L k = 1 := by
  unfold levelW
  rw [Fin.sum_univ_eq_sum_range (fun m => if m = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1)
    else (1 / 2 : ℝ) ^ (m + 1)) L]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have : ∀ i ∈ Finset.range L', (1 / 2 : ℝ) ^ (1 + i + 1) = (1 / 2 : ℝ) ^ (i + 1 + 1) := by
    intro i _; rw [show 1 + i + 1 = i + 1 + 1 by ring]
  rw [Finset.sum_congr rfl this]
  ring

lemma expect_sum {n L : ℕ} {ι : Type*} (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ)
    (s : Finset ι) (f : ι → (Fin T → Step n L) → ℝ) :
    expect inst P A T (fun τ => ∑ i ∈ s, f i τ) =
      ∑ i ∈ s, expect inst P A T (fun τ => f i τ) := by
  unfold expect
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_const_mul {n L : ℕ} (inst : Instance n) (P : Adversary n) (A : Alg n L) (T : ℕ)
    (c : ℝ) (g : (Fin T → Step n L) → ℝ) :
    expect inst P A T (fun τ => c * g τ) = c * expect inst P A T g := by
  unfold expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => by ring)

end SolThm3

open Classical in
theorem solution :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
        regret inst P (forc n T tb fb) T ≤
          C * (((n : ℝ) ^ 2 * F + Real.log T) *
            ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, Real.log ((n : ℝ) * T) / gap inst j i) := by
  refine ⟨300, ?_⟩
  intro n T F hn hT inst hμ P hP tb htb fb
  set A := forc n T tb fb
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun h k => SolThm3.levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun h => SolThm3.levelW_sum _ hL
  have h1 := lemma_1 T F A hw_nonneg hw_sum inst hμ P hP
  have h9 := lemma_9 n T F hn hT inst hμ P hP tb htb fb
  have h8 := lemma_8_goodEvent_bound n T F hn hT inst hμ P hP tb htb fb
  set S : (Fin T → Step n (numLevels T)) → ℝ := fun τ =>
    ∑ j : Fin n, ∑ i ∈ Finset.Ioi j, gap inst j i *
      ∑ t : Fin T, (if feedbackEvent A τ t j i then (1 : ℝ) else 0)
  have hpart : expect inst P A T S =
      expect inst P A T (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) * S τ) +
      expect inst P A T (fun τ => (if goodEvent inst F tb fb τ then 0 else 1) * S τ) := by
    unfold expect
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hG : goodEvent inst F tb fb τ <;> simp [hG]
  have hfubini : (∑ t : Fin T, ∑ j : Fin n, ∑ i ∈ Finset.Ioi j,
        gap inst j i * prob inst P A T (fun τ => feedbackEvent A τ t j i)) =
      expect inst P A T S := by
    unfold S prob
    simp only [SolThm3.expect_sum, SolThm3.expect_const_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact Finset.sum_comm
  linarith
