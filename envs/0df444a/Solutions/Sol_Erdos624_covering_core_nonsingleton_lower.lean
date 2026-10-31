-- Prove2me | solution 1 for Erdos624.covering_core_nonsingleton_lower
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-30T14:11:04.298254+00:00
-- url     : https://prove2.me/submissions/6dbe3ac6-27ba-4eb3-9700-00db1b72971f

import Mathlib
open Finset
namespace E624R17E
open Finset

lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_two_right]
    have heven : Even (n * (n + 1)) := Nat.even_mul_succ_self n
    have hdiv : 2 ∣ (n + 1) * n := by simpa [Nat.mul_comm] using heven.two_dvd
    simpa [Nat.succ_mul, Nat.mul_comm] using Nat.mul_div_cancel' hdiv

/-- If every `k`-subset of `V` contains some edge from `E` (2-subsets of `V`), then
`#V * (#V - 1) ≤ k * (k - 1) * #E`. -/
theorem no_indep_k_edge_lower {α : Type*} [DecidableEq α]
    (V : Finset α) (E : Finset (Finset α)) (k : ℕ)
    (hk : 2 ≤ k) (hVk : k ≤ #V)
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V)
    (hcov : ∀ S ∈ V.powersetCard k, ∃ e ∈ E, e ⊆ S) :
    #V * (#V - 1) ≤ k * (k - 1) * #E := by
  classical
  set n := #V with hn
  have hge : n.choose k ≤ #E * (n - 2).choose (k - 2) := by
    have hsum : ∑ S ∈ V.powersetCard k, (1 : ℕ) ≤
        ∑ S ∈ V.powersetCard k, #{e ∈ E | e ⊆ S} := by
      apply sum_le_sum
      intro S hS
      obtain ⟨e, heE, heS⟩ := hcov S hS
      have : 0 < #{e' ∈ E | e' ⊆ S} := card_pos.2 ⟨e, mem_filter.2 ⟨heE, heS⟩⟩
      omega
    have hleft : ∑ S ∈ V.powersetCard k, (1 : ℕ) = n.choose k := by
      simp [sum_const, card_powersetCard, n]
    have hright : ∑ S ∈ V.powersetCard k, #{e ∈ E | e ⊆ S} =
        #E * (n - 2).choose (k - 2) := by
      calc ∑ S ∈ V.powersetCard k, #{e ∈ E | e ⊆ S}
          = ∑ S ∈ V.powersetCard k, ∑ e ∈ E, (if e ⊆ S then (1 : ℕ) else 0) := by
              simp [sum_boole]
        _ = ∑ e ∈ E, ∑ S ∈ V.powersetCard k, (if e ⊆ S then (1 : ℕ) else 0) := by
              rw [sum_comm]
        _ = ∑ e ∈ E, #{S ∈ V.powersetCard k | e ⊆ S} := by
              simp [sum_boole]
        _ = ∑ e ∈ E, (n - 2).choose (k - 2) := by
              apply sum_congr rfl
              intro e he
              have ⟨h2, hsub⟩ := hE e he
              simpa [n, h2] using
                (card_filter_powersetCard_subset e V k hsub (by omega))
        _ = #E * (n - 2).choose (k - 2) := by
              simp [sum_const]
    linarith
  have hchoose2 : n.choose 2 ≤ #E * k.choose 2 := by
    by_cases h0 : (n - 2).choose (k - 2) = 0
    · have hle0 : n.choose k ≤ 0 := by simpa [h0] using hge
      have hk0 : n.choose k = 0 := Nat.eq_zero_of_le_zero hle0
      have : n < k := Nat.choose_eq_zero_iff.1 hk0
      exact (Nat.not_lt.2 hVk this).elim
    · have hpos : 0 < (n - 2).choose (k - 2) := Nat.pos_of_ne_zero h0
      have hm := Nat.choose_mul (n := n) (k := k) (s := 2) hk
      have hmul : n.choose k * k.choose 2 ≤ #E * (n - 2).choose (k - 2) * k.choose 2 :=
        Nat.mul_le_mul_right _ hge
      have hrewritten : n.choose 2 * (n - 2).choose (k - 2) ≤
          #E * k.choose 2 * (n - 2).choose (k - 2) := by
        calc n.choose 2 * (n - 2).choose (k - 2)
            = n.choose k * k.choose 2 := hm.symm
          _ ≤ #E * (n - 2).choose (k - 2) * k.choose 2 := hmul
          _ = #E * k.choose 2 * (n - 2).choose (k - 2) := by ring
      exact Nat.le_of_mul_le_mul_right hrewritten hpos
  have hk2 := two_mul_choose_two k
  have hn2 := two_mul_choose_two n
  have h2 := Nat.mul_le_mul_left 2 hchoose2
  calc n * (n - 1)
      = 2 * n.choose 2 := hn2.symm
    _ ≤ 2 * (#E * k.choose 2) := h2
    _ = #E * (2 * k.choose 2) := by ring
    _ = #E * (k * (k - 1)) := by rw [hk2]
    _ = k * (k - 1) * #E := by ring

/-- Covering family of nonsingleton sets ⇒ same numerical bound (via a 2-subset of each). -/
theorem covering_core_nonsingleton_lower {α : Type*} [DecidableEq α]
    (R : Finset α) (G : Finset (Finset α)) (k : ℕ)
    (hk : 2 ≤ k) (hRk : k ≤ #R)
    (hG : ∀ A ∈ G, A ⊆ R ∧ 2 ≤ #A)
    (hcov : ∀ S ∈ R.powersetCard k, ∃ A ∈ G, A ⊆ S) :
    #R * (#R - 1) ≤ k * (k - 1) * #G := by
  classical
  let eOf (A : Finset α) (hA : A ∈ G) : Finset α := by
    have hcard : 2 ≤ #A := (hG A hA).2
    exact Classical.choose (exists_subset_card_eq hcard)
  have heOf (A : Finset α) (hA : A ∈ G) :
      eOf A hA ⊆ A ∧ #(eOf A hA) = 2 := by
    have hcard : 2 ≤ #A := (hG A hA).2
    exact Classical.choose_spec (exists_subset_card_eq hcard)
  let E : Finset (Finset α) :=
    G.attach.image (fun p : {x // x ∈ G} => eOf p.1 p.2)
  have hEcard : #E ≤ #G := by
    have hle : #E ≤ #G.attach := by
      dsimp [E]
      exact card_image_le
    simpa using hle
  have hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ R := by
    intro e he
    obtain ⟨⟨A, hA⟩, _, rfl⟩ := mem_image.1 he
    have ⟨hsub, h2⟩ := heOf A hA
    exact ⟨h2, hsub.trans (hG A hA).1⟩
  have hcovE : ∀ S ∈ R.powersetCard k, ∃ e ∈ E, e ⊆ S := by
    intro S hS
    obtain ⟨A, hA, hAS⟩ := hcov S hS
    refine ⟨eOf A hA, ?_, (heOf A hA).1.trans hAS⟩
    exact mem_image.2 ⟨⟨A, hA⟩, mem_attach _ _, rfl⟩
  have hmain := no_indep_k_edge_lower R E k hk hRk hE hcovE
  exact hmain.trans (Nat.mul_le_mul_left (k * (k - 1)) hEcard)

end E624R17E

namespace Erdos624

theorem covering_core_nonsingleton_lower {α : Type*} [DecidableEq α]
    (R : Finset α) (G : Finset (Finset α)) (k : ℕ)
    (hk : 2 ≤ k) (hRk : k ≤ #R)
    (hG : ∀ A ∈ G, A ⊆ R ∧ 2 ≤ #A)
    (hcov : ∀ S ∈ R.powersetCard k, ∃ A ∈ G, A ⊆ S) :
    #R * (#R - 1) ≤ k * (k - 1) * #G := by
  exact E624R17E.covering_core_nonsingleton_lower R G k hk hRk hG hcov

end Erdos624

open Finset

theorem solution {α : Type*} [DecidableEq α]
    (R : Finset α) (G : Finset (Finset α)) (k : ℕ)
    (hk : 2 ≤ k) (hRk : k ≤ #R)
    (hG : ∀ A ∈ G, A ⊆ R ∧ 2 ≤ #A)
    (hcov : ∀ S ∈ R.powersetCard k, ∃ A ∈ G, A ⊆ S) :
    #R * (#R - 1) ≤ k * (k - 1) * #G :=
  Erdos624.covering_core_nonsingleton_lower R G k hk hRk hG hcov
