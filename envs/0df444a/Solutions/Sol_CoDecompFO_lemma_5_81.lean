-- Prove2me | solution 1 for CoDecompFO.lemma_5_81
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:07:33.940158+00:00
-- url     : https://prove2.me/submissions/a39577a0-7264-4c53-8c12-790cd5deba13

import Mathlib
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

theorem natCard_set (α : Type) [Finite α] : Nat.card (Set α) = 2 ^ Nat.card α := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_set]

theorem card_atom (σ : Sig) (k : ℕ) : Nat.card (σ.Atom k) = ∑ i, k ^ σ.ar i := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- Lemma 5.81 for every number `k` of head points. -/
theorem l581_aux (σ : Sig) (n w k : ℕ) (hn : n ≤ w) :
    ∀ m : ℕ, Finite (HTh σ (Fin n) k m) ∧
      Nat.card (HTh σ (Fin n) k m) ≤ tower w (∑ i, k ^ σ.ar i) m := by
  intro m
  induction m with
  | zero =>
    show Finite (Set (Set (σ.Atom k))) ∧
      Nat.card (Set (Set (σ.Atom k))) ≤ 2 ^ 2 ^ (∑ i, k ^ σ.ar i)
    refine ⟨inferInstance, ?_⟩
    rw [natCard_set, natCard_set, card_atom]
  | succ m ih =>
    obtain ⟨hfin, hcard⟩ := ih
    show Finite (Fin n → Set (Set (Fin n × HTh σ (Fin n) k m))) ∧
      Nat.card (Fin n → Set (Set (Fin n × HTh σ (Fin n) k m))) ≤
        2 ^ (w * 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m))
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_fun, natCard_set, natCard_set, Nat.card_prod, Nat.card_fin, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    calc 2 ^ (n * Nat.card (HTh σ (Fin n) k m)) * n
        ≤ 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m) * w :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hn hcard)) hn
      _ = w * 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m) := Nat.mul_comm _ _

end CoDecompFO

theorem solution (σ : CoDecompFO.Sig) (n w ℓ m : ℕ) (hn : n ≤ w) :
    Finite (CoDecompFO.HTh σ (Fin n) (2 * ℓ) m) ∧
      Nat.card (CoDecompFO.HTh σ (Fin n) (2 * ℓ) m) ≤
        CoDecompFO.tower w (∑ i, (2 * ℓ) ^ σ.ar i) m :=
  CoDecompFO.l581_aux σ n w (2 * ℓ) hn m
