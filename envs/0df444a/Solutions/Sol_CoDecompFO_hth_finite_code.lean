-- Prove2me | solution 1 for CoDecompFO.hth_finite_code
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:47:15.275943+00:00
-- url     : https://prove2.me/submissions/017d0f95-3546-44fe-bbee-370e6a9ef6ba

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

open FirstOrder
open CoDecompFO

private theorem natCard_set_aux (α : Type) [Finite α] : Nat.card (Set α) = 2 ^ Nat.card α := by
  classical
  haveI := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_set]

private theorem card_atom_aux (σ : Sig) (k : ℕ) : Nat.card (σ.Atom k) = ∑ i, k ^ σ.ar i := by
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

private theorem l581_local (σ : Sig) (n w k : ℕ) (hn : n ≤ w) :
    ∀ m : ℕ, Finite (HTh σ (Fin n) k m) ∧
      Nat.card (HTh σ (Fin n) k m) ≤ tower w (∑ i, k ^ σ.ar i) m := by
  intro m
  induction m with
  | zero =>
    show Finite (Set (Set (σ.Atom k))) ∧
      Nat.card (Set (Set (σ.Atom k))) ≤ 2 ^ 2 ^ (∑ i, k ^ σ.ar i)
    refine ⟨inferInstance, ?_⟩
    rw [natCard_set_aux, natCard_set_aux, card_atom_aux]
  | succ m ih =>
    obtain ⟨hfin, hcard⟩ := ih
    show Finite (Fin n → Set (Set (Fin n × HTh σ (Fin n) k m))) ∧
      Nat.card (Fin n → Set (Set (Fin n × HTh σ (Fin n) k m))) ≤
        2 ^ (w * 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m))
    refine ⟨inferInstance, ?_⟩
    rw [Nat.card_fun, natCard_set_aux, natCard_set_aux, Nat.card_prod, Nat.card_fin, ← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    calc 2 ^ (n * Nat.card (HTh σ (Fin n) k m)) * n
        ≤ 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m) * w :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul hn hcard)) hn
      _ = w * 2 ^ (w * tower w (∑ i, k ^ σ.ar i) m) := Nat.mul_comm _ _

/-- Every finite type of reduced hypotheticals over a bag has an injective numeric enumeration,
bounded by the explicit tower of Lemma 5.81. -/
theorem solution (σ : Sig) (n w ℓ m : ℕ) (hn : n ≤ w) :
    ∃ code : HTh σ (Fin n) (2 * ℓ) m → ℕ,
      Function.Injective code ∧
      ∀ H, code H ≤ tower w (∑ i, (2 * ℓ) ^ σ.ar i) m := by
  obtain ⟨hfin, hcard⟩ := l581_local σ n w (2 * ℓ) hn m
  letI : Finite (HTh σ (Fin n) (2 * ℓ) m) := hfin
  letI : Fintype (HTh σ (Fin n) (2 * ℓ) m) := Fintype.ofFinite _
  let e := Fintype.equivFin (HTh σ (Fin n) (2 * ℓ) m)
  refine ⟨fun H => (e H).val, ?_, ?_⟩
  · intro H₁ H₂ h
    exact e.injective (Fin.ext h)
  · intro H
    have hc : Fintype.card (HTh σ (Fin n) (2 * ℓ) m) ≤
        tower w (∑ i, (2 * ℓ) ^ σ.ar i) m := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    exact Nat.le_of_lt (lt_of_lt_of_le (e H).isLt hc)
