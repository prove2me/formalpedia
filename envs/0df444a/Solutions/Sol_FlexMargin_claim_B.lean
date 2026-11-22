-- Prove2me | solution 1 for FlexMargin.claim_B
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:21:21.686016+00:00
-- url     : https://prove2.me/submissions/6df9ca83-74d0-418e-8596-fefe9430c266

import Mathlib
import Definitions.Def_FlexMargin_windowCount

set_option autoImplicit false

open Finset FlexMargin

namespace FlexMargin.WindowDoubleCount

theorem window_sum {n : ℕ} (cat : Fin n → Fin 2) (τ : Equiv.Perm (Fin n)) (len : ℕ) :
    ∑ s : Fin n, windowCount cat τ s len 1 = len * (univ.filter (fun i => cat i = 1)).card := by
  simp only [windowCount, Finset.card_filter]
  rw [Finset.sum_comm]
  have h : ∀ j ∈ Finset.range len,
      (∑ s : Fin n, if cat (τ (((finRotate n) ^ j) s)) = 1 then 1 else 0) =
        ∑ i : Fin n, if cat i = 1 then 1 else 0 := by
    intro j _
    exact (Equiv.sum_comp ((finRotate n) ^ j) (fun i => if cat (τ i) = 1 then 1 else 0)).trans
      (Equiv.sum_comp τ (fun i => if cat i = 1 then 1 else 0))
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem two_mul_high {n : ℕ} (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card) :
    2 * (univ.filter (fun i => cat i = 1)).card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
    (fun i => cat i = 1)
  have hx : ∀ x : Fin 2, ¬ x = 1 ↔ x = 0 := by decide
  have hneg : univ.filter (fun i => ¬ cat i = 1) = univ.filter (fun i => cat i = 0) := by
    ext i
    simp [hx]
  rw [hneg, ← hbal, Finset.card_univ, Fintype.card_fin] at h
  omega

end FlexMargin.WindowDoubleCount

open FlexMargin.WindowDoubleCount in
theorem solution (n : ℕ) (cat : Fin n → Fin 2)
    (hbal : (univ.filter (fun i => cat i = 1)).card = (univ.filter (fun i => cat i = 0)).card)
    (τ : Equiv.Perm (Fin n)) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ n / 2) :
    (∃ s : Fin n, k ≤ windowCount cat τ s (2 * k) 1) ∧
      (∃ s : Fin n, windowCount cat τ s (2 * k) 1 ≤ k) := by
  have hsum := window_sum cat τ (2 * k)
  have hH := two_mul_high cat hbal
  set H := (univ.filter (fun i => cat i = 1)).card
  have hn : 0 < n := by omega
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, mem_univ _⟩
  have hconst : ∑ _s : Fin n, k = n * k := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  constructor
  · by_contra hc
    push Not at hc
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun s _ => hc s)
    rw [hconst, hsum, ← hH] at hlt
    nlinarith
  · by_contra hc
    push Not at hc
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun s _ => hc s)
    rw [hconst, hsum, ← hH] at hlt
    nlinarith
