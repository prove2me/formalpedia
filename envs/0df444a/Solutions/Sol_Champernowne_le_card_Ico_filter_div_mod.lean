-- Prove2me | solution 1 for Champernowne.le_card_Ico_filter_div_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:31.999992+00:00
-- url     : https://prove2.me/submissions/dd806c85-b6e1-42b8-af1e-717ab072d2fc

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {A t p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) :
    t / (p * q) * p
      ≤ ((Finset.Ico A (A + t)).filter (fun n => n / p % q = d)).card := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hdpr : ∀ r < p, d * p + r < p * q := by
    intro r hr
    calc d * p + r < (d + 1) * p := by rw [Nat.succ_mul]; omega
    _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
    _ = p * q := Nat.mul_comm q p
  rw [show t / (p * q) * p
      = (Finset.range (t / (p * q)) ×ˢ Finset.range p).card by
    rw [Finset.card_product, Finset.card_range, Finset.card_range]]
  apply Finset.card_le_card_of_injOn
    (fun x => A + (x.1 * (p * q) + d * p + x.2))
  · -- the map lands in the filtered interval
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx
    obtain ⟨hh, hr⟩ := hx
    have hlt : h * (p * q) + d * p + r < t :=
      calc h * (p * q) + d * p + r
          < h * (p * q) + p * q := by have := hdpr r hr; omega
      _ = (h + 1) * (p * q) := by ring
      _ ≤ t / (p * q) * (p * q) := Nat.mul_le_mul_right _ (by omega)
      _ ≤ t := Nat.div_mul_le_self t (p * q)
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
    refine ⟨⟨Nat.le_add_right _ _, by omega⟩, ?_⟩
    obtain ⟨a, rfl⟩ := hA
    have hrew : p * q * a + (h * (p * q) + d * p + r)
        = r + p * (d + q * (a + h)) := by ring
    rw [hrew, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  · -- injectivity: extract `h` and `r` back out by div/mod
    have hext : ∀ h r, r < p →
        (h * (p * q) + d * p + r) / (p * q) = h
          ∧ (h * (p * q) + d * p + r) % p = r := by
      intro h r hr
      constructor
      · have hrew : h * (p * q) + d * p + r = d * p + r + (p * q) * h := by
          ring
        rw [hrew, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt (hdpr r hr),
          Nat.zero_add]
      · have hrew : h * (p * q) + d * p + r = p * (h * q + d) + r := by ring
        rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    rintro ⟨h₁, r₁⟩ hx₁ ⟨h₂, r₂⟩ hx₂ heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe,
      Finset.mem_range] at hx₁ hx₂
    have hcancel : h₁ * (p * q) + d * p + r₁ = h₂ * (p * q) + d * p + r₂ :=
      Nat.add_left_cancel heq
    have hh : h₁ = h₂ := by
      rw [← (hext h₁ r₁ hx₁.2).1, ← (hext h₂ r₂ hx₂.2).1, hcancel]
    have hr : r₁ = r₂ := by
      rw [← (hext h₁ r₁ hx₁.2).2, ← (hext h₂ r₂ hx₂.2).2, hcancel]
    exact Prod.ext hh hr
end Champernowne
