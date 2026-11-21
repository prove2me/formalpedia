-- Prove2me | solution 1 for Champernowne.card_Ico_filter_div_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:04.552579+00:00
-- url     : https://prove2.me/submissions/eaca7d2d-32c3-4058-aa0a-5179ad3c3612

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {A B p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : d < q) (hA : p * q ∣ A) (hB : p * q ∣ B) :
    ((Finset.Ico A B).filter (fun n => n / p % q = d)).card
      = (B / (p * q) - A / (p * q)) * p := by
  have hpq : 0 < p * q := Nat.mul_pos hp hq
  have hdpr : ∀ r < p, d * p + r < p * q := by
    intro r hr
    calc d * p + r < (d + 1) * p := by rw [Nat.succ_mul]; omega
    _ ≤ q * p := Nat.mul_le_mul_right p (by omega)
    _ = p * q := Nat.mul_comm q p
  rw [show (B / (p * q) - A / (p * q)) * p
      = ((Finset.Ico (A / (p * q)) (B / (p * q))) ×ˢ Finset.range p).card by
    rw [Finset.card_product, Nat.card_Ico, Finset.card_range]]
  apply Finset.card_nbij' (i := fun n => (n / (p * q), n % p))
    (j := fun x => x.1 * (p * q) + d * p + x.2)
  · -- forward map lands in the box
    intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, _⟩ := hn
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range]
    refine ⟨⟨Nat.div_le_div_right h1, ?_⟩, Nat.mod_lt n hp⟩
    rw [Nat.div_lt_iff_lt_mul hpq, Nat.div_mul_cancel hB]
    exact h2
  · -- inverse map lands in the filtered interval
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range] at hx
    obtain ⟨⟨hh1, hh2⟩, hr⟩ := hx
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · calc A = A / (p * q) * (p * q) := (Nat.div_mul_cancel hA).symm
      _ ≤ h * (p * q) := Nat.mul_le_mul_right _ hh1
      _ ≤ h * (p * q) + d * p + r := by
          exact le_add_right (le_add_right le_rfl)
    · calc h * (p * q) + d * p + r
          = h * (p * q) + (d * p + r) := by rw [Nat.add_assoc]
      _ < h * (p * q) + p * q := Nat.add_lt_add_left (hdpr r hr) _
      _ = (h + 1) * (p * q) := by rw [Nat.succ_mul]
      _ ≤ B / (p * q) * (p * q) := Nat.mul_le_mul_right _ (by omega)
      _ = B := Nat.div_mul_cancel hB
    · have hrew : h * (p * q) + d * p + r = r + p * (q * h + d) := by ring
      rw [hrew, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add,
        Nat.mul_add_mod, Nat.mod_eq_of_lt hd]
  · -- left inverse on the filtered interval
    intro n hn
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_Ico] at hn
    obtain ⟨-, hd'⟩ := hn
    change n / (p * q) * (p * q) + d * p + n % p = n
    rw [← hd']
    calc n / (p * q) * (p * q) + n / p % q * p + n % p
        = (q * (n / p / q) + n / p % q) * p + n % p := by
          rw [← Nat.div_div_eq_div_mul]; ring
    _ = n / p * p + n % p := by rw [Nat.div_add_mod]
    _ = n := by rw [Nat.mul_comm]; exact Nat.div_add_mod n p
  · -- right inverse on the box
    rintro ⟨h, r⟩ hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_Ico,
      Finset.mem_range] at hx
    obtain ⟨-, hr⟩ := hx
    have h1 : (h * (p * q) + d * p + r) / (p * q) = h := by
      have hrew : h * (p * q) + d * p + r = d * p + r + (p * q) * h := by ring
      rw [hrew, Nat.add_mul_div_left _ _ hpq, Nat.div_eq_of_lt (hdpr r hr),
        Nat.zero_add]
    have h2 : (h * (p * q) + d * p + r) % p = r := by
      have hrew : h * (p * q) + d * p + r = p * (h * q + d) + r := by ring
      rw [hrew, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
    exact Prod.ext h1 h2
end Champernowne
