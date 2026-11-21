-- Prove2me | solution 1 for Champernowne.block_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:35:30.282453+00:00
-- url     : https://prove2.me/submissions/2902d278-f6df-41f9-8cf5-e41b19d1e6a1

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
theorem _root_.solution {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {w : List ℕ} (hw : ∀ d ∈ w, d < b)
    {j : ℕ} (hjk : j + w.length ≤ m) :
    ((bigDigits b n).drop j).take w.length = w
      ↔ n / b ^ (m - j - w.length) % b ^ w.length
          = Nat.ofDigits b w.reverse := by
  have hml : (Nat.digits b n).length = m := by simpa [bigDigits] using hlen
  have hsub : ((bigDigits b n).drop j).take w.length
      = (((Nat.digits b n).drop (m - j - w.length)).take w.length).reverse := by
    change (((Nat.digits b n).reverse.drop j).take w.length) = _
    rw [List.drop_reverse, hml, List.take_reverse, List.length_take, hml,
      Nat.min_eq_left (by omega)]
    congr 1
    rw [List.take_drop,
      show m - j - w.length + w.length = m - j by omega]
  have hA_lt : ∀ d ∈ ((Nat.digits b n).drop (m - j - w.length)).take w.length,
      d < b := fun d hd =>
    Nat.digits_lt_base hb (List.mem_of_mem_drop (List.mem_of_mem_take hd))
  have hA_len :
      ((((Nat.digits b n).drop (m - j - w.length)).take w.length)).length
      = w.length := by
    rw [List.length_take, List.length_drop, hml]
    omega
  have hofA : Nat.ofDigits b
      (((Nat.digits b n).drop (m - j - w.length)).take w.length)
      = n / b ^ (m - j - w.length) % b ^ w.length := by
    rw [← Nat.ofDigits_mod_pow_eq_ofDigits_take w.length (by omega) _
        (fun d hd => Nat.digits_lt_base hb (List.mem_of_mem_drop hd)),
      ← Nat.self_div_pow_eq_ofDigits_drop _ _ hb]
  rw [hsub, List.reverse_eq_iff]
  constructor
  · intro h
    rw [← hofA, h]
  · intro h
    refine Nat.ofDigits_inj_of_len_eq hb ?_ hA_lt
      (fun d hd => hw d (List.mem_reverse.mp hd)) ?_
    · rw [hA_len, List.length_reverse]
    · rw [hofA, h]
end Champernowne
