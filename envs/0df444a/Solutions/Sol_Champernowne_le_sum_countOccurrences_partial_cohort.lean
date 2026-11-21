-- Prove2me | solution 1 for Champernowne.le_sum_countOccurrences_partial_cohort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:50.268159+00:00
-- url     : https://prove2.me/submissions/71f441ac-c094-445b-98b0-41f0d02eacdd

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Theorems.Thm_Champernowne_geomsum_lt
public import Theorems.Thm_Champernowne_le_card_blockAt_partial
public import Theorems.Thm_Champernowne_sum_countOccurrences_Ico_eq

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (K t : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hk : w.length ≤ K + 1)
    (hAt : b ^ K + t ≤ b ^ (K + 1)) :
    (K + 1 - w.length) * (t / b ^ w.length)
      ≤ (∑ n ∈ Finset.Ico (b ^ K) (b ^ K + t), countOccurrences w (bigDigits b n))
        + 2 * b ^ (K + 1 - w.length) := by
  rw [sum_countOccurrences_Ico_eq hb K t w hAt, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (K + 1 - w.length + 1))
      (by omega : K + 1 - w.length + 1 ≤ K + 2),
    ← Finset.range_eq_Ico, Finset.sum_range_succ']
  have hint : (K + 1 - w.length) * (t / b ^ w.length)
      ≤ (∑ i ∈ Finset.range (K + 1 - w.length),
          ((Finset.Ico (b ^ K) (b ^ K + t)).filter
            (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card)
        + ∑ i ∈ Finset.range (K + 1 - w.length), b ^ (K - w.length - i) := by
    have h1 : ∑ _i ∈ Finset.range (K + 1 - w.length), t / b ^ w.length
        = (K + 1 - w.length) * (t / b ^ w.length) := by
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h2 : (∑ _i ∈ Finset.range (K + 1 - w.length), t / b ^ w.length)
        ≤ ∑ i ∈ Finset.range (K + 1 - w.length),
            (((Finset.Ico (b ^ K) (b ^ K + t)).filter
              (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card
              + b ^ (K + 1 - (i + 1) - w.length)) :=
      Finset.sum_le_sum fun i hi =>
        le_card_blockAt_partial hb K t (i + 1) hw (Nat.succ_pos i)
          (by rw [Finset.mem_range] at hi; omega) hAt
    rw [Finset.sum_add_distrib] at h2
    rw [h1] at h2
    refine le_trans h2 (Nat.add_le_add_left (le_of_eq ?_) _)
    exact Finset.sum_congr rfl fun i _ => by congr 1; omega
  have hgl := geomsum_lt hb (K + 1 - w.length)
  have hrefl : ∑ i ∈ Finset.range (K + 1 - w.length), b ^ (K - w.length - i)
      = ∑ i ∈ Finset.range (K + 1 - w.length), b ^ i := by
    rw [← Finset.sum_range_reflect (fun i => b ^ i) (K + 1 - w.length)]
    exact Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_range] at hi; congr 1; omega
  rw [hrefl] at hint
  omega
end Champernowne
