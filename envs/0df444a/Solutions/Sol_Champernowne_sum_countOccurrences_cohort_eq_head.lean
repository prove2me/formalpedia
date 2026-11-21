-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_cohort_eq_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:17.910875+00:00
-- url     : https://prove2.me/submissions/b8bd35f9-d593-4167-8835-cefa7634053c

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_card_blockAt
public import Theorems.Thm_Champernowne_card_blockAt_past_end
public import Theorems.Thm_Champernowne_countOccurrences_eq_card_filter_range
public import Theorems.Thm_Champernowne_length_bigDigits_eq


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), countOccurrences w (bigDigits b n)
      = ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
          (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  have hstep : ∀ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
      countOccurrences w (bigDigits b n)
        = ∑ j ∈ Finset.range (m + 1),
            if ((bigDigits b n).drop j).take w.length = w then 1 else 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    have hpred : ∀ j ∈ Finset.range (m + 1),
        (w.isPrefixOf ((bigDigits b n).drop j) = true)
          ↔ ((bigDigits b n).drop j).take w.length = w := fun j _ => by
      rw [List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, eq_comm]
    rw [countOccurrences_eq_card_filter_range,
      length_bigDigits_eq hb hn.1 hn.2, Finset.filter_congr hpred,
      Finset.card_filter]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  have hswap : ∀ j ∈ Finset.range (m + 1),
      (∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        if ((bigDigits b n).drop j).take w.length = w then 1 else 0)
      = ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
          (fun n => ((bigDigits b n).drop j).take w.length = w)).card := by
    intro j _
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hswap, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le (m - w.length + 1))
      (by omega : m - w.length + 1 ≤ m + 1)]
  have htail : ∑ j ∈ Finset.Ico (m - w.length + 1) (m + 1),
      ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
        (fun n => ((bigDigits b n).drop j).take w.length = w)).card = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    exact card_blockAt_past_end hb m j hwne (by omega)
  rw [htail, Nat.add_zero, ← Finset.range_eq_Ico, Finset.sum_range_succ']
  have hint : ∀ i ∈ Finset.range (m - w.length),
      ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
        (fun n => ((bigDigits b n).drop (i + 1)).take w.length = w)).card
      = (b - 1) * b ^ (m - w.length - 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    exact card_blockAt hb m (i + 1) hw (Nat.succ_pos i) (by omega)
  rw [Finset.sum_congr rfl hint, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  exact Nat.add_comm _ _
end Champernowne
