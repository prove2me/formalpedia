-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_cohort_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:56.034031+00:00
-- url     : https://prove2.me/submissions/2fd5ff1c-f2a3-4ba9-ad64-1fad11fb2a8f

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_card_blockAt_head_zero
public import Theorems.Thm_Champernowne_sum_countOccurrences_cohort_eq_head

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? = some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  rw [sum_countOccurrences_cohort_eq_head hb m hw hwne hk,
    card_blockAt_head_zero hb m hw hw0 hk, Nat.zero_add]
end Champernowne
