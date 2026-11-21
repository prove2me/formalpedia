-- Prove2me | solution 1 for Champernowne.sum_countOccurrences_cohort
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:41:55.130183+00:00
-- url     : https://prove2.me/submissions/91c1c74e-18e3-493b-80bf-b7cbab6339d9

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_card_blockAt_head
public import Theorems.Thm_Champernowne_sum_countOccurrences_cohort_eq_head

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ)
    {w : List ℕ} (hw : ∀ d ∈ w, d < b) (hwne : w ≠ [])
    (hw0 : w.head? ≠ some 0) (hk : w.length ≤ m) :
    ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m),
        countOccurrences w (bigDigits b n)
      = b ^ (m - w.length)
        + (m - w.length) * ((b - 1) * b ^ (m - w.length - 1)) := by
  rw [sum_countOccurrences_cohort_eq_head hb m hw hwne hk,
    card_blockAt_head hb m hw hwne hw0 hk]
end Champernowne
