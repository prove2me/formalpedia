-- Prove2me | solution 1 for Champernowne.card_blockAt_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:07.750186+00:00
-- url     : https://prove2.me/submissions/f813f1cf-2863-426f-ab64-b562a9b9f731

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras
public import Theorems.Thm_Champernowne_block_eq_iff
public import Theorems.Thm_Champernowne_length_bigDigits_eq


set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ) {w : List ℕ}
    (hw : ∀ d ∈ w, d < b) (hwne : w ≠ []) (hw0 : w.head? ≠ some 0)
    (hk : w.length ≤ m) :
    ((Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)).card
      = b ^ (m - w.length) := by
  have hkpos : 0 < w.length := List.length_pos_of_ne_nil hwne
  have hmem := ofDigits_reverse_mem_Ico hb hkpos rfl hw hw0
  rw [Finset.mem_Ico] at hmem
  have hP : 0 < b ^ (m - w.length) := pow_pos (by omega) _
  have hbm : b ^ w.length * b ^ (m - w.length) = b ^ m := by
    rw [← pow_add]; congr 1; omega
  have hbm1 : b ^ (w.length - 1) * b ^ (m - w.length) = b ^ (m - 1) := by
    rw [← pow_add]; congr 1; omega
  have hset : (Finset.Ico (b ^ (m - 1)) (b ^ m)).filter
      (fun n => ((bigDigits b n).drop 0).take w.length = w)
      = Finset.Ico (Nat.ofDigits b w.reverse * b ^ (m - w.length))
        ((Nat.ofDigits b w.reverse + 1) * b ^ (m - w.length)) := by
    ext n
    rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, hblk⟩
      rw [block_eq_iff hb (length_bigDigits_eq hb h1 h2) hw (by omega),
        show m - 0 - w.length = m - w.length from rfl] at hblk
      have hdiv : n / b ^ (m - w.length) < b ^ w.length := by
        rw [Nat.div_lt_iff_lt_mul hP]
        omega
      rw [Nat.mod_eq_of_lt hdiv] at hblk
      constructor
      · rw [← hblk]
        exact (Nat.le_div_iff_mul_le hP).mp le_rfl
      · rw [← hblk]
        exact (Nat.div_lt_iff_lt_mul hP).mp (by omega)
    · rintro ⟨hlo, hhi⟩
      have hmem1 : b ^ (m - 1) ≤ n := by
        calc b ^ (m - 1) = b ^ (w.length - 1) * b ^ (m - w.length) :=
            hbm1.symm
        _ ≤ Nat.ofDigits b w.reverse * b ^ (m - w.length) :=
            Nat.mul_le_mul_right _ hmem.1
        _ ≤ n := hlo
      have hmem2 : n < b ^ m := by
        calc n < (Nat.ofDigits b w.reverse + 1) * b ^ (m - w.length) := hhi
        _ ≤ b ^ w.length * b ^ (m - w.length) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = b ^ m := hbm
      have hdiv : n / b ^ (m - w.length) = Nat.ofDigits b w.reverse := by
        have hlow := (Nat.le_div_iff_mul_le hP).mpr hlo
        have hhigh := (Nat.div_lt_iff_lt_mul hP).mpr hhi
        omega
      refine ⟨⟨hmem1, hmem2⟩, ?_⟩
      rw [block_eq_iff hb (length_bigDigits_eq hb hmem1 hmem2) hw (by omega),
        show m - 0 - w.length = m - w.length from rfl, hdiv,
        Nat.mod_eq_of_lt (by omega)]
  rw [hset, Nat.card_Ico, Nat.succ_mul]
  omega
end Champernowne
