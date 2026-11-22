-- Prove2me | solution 1 for BooleanIsoperimetry.cascade_pred_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:25.271419+00:00
-- url     : https://prove2.me/submissions/6643ac10-967a-49f9-b1f4-454787542e5e

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cube
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Nat.Choose.Sum
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Cascade
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_succ
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_mono
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pascal
public import Theorems.Thm_BooleanIsoperimetry_choose_succ_dim
public import Theorems.Thm_BooleanIsoperimetry_binomPrefix_pred_add_choosePred
public import Theorems.Thm_BooleanIsoperimetry_mem_neighborhood_iff
attribute [local simp] BooleanIsoperimetry.mem_neighborhood_iff



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution {n r t c rho : ℕ}
    (ht : t ≤ Nat.choose (n + 1) r)
    (hlo : binomPrefix n c ≤ rho)
    (hhi : rho < binomPrefix n (c + 1)) :
    rho + binomPrefix n (c + 1) < binomPrefix (n + 1) r + t
      ↔ rho < binomPrefix n (r - 1) + min t (choosePred n r) := by
  by_cases hge : r ≤ c
  · constructor <;> intro <;>
      simp_all +decide only [choose_succ_dim, binomPrefix_succ, binomPrefix_pascal]
    · have := binomPrefix_pred_add_choosePred n r
      have := binomPrefix_mono n hge
      have := binomPrefix_mono n (by omega : r + 1 ≤ c + 1)
      norm_num [binomPrefix_succ n r, binomPrefix_succ n c] at *
      omega
    · rcases r with (_ | r) <;> simp_all +decide [binomPrefix_succ, choosePred]
      · linarith [show binomPrefix n 0 = 0 from by rfl]
      · have h_mono : binomPrefix n c ≥ binomPrefix n (r + 1) := by
          exact binomPrefix_mono n (by linarith)
        simp_all +decide [binomPrefix_succ]
        grind
  · rcases Nat.lt_or_ge c (r - 1) with h2 | h2 <;>
      simp_all +decide only [not_le, ge_iff_le, tsub_le_iff_right, add_comm]
    · rw [min_def]
      split_ifs <;> constructor <;> intros <;>
        linarith [binomPrefix_mono n (by omega : c + 1 ≤ r - 1),
          binomPrefix_mono n (by omega : r - 1 ≤ r), binomPrefix_pascal n r,
          binomPrefix_pred_add_choosePred n r, choose_succ_dim n r]
    · cases h2.eq_or_lt <;> first | linarith | simp_all +decide [Nat.choose_succ_succ, add_comm]
      simp_all +decide [binomPrefix_pascal, binomPrefix_succ, choosePred]
      grind
end BooleanIsoperimetry
