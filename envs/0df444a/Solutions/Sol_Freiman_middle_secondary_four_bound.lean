-- Prove2me | solution 1 for Freiman.middle_secondary_four_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:58:13.347001+00:00
-- url     : https://prove2.me/submissions/a7262391-9d3e-42e3-a457-ca1195d5377d

import Definitions.Def_Freiman_middleRoots
import Theorems.Thm_Freiman_cf_convergence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.List.GetD
open Freiman
set_option autoImplicit false
private theorem root_left_digits (r : Fin 15) :
    ∀ d ∈ (middleRoot r).left, (d : ℕ) ≤ 3 := by
  fin_cases r <;> norm_num [middleRoot, middleRootList]

private theorem root_right_tail_digits (r : Fin 15) (n : ℕ)
    (hn : 0 < n) (hl : n < (middleRoot r).right.length) :
    ((middleRoot r).right.getD n 1 : ℕ) ≤ 3 := by
  fin_cases r <;> norm_num [middleRoot, middleRootList] at hl ⊢
  all_goals first | omega | (interval_cases n <;> norm_num)

private theorem away_four (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (i : ℤ)
    (h0 : i ≠ 0) (h1 : i ≠ 1) : (a i : ℕ) ≤ 3 := by
  by_cases hs : 0 ≤ i
  · have hip : 1 < i := by omega
    let n := i.toNat - 1
    have hi : (n:ℤ) + 1 = i := by dsimp [n]; omega
    by_cases hl : (middleRoot r).right.length ≤ n
    · simpa only [hi] using ha.2.2.2.2 n hl
    · have hn : 0 < n := by dsimp [n]; omega
      have hd := ha.2.2.1 n (by omega)
      rw [hi] at hd
      rw [hd]
      exact root_right_tail_digits r n hn (by omega)
  · let n := (-i).toNat - 1
    have hi : -(n:ℤ) - 1 = i := by dsimp [n]; omega
    by_cases hl : (middleRoot r).left.length ≤ n
    · simpa only [hi] using ha.2.2.2.1 n hl
    · have hd := ha.2.1 n (by omega)
      rw [hi] at hd
      rw [hd, List.getD_eq_getElem _ _ (by omega)]
      exact root_left_digits r _ (List.getElem_mem _)

private theorem secondary_index (r : Fin 15) (a : ℤ→ℕ+)
    (ha : middleCompatible (middleRoot r) a) (h : ¬ (a 1 : ℕ) ≤ 3) :
    r.val ∈ [5,6,7,8,9,10,11,13] ∧ a 1 = 4 := by
  have hl : 0 < (middleRoot r).right.length := by
    fin_cases r <;> norm_num [middleRoot, middleRootList]
  have hd := ha.2.2.1 0 hl
  norm_num only [Nat.cast_zero, zero_add] at hd
  fin_cases r <;> norm_num [middleRoot, middleRootList] at hd ⊢
  all_goals simp_all

theorem solution :
    (∀ a : ℤ→ℕ+, a 0=4 → a 1=4 → localValue a 0-localValue a 1 = (cfValue (fun n : ℕ => a (-(n:ℤ)-1))-cfValue (fun n : ℕ => a ((n:ℤ)+2))) * (1+1/((4+cfValue (fun n : ℕ => a (-(n:ℤ)-1)))*(4+cfValue (fun n : ℕ => a ((n:ℤ)+2)))))) →
    (∀ (r : Fin 15) (a : ℤ→ℕ+), middleCompatible (middleRoot r) a → (r.val∈[5,6,7,8,9,10,11,13]) → cfValue (fun n : ℕ => a (-(n:ℤ)-1)) > cfValue (fun n : ℕ => a ((n:ℤ)+2))) →
    ∀ (r : Fin 15) (a : ℤ→ℕ+) (i : ℤ), middleCompatible (middleRoot r) a → ¬(a i:ℕ) ≤ 3 → localValue a i ≤ localValue a 0 := by
  intro hid hsep r a i ha hn
  by_cases h0 : i = 0
  · subst i
    exact le_rfl
  have h1 : i = 1 := by
    by_contra hh
    exact hn (away_four r a ha i h0 hh)
  subst i
  obtain ⟨hr, ha1⟩ := secondary_index r a ha hn
  have heq := hid a ha.1 ha1
  have hsep' := hsep r a ha hr
  have hp := (cf_convergence (fun n : ℕ => a (-(n:ℤ)-1))).2.2.1
  have hq := (cf_convergence (fun n : ℕ => a ((n:ℤ)+2))).2.2.1
  have hh : 0 ≤ (1:ℝ)+1/((4+cfValue (fun n : ℕ => a (-(n:ℤ)-1)))*
      (4+cfValue (fun n : ℕ => a ((n:ℤ)+2)))) := by positivity
  have hm := mul_nonneg (sub_nonneg.mpr hsep'.le) hh
  linarith only [heq, hm]
#print axioms solution
