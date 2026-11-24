-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T02:38:28.900635+00:00
-- url     : https://prove2.me/submissions/1270f63d-46fd-42fc-b305-c6dae404b3c2

import Mathlib
open Finset


theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Icc 1 M, χ (n : ZMod q)‖ ≤ (q : ℝ) + 1 := by
  have hperiod (m : ℕ) : (∑ n ∈ range (q+m), χ (n : ZMod q)) = ∑ n ∈ range m, χ (n : ZMod q) := by
    have hz : (∑ n ∈ range q, χ (n : ZMod q)) = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      convert (MulChar.sum_eq_zero_of_ne_one hχ) using 1
      exact (Fintype.sum_equiv (ZMod.finEquiv q).toEquiv _ _ (by
        intro i; congr 1; cases q with
        | zero => exact (NeZero.ne 0 rfl).elim
        | succ q => apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt)).symm.symm
    rw [Finset.sum_range_add, hz, zero_add]; simp
  have bound (m : ℕ) : ‖∑ n ∈ range m, χ (n : ZMod q)‖ ≤ (q:ℝ) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases h : m < q
      · calc
          _ ≤ ∑ n ∈ range m, ‖χ (n : ZMod q)‖ := norm_sum_le _ _
          _ ≤ ∑ _ ∈ range m, (1:ℝ) := Finset.sum_le_sum fun n _ => χ.norm_le_one _
          _ ≤ _ := by simpa using (show (m:ℝ) ≤ q by exact_mod_cast h.le)
      · have he : m = q + (m-q) := by omega
        rw [show (∑ n ∈ range m, χ (n : ZMod q)) = ∑ n ∈ range (m-q), χ (n : ZMod q) by conv_lhs => rw [he]; exact hperiod _]
        apply ih; have := NeZero.pos q; omega
  classical
  have he : insert 0 (Icc 1 M) = range (M+1) := by ext i; simp; omega
  have hsum := Finset.sum_insert (s := Icc 1 M) (a := 0) (f := fun n : ℕ => χ (n : ZMod q)) (by simp)
  rw [he] at hsum
  have e : (∑ n ∈ Icc 1 M, χ (n : ZMod q)) = (∑ n ∈ range (M+1), χ (n : ZMod q)) - χ 0 := by simpa using (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hsum.symm) : (∑ n ∈ Icc 1 M, χ (n : ZMod q)) = _ - χ 0)
  rw [e]; exact (norm_sub_le _ _).trans (add_le_add (bound _) (χ.norm_le_one 0))
